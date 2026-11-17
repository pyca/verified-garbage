module

-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Prep
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Weierstrass.Words

/-! ### `Ecdsa.Rfc6979.AArch64.Blocks`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on AArch64: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates
(`initCnt_ok`), the arguments of `core` (`coreArgs_ok`), whether to go on
(`goOn_ok`, `again_ok`, `stop_ok`), and the wiping of the frame (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (eval_nonzero)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The `8 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 64) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m q (8 * k) = (List.range (8 * k)).map fun i => w.extractLsb' (8 * (i % 8)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 8 * (i / 8) + i % 8 by omega_arith, Proof.Weierstrass.byte_word m q (i / 8) (Nat.mod_lt _ (by decide)),
    h _ (by omega_arith)]
  congr 2; omega_arith

theorem sep8 (B : Addr) {x y : Nat} (h : x + 8 ≤ y ∨ y + 8 ≤ x) (h₁ : x + 8 ≤ 256) (h₂ : y + 8 ≤ 256) :
    Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
  Offset.sep B h (by omega_arith) (by omega_arith)

/-- A word stored at `sp + o`, through `x15`. -/
theorem str15_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR])
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {t : Reg} {o : Nat} (ho : o % 8 = 0) (ho' : o + 8 ≤ 224 + 8 * L.e) :
    WP isa (.block [.str .x t .x15 o]) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.gpr = u.gpr ∧ u'.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (16 + o)) (u.gpr t) := by
  have := L.he
  have w : InRegions u.wr (L.B + BitVec.ofNat 64 (16 + o)) 8 :=
    ⟨L.FR, by rw [hwr]; simp, Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, ho,
    show o < 4096 * 8 by omega_arith, and_self, ite_true, Option.bind_some, State.store, State.read, Size.bits,
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
    refine WP.mono (kvN_ok hwr h15 ha hb k (by omega_arith)) fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hv₁⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg₁, h15]) (t := .x9) (o := fV + 8 * k)
      (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    refine WP.mono (str15_ok (u := u₂) ((hwr₂.trans hwr₁).trans hwr) (by rw [hg₂, hg₁, h15]) (t := .x10)
      (o := fK + 8 * k) (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith))
      fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ => ?_
    simp only [fV, fK, hg₂, hg₁, ha, hb, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd] at hm₂ hm₃
    refine ⟨hrd₃.trans (hrd₂.trans hrd₁), hwr₃.trans (hwr₂.trans hwr₁), hsp₃.trans (hsp₂.trans hsp₁),
      hg₃.trans (hg₂.trans hg₁), hf₁.trans ?_, fun j hj => ?_⟩
    · rw [hm₃, hm₂]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    rw [hm₃, hm₂]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep8 _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hv₁ j hj
    · rw [Mem.readW_writeW_sep (sep8 _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self64, Mem.readW_writeW_self64]
      exact ⟨rfl, rfl⟩

theorem kv_bytes (m : Mem) (q : Addr) (w : BitVec 64) (o : Nat)
    (h : ∀ j < 8, m.readW (q + BitVec.ofNat 64 (o + 8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m (q + BitVec.ofNat 64 o) 64 =
      (List.range 64).map fun i => w.extractLsb' (8 * (i % 8)) 8 :=
  bytesAt_of_readW (k := 8) m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 16, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) n = List.replicate n 0 := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
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
    (by omega_arith)) fun u' ⟨hrd', hwr', _, _, hf, hv⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, fun n hn => ?_,
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
abbrev cnt {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 192) 64

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 192, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 64 P.I.tries := by
  have w := hc.inFrW (d := 192) (n := 8) (by omega_arith) (by omega_arith)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
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
  rw [BitVec.shiftLeft_zero]
  exact BitVec.setWidth_ofNat_of_le_of_lt (by omega_arith) P.tries_lt

/-! ## `core`'s arguments -/

/-- The digest `core` reads: `X`, or, if `big`, the digest shifted left by
`sh` bits, at `fXc`; both above the pointers. -/
abbrev dgArg (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Addr :=
  if P.R.big then L.B + BitVec.ofNat 64 (16 + fXc) else L.B + BitVec.ofNat 64 (16 + fX)

/-- Where `core` reads the candidate `k`: `T`. -/
abbrev kArg (_P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Addr :=
  L.B + BitVec.ofNat 64 (16 + fT)

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .x0 = L.out ∧
      t'.gpr .x1 = L.d ∧ t'.gpr .x2 = dgArg P L ∧
      t'.gpr .x3 = kArg P L ∧ t'.gpr .x4 = L.scr := by
  have p0 := hc.inFr (d := 224) (by omega_arith) (by omega_arith)
  have p1 := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  have p3 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [dgArg, kArg]
  cases hb : P.R.big
  · simp only [Cfg.coreArgs, Cfg.fDg, cfgOf, hb, Cfg.fr, fOut, fD, fX, fT, fScratch, Bool.false_eq_true, ite_false,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod, Nat.reduceLT, and_self, ite_true,
      State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
      reduceCtorEq, hc.sp, Offset.add_add, Nat.reduceAdd, p0, p1, p3, Option.map_some,
      read8, hc.pOut, hc.pD, hc.pScr, BitVec.setWidth_eq, Option.some.injEq,
      exists_eq_left']
    refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial⟩
    have h₁ : r ∉ [Reg.x0, .x1, .x2, .x3, .x4] := not_pres hr _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
    simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2, ite_false]
  · simp only [Cfg.coreArgs, Cfg.fDg, cfgOf, hb, Cfg.fr, fOut, fD, fXc, fT, fScratch, ite_true,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod, Nat.reduceLT, and_self,
      State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
      reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, p0, p1, p3, Option.map_some,
      read8, hc.pOut, hc.pD, hc.pScr, BitVec.setWidth_eq, Option.some.injEq,
      exists_eq_left']
    refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial⟩
    have h₁ : r ∉ [Reg.x0, .x1, .x2, .x3, .x4] := not_pres hr _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
    simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2, ite_false]

/-! ## Whether to go on -/

theorem decr_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.ldrSp .x9 fCnt, .subImm .x .x9 .x9 1, .addSp .x15 0, .str .x .x9 .x15 fCnt]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.gpr .x9 = cnt L t.mem - 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x15 → u.gpr r = t.gpr r) ∧
      u.mem = t.mem.writeW (L.B + BitVec.ofNat 64 192) (cnt L t.mem - 1) := by
  have r := hc.inFr (d := 192) (by omega_arith) (by omega_arith)
  have w := hc.inFrW (d := 192) (n := 8) (by omega_arith) (by omega_arith)
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
      omega_arith
    have e : (~~~(1 : BitVec 32)).toNat = 2 ^ 32 - 2 := by decide
    rw [decide_eq_true (by simp only [Bool.toNat_true]; omega_arith :
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

/-- One candidate fewer; `x12 ≠ 0` iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 192, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .x0 = t.gpr .x0 ∧
      isa.eval (.nonzero .x .x12) t' = some (decide ((t.gpr .x0).setWidth 32 = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
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
    ∀ k ≤ 16, WP isa (.block ((List.range k).map fun j => .str .x .x14 .x15 (8 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 128⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    have := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hwr h15 k (by omega_arith)) fun u₁ ⟨hrd, hwr₁, hsp, hg, hf⟩ => ?_
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg, h15]) (t := .x14) (o := 8 * k) (by omega_arith)
      (by omega_arith)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd, hwr₂.trans hwr₁, hsp₂.trans hsp,
        hg₂.trans hg, hf.trans ?_⟩
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))

/-- The words above the pointers but `D`, `B` and the table cleared. -/
theorem zeroH_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR]) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    ∀ k ≤ L.e - 2, WP isa (.block ((List.range k).map fun j => .str .x .x14 .x15 (fBl + 8 + 8 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧ Frame [L.HIGH] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    have := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroH_ok hwr h15 k (by omega_arith)) fun u₁ ⟨hrd, hwr₁, hsp, hg, hf⟩ => ?_
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg, h15]) (t := .x14) (o := fBl + 8 + 8 * k)
      (by simp only [fBl]; omega_arith) (by simp only [fBl]; omega_arith)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ =>
        ⟨hrd₂.trans hrd, hwr₂.trans hwr₁, hsp₂.trans hsp, hg₂.trans hg, hf.trans ?_⟩
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [fBl]; omega_arith) (by simp only [fBl]; omega_arith) (by omega_arith))

/-- `K`, `V` and the words above the pointers but `D`, `B` and the table
cleared, keeping `x0`. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .x0 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 128⟩, L.HIGH] t.mem t'.mem := by
  have he := L.he
  have h := Ctx.of_keep (Q := fun t' => t'.gpr .x0 = t.gpr .x0) hL hc (is := Cfg.wipe)
    (ws := [⟨L.B + BitVec.ofNat 64 16, 128⟩, L.HIGH]) ?_ (by rfl) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact safe_low L (by omega_arith)
      · exact safe_high L (by omega_arith) (by omega_arith)
  · exact WP.mono h fun _ ⟨hc', hf, ha⟩ => ⟨hc', ha, hf⟩
  rw [Cfg.wipe, WP.block_append_iff, WP.block_append_iff]
  have h₁ : WP isa (.block [.addSp .x15 0, .movz .x .x14 0 0]) t fun u => u.rd = t.rd ∧
      u.wr = t.wr ∧ u.sp = t.sp ∧ u.mem = t.mem ∧ u.gpr .x0 = t.gpr .x0 ∧
      u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
      show (0 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write, RegUpd.sp_write, reduceCtorEq, ite_false,
      hc.sp, Option.some.injEq, exists_eq_left']
    exact ⟨by atriv, by atriv, by atriv, by atriv, by atriv, by rw [BitVec.setWidth_eq, BitVec.add_zero]⟩
  refine WP.mono h₁ fun u ⟨hrd, hwr, hsp, hm, ha, h15⟩ => WP.mono (zeroN_ok (hwr.trans hc.wr) h15 16 (by omega_arith))
    fun u' ⟨hrd', hwr', _, hg, hf⟩ => WP.mono (zeroH_ok (((hwr'.trans hwr)).trans hc.wr) (by rw [hg, h15])
      (extra - 2) (by rw [he]; rfl))
    fun u'' ⟨hrd'', hwr'', _, hg', hf'⟩ => ⟨hrd''.trans (hrd'.trans hrd), hwr''.trans (hwr'.trans hwr), ?_, by
      rw [hg', hg, ha]⟩
  rw [← hm]
  exact (hf.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (hf'.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`, at
`fT` above the frame's pointers, its length at `fTlen`: empty (`tInit_ok`),
then, while it is shorter than `Q` bytes, `V = HMAC_K(V)` appended to it
(`step_ok`: `hmacVR_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`), which the loop
does `nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is
then `genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by
`sh` bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (count_loop sbc_self eval_nonzero)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : BitVec 64 :=
  m.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + fT)) n

/-! ## The blocks -/

/-- A word of `x9` stored at `sp + o`, through `x15`. -/
theorem stF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {o : Nat} (ho : o % 8 = 0) (ho₂ : 16 + o + 8 ≤ 200) :
    WP isa (.block [.str .x .x9 .x15 o]) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u'.mem ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 (16 + o)) 64 = u.gpr .x9 := by
  refine WP.mono_syms (strW_ok (t := .x9) (dst := .x15) (D := L.B + BitVec.ofNat 64 16) (d := o) h15
    ⟨ho, by omega_using [ho₂]⟩ (by rw [Offset.add_add]; exact hc.inFrW (by omega_using []) (by have := L.he; omega_using [ho₂])))
    fun u₂ ⟨hrd, hwr, hsp, hg, _, hm⟩ hsy => ?_
  rw [Offset.add_add] at hm
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact safe_low L (by omega_using [ho₂])), hg, hf,
    by rw [hm, Mem.readW_writeW_self64]⟩

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fTlen), 8⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 64 0 := by
  rw [show Cfg.tInit = [.movz .x .x9 0 0] ++ Cfg.fr .x15 0 ++ [.str .x .x9 .x15 fTlen] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x9) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .x15) (by decide) (o := 0) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (stF_ok hL h₂.ctx (by rw [h₂.val]) (o := fTlen) (by decide) (by decide))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  rw [h₂.mem, h₁.mem] at hf₃
  exact ⟨hc₃, hf₃, by show u₃.mem.readW _ 64 = _; rw [hb₃, h₂.keep _ (by decide), h₁.val]⟩

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`x11`, `T + a` in `x12` and `x13 = D`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 64 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .x11 = L.B + BitVec.ofNat 64 (16 + fV) ∧ u.gpr .x12 = L.B + BitVec.ofNat 64 (16 + fT + a) ∧
      u.gpr .x13 = BitVec.ofNat 64 P.H.D := by
  have he := L.he
  rw [show Cfg.keepArgs = Cfg.fr .x11 fV ++ Cfg.fr .x12 fT ++ [.ldrSp .x9 fTlen] ++ [.add .x .x12 .x12 .x9] ++
      [.ldrSp .x13 fDl] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x11) (by decide) (o := fV) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .x12) (by decide) (o := fT) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (ldF_ok hL h₂.ctx (d := .x9) (by decide) (o := fTlen) (by simp only [fTlen]; omega_using []) rfl)
    fun u₃ h₃ => ?_
  refine WP.mono (add_ok hL h₃.ctx (d := .x12) (r := .x9) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (ldD_ok hL hT h₄.ctx (d := .x13) (by decide)) fun u₅ h₅ => ?_
  have hm₄ : u₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨h₅.ctx, by rw [h₅.mem, hm₄], ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.val, h₃.keep _ (by decide), h₂.val, h₃.val, h₂.mem, h₁.mem,
      show t.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 = tlen L t.mem from rfl, ha, Offset.add_add]

/-- `T` longer by `D` bytes, and `x12` nonzero iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 64 a) (hn : a + P.H.D < 2 ^ 63) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 (a + P.H.D) ∧ (u'.gpr .x12 != 0) = decide (a + P.H.D < P.Q) := by
  have he := L.he
  have hQ : P.Q < 2 ^ 16 := by anums
  rw [show (cfgOf P).tStep = [.ldrSp .x9 fTlen] ++ [.ldrSp .x10 fDl] ++ [.add .x .x9 .x9 .x10] ++ Cfg.fr .x15 0 ++
      [.str .x .x9 .x15 fTlen] ++ [.movz .x .x10 (BitVec.ofNat 16 P.Q) 0] ++
      [.subs .x .x12 .x9 .x10, .sbc .x .x12 .x12 .x12] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .x9) (by decide) (o := fTlen) (by simp only [fTlen]; omega_using []) rfl)
    fun u₁ h₁ => ?_
  refine WP.mono (ldD_ok hL hT h₁.ctx (d := .x10) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (add_ok hL h₂.ctx (d := .x9) (r := .x10) (by decide)) fun u₃ h₃ => ?_
  have h9₃ : u₃.gpr .x9 = BitVec.ofNat 64 (a + P.H.D) := by
    rw [h₃.val, h₂.keep _ (by decide), h₁.val, h₂.val,
      show u.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 = tlen L u.mem from rfl, ha, BitVec.ofNat_add_ofNat]
  refine WP.mono (fr_ok hL h₃.ctx (d := .x15) (by decide) (o := 0) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (stF_ok hL h₄.ctx (by rw [h₄.val]) (o := fTlen) (by decide) (by decide))
    fun u₅ ⟨hc₅, hg₅, hf₅, hb₅⟩ => ?_
  refine WP.mono (movz_ok hL hc₅ (d := .x10) (by decide) (n := P.Q) hQ) fun u₆ h₆ => ?_
  have h9₆ : u₆.gpr .x9 = BitVec.ofNat 64 (a + P.H.D) := by
    rw [h₆.keep _ (by decide), hg₅, h₄.keep _ (by decide), h9₃]
  have hQt : (u₆.gpr .x10).toNat = P.Q := by rw [h₆.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hQ])]
  have hnt : (u₆.gpr .x9).toNat = a + P.H.D := by rw [h9₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  refine WP.mono (show WP isa (.block [.subs .x .x12 .x9 .x10, .sbc .x .x12 .x12 .x12]) u₆ fun u₇ =>
      u₇.rd = u₆.rd ∧ u₇.wr = u₆.wr ∧ u₇.sp = u₆.sp ∧ u₇.mem = u₆.mem ∧ u₇.syms = u₆.syms ∧
      (∀ r, r ≠ .x12 → u₇.gpr r = u₆.gpr r) ∧
      u₇.gpr .x12 = if P.Q ≤ a + P.H.D then 0 else BitVec.allOnes 64 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
      RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.mem_write,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by atriv, by atriv, by atriv, by atriv, by atriv, fun r hr => by simp only [hr, ite_false], ?_⟩
    rw [sbc_self, hQt, hnt]) fun u₇ ⟨hrd₇, hwr₇, hsp₇, hm₇, hsy₇, hg₇, h12₇⟩ => ?_
  have hc₇ : Ctx L g m₀ u₇ := h₆.ctx.regs hL hrd₇ hwr₇ hm₇ hsp₇
    (fun r hr _ => hg₇ r (ne_cs hr (by decide))) hsy₇
  refine ⟨hc₇, by rw [hm₇, h₆.mem]; rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem] at hf₅; exact hf₅,
    by rw [show tlen L u₇.mem = u₇.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 from rfl, hm₇, h₆.mem, hb₅,
      h₄.keep _ (by decide), h9₃], ?_⟩
  rw [h12₇]
  by_cases h : P.Q ≤ a + P.H.D
  · simp only [h, ite_true, show ¬ a + P.H.D < P.Q by omega_using [h], decide_false]; rfl
  · simp only [h, ite_false, show a + P.H.D < P.Q by omega_using [h], decide_true]; rfl

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
frame, `K`, `V` and `T`'s length, and `T`. -/
abbrev CW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region :=
  [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)
  t : tOf L u.mem (j * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat} (hj : (j + 1) * P.H.D ≤ 136)
    {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      (u'.gpr .x12 != 0) = decide ((j + 1) * P.H.D < P.Q) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hjD : (j + 1) * P.H.D = j * P.H.D + P.H.D := Nat.succ_mul _ _
  have hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega_using [])
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega_using []) (by simp only [fTlen]; omega_using [])) (by decide)
  have ht₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) =
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fT]; omega_using [hj, he, hjD])
      · exact Offset.disjoint_base _ (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hj, hjD])) (by omega_using [hj, hjD])
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, hsi₂, hdi₂, hcx₂⟩ => ?_)
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D))
      (q := L.B + BitVec.ofNat 64 (16 + fV)) (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) hcx₂ hdi₂ hsi₂ ?_
      (hc₂.inFrW (by omega_using []) (by simp only [fT]; omega_using [hj, he, hjD]))
      (safe_high L (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hj, he, hjD]))
      (fun i hi => by
        obtain ⟨R, hR, h⟩ := hc₂.inFrW (d := 16 + fV + i) (n := 1) (by omega_using []) (by simp only [fV]; omega_using [hD64, hi])
        exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
      (fun i hi h => Offset.disjoint L.B (d := 16 + fV + i) (n := 1) (e := 16 + fT + j * P.H.D) (k := P.H.D)
        (.inl (by simp only [fV, fT]; omega_using [hD64, hi])) (by simp only [fV]; omega_using [hD64, hi]) (by simp only [fT]; omega_using [hj, hjD]) _
        (by rw [← Offset.add_add]; exact Region.contains_self _ _) h))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fT + _) (by simp only [fT]; omega_using [hj, hjD]),
      Nat.mod_eq_of_lt (by simp only [fT]; omega_using [hj, he, hnb, hjD])]
    simp only [fT]; omega_using [hj, he, hnb, hjD]
  rw [hm₂] at hf₃ hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega_using [])) (by simp only [fTlen]; omega_using [])
        (by simp only [fT]; omega_using [hj, hjD])) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega_using [hj, hjD])) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 16 ≤ o → o + n ≤ 16 + fTlen →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl h₂) (by simp only [fTlen] at h₂ ⊢; omega_using [h₂]) (by simp only [fTlen]; omega_using []))
        (by simp only [fTlen] at h₂; omega_using [h₂]),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by simp only [fTlen, fT] at h₂ ⊢; omega_using [h₂])) (by simp only [fTlen] at h₂ ⊢; omega_using [h₂])
            (by simp only [fT]; omega_using [hj, hjD])) (by simp only [fTlen] at h₂; omega_using [h₂])]
  have hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 16) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega_using [hD64])]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 152⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩, by simp, Offset.sub _ (by omega_using []) (by omega_using [hj, hjD])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 152⟩, by simp, Offset.sub_base _ (by simp only [fTlen]; omega_using [])⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 80) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega_using [hD64]), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fT)) ((j + 1) * P.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega_using [])) (by simp only [fT]; omega_using [hj, hjD])
          (by simp only [fTlen]; omega_using [])) (by omega_using [hj, hjD]),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega_using [])) (by simp only [fT]; omega_using [hj, hjD])
          (by simp only [fTlen]; omega_using [])) (by omega_using [hD64]),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fT]; omega_using [hj, hjD]) (by simp only [fT]; omega_using [hj, hjD])) (by omega_using [hj, hjD]),
      ht₁, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D = vOf P L u₁.mem from rfl, hv₁, hI.k,
      hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame hf₃ fun r hr => ?_).frame hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fT]; omega_using [hj, he, hjD]) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fTlen]; omega_using []) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.H.D - 1) / P.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.H.D < P.Q := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega_using [hD16]), Nat.succ_mul (j + 1)]
  omega_using [hD16]

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.H.D ≤ P.Q + P.H.D - 1 ∧ P.Q ≤ P.nV * P.H.D := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega_using [hD16])
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega_using [hD16])).mpr (by omega_using [hQ8])
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.H.D - 1) / P.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega_using [e₁, e₂, e₃]

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nV := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega_using [hD16])
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.H.D - 1) / P.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.H.D) = 8 * (N * P.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.H.D) = 8 * (N * P.H.D) + 8 * P.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega_using [hl, e₁, h₁]) (by omega_using [hl, e₂, h₂])

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep (.nonzero .x .x12)) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.H.D)) (by omega_using [hND, hD64, hQ66])
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true ((nV_lt P j).mp hlt)],
      P.nV - (j + 1), by omega_using [hj], j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega_using [hj, hlt]]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have kv0 : ∀ {o : Nat}, 16 ≤ o → o + P.H.D ≤ 144 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen]; omega_using [h₂])) (by omega_using [h₂]) (by simp only [fTlen]; omega_using []))
      (by omega_using [hD64])
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 152⟩, by simp, Offset.sub_base _ (by decide)⟩
      k := kv0 (by decide) (by omega_using [hD64])
      v := kv0 (by decide) (by omega_using [hD64])
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by simp only [fTlen]; omega_using []) (by decide)).symm }


theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg P L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, Rfc6979.hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg P L) (P.nV * P.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hb : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hb).2.2.1; omega_using [hl, this]
    rw [show (cfgOf P).candTop = .block [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero], hI₁.saved⟩
  · have hsh8 : P.R.sh < 8 := by omega_using [hl]
    have hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hb); omega_using [hl, this]
    refine WP.mono (candTop_ok hL hb hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    have kv : ∀ {o : Nat}, 16 ≤ o → o + P.H.D ≤ 144 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega_using [h₂]) (by decide)
        · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_using [h₂])) (by omega_using [h₂]) (by simp only [fT]; omega_using [hQ66])) (by omega_using [hD64])
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega_using [hD64])).trans hI₁.k,
      (kv (by decide) (by omega_using [hD64])).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩, by simp, Region.sub_prefix (by omega_using [hQ66])⟩
    · rw [show kArg P L = L.B + BitVec.ofNat 64 (16 + fT) from rfl, hbu, hbits,
        Rfc6979.ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := Rfc6979.ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fT)) P.Q)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by simp only [fT]; omega_using [he, hQ66]) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.AArch64
