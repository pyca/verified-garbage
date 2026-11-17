module

-- separate module: its proofs (the buffers X and h, about 3 s) build in parallel with `Steps`, which `Cand` also imports
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
public import VerifiedGarbage.Proof.Mont.X86_64.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import VerifiedGarbage.Proof.Weierstrass.Words

/-! ### `Ecdsa.Rfc6979.X86_64.Blocks`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86-64: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates
(`initCnt_ok`), the message `V ‖ b (‖ d ‖ h)` in `scratch` (`msg_ok`), the
arguments of `core` (`coreArgs_ok`), whether to go on (`goOn_ok`, `again_ok`,
`stop_ok`), and the wiping of the frame (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

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

/-! ## `V` and `K` -/

theorem kvN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : BitVec 64} (ha : u.gpr .rax = a)
    (hb : u.gpr .rcx = b) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap fun j => [.store (stk (fV + 8 * j)) .rax,
      .store (stk (fK + 8 * j)) .rcx])) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (88 + 8 * j)) 64 = a ∧
        u'.mem.readW (L.B + BitVec.ofNat 64 (24 + 8 * j)) 64 = b
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hL hc ha hb k (by omega_arith)) fun u₁ ⟨hrd, hwr, hg, hf, hv⟩ => ?_
    have w₁ := hc.inFrW (d := 88 + 8 * k) (n := 8) (by omega_arith) (by omega_arith)
    have w₂ := hc.inFrW (d := 24 + 8 * k) (n := 8) (by omega_arith) (by omega_arith)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hc.rsp,
      Offset.add_add, fV, fK, Nat.zero_add, show 24 + (64 + 8 * k) = 88 + 8 * k by omega_arith, hwr, w₁, w₂, ite_true,
      Option.some.injEq, exists_eq_left', ha, hb]
    have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 240 → y + 8 ≤ 240 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (64 / 8) (L.B + BitVec.ofNat 64 y) (64 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    refine ⟨hrd, trivial, trivial, hf.trans ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)))), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hv j hj
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self64, Mem.readW_writeW_self64]
      exact ⟨rfl, rfl⟩

theorem xor_self_zx (x : BitVec 32) : (x ^^^ x).setWidth 64 = 0 := by simp

theorem kv_bytes (m : Mem) (q : Addr) (w : BitVec 64) (o : Nat)
    (h : ∀ j < 8, m.readW (q + BitVec.ofNat 64 (o + 8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m (q + BitVec.ofNat 64 o) 64 =
      (List.range 64).map fun i => w.extractLsb' (8 * (i % 8)) 8 :=
  bytesAt_of_readW (k := 8) m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) n = List.replicate n 0 := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
  rw [Cfg.initKV, WP.block_append_iff]
  have h₁ : WP isa (.block [.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)]) t
      fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.mem = t.mem ∧
        u.gpr .rax = BitVec.ofNat 64 0x0101010101010101 ∧ u.gpr .rcx = 0 := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, exists_eq_left', xor_self_zx]
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, by triv⟩
  refine WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, ha, hb⟩ => WP.mono (kvN_ok hL hcu ha hb 8 (by omega_arith))
    fun u' ⟨hrd', hwr', _, hf, hv⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, fun n hn => ?_, fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (88 : Nat) = 88 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (BitVec.ofNat 64 0x0101010101010101).extractLsb' (8 * (i % 8)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (24 : Nat) = 24 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

/-- The number of candidates left, in the frame. -/
abbrev cnt {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 200) 64

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 200, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 64 P.I.tries := by
  have w := hc.inFrW (d := 200) (n := 8) (by omega_arith) (by omega_arith)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.initCnt, cfgOf, fCnt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    State.store64, ea_stk, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg, reduceCtorEq, ite_false,
    RegUpd.wr_setReg, RegUpd.rd_setReg, RegUpd.mem_setReg, hc.rsp, Offset.add_add, Nat.reduceAdd, w, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _), ?_⟩
  simp only [cnt, Mem.readW_writeW_self64]
  exact BitVec.setWidth_ofNat_of_le_of_lt (by omega_arith) P.tries_lt

/-! ## `core`'s arguments -/

/-- The digest and `k` `core` reads: `X` (or, if `big`, the digest shifted
left by `sh` bits, at `fXc`) and `T`, above the pointers. -/
abbrev dgArg (P : RfcHash) {dn : Nat} (L : Lay dn) : Addr :=
  if P.R.big then L.B + BitVec.ofNat 64 (24 + fXc) else L.B + BitVec.ofNat 64 (24 + fX)
abbrev kArg (_P : RfcHash) {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (24 + fT)

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = L.out ∧
      t'.gpr .rsi = L.d ∧ t'.gpr .rdx = dgArg P L ∧ t'.gpr .rcx = kArg P L ∧ t'.gpr .r8 = L.scr := by
  have p0 := hc.inFr (d := 232) (by omega_arith) (by omega_arith)
  have p1 := hc.inFr (d := 224) (by omega_arith) (by omega_arith)
  have p3 := hc.inFr (d := 208) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [dgArg, kArg]
  cases hb : P.R.big
  · simp only [Cfg.coreArgs, Cfg.fDg, cfgOf, hb, Bool.false_eq_true, ite_false, Cfg.fr, fOut, fD, fX, fT,
      fScratch, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk, RegUpd.gpr_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq,
      ite_true, hc.rsp, Offset.add_add, Nat.reduceAdd, p0, p1, p3, hc.pOut, hc.pD, hc.pScr, sx32,
      Nat.reducePow, Nat.reduceLT, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, by triv, by triv⟩
  · simp only [Cfg.coreArgs, Cfg.fDg, cfgOf, hb, ite_true, ite_false, Cfg.fr, fOut, fD, fXc, fT,
      fScratch, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk, RegUpd.gpr_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq,
      hc.rsp, Offset.add_add, Nat.reduceAdd, p0, p1, p3, hc.pOut, hc.pD, hc.pScr, sx32,
      Nat.reducePow, Nat.reduceLT, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, by triv, by triv⟩

/-! ## Whether to go on -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem mask_true (x : BitVec 64) : x - x - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
theorem mask_false (x : BitVec 64) : x - x - (BitVec.ofBool false).setWidth 64 = 0 := by simp

theorem goOn_flag (a : BitVec 32) (c : BitVec 64) (x : BitVec 64) :
    ((x - x - (BitVec.ofBool (decide (a.toNat < (1 : BitVec 32).toNat))).setWidth 64) &&& c &&&
        ((x - x - (BitVec.ofBool (decide (a.toNat < (1 : BitVec 32).toNat))).setWidth 64) &&& c) == 0) =
      !decide (a = 0 ∧ c ≠ 0) := by
  have hb : decide (a.toNat < (1 : BitVec 32).toNat) = decide (a = 0) := by
    by_cases ha : a = 0
    · subst ha; rfl
    · have : ¬ a.toNat < (1 : BitVec 32).toNat := fun h => ha (BitVec.eq_of_toNat_eq (by
        have : (1 : BitVec 32).toNat = 1 := rfl
        show a.toNat = 0; omega_arith))
      rw [decide_eq_false this, decide_eq_false ha]
  rw [hb, BitVec.and_self]
  by_cases ha : a = 0
  · simp only [ha, decide_true, mask_true, BitVec.allOnes_and, true_and]
    by_cases hc : c = 0
    · subst hc; rfl
    · simp only [hc, decide_true, Bool.not_true, ne_eq, not_false_eq_true, beq_eq_false_iff_ne]
  · simp only [ha, decide_false, mask_false, false_and]
    simp

/-- One candidate fewer; `ZF` is clear iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 200, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .rax = t.gpr .rax ∧
      t'.zf = some (!decide ((t.gpr .rax).setWidth 32 = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  have r := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  have w := hc.inFrW (d := 200) (n := 8) (by omega_arith) (by omega_arith)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.goOn, fCnt, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execAlu32, readSrc, readSrc32,
    State.load64, State.store64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, RegUpd.zf_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    hc.rsp, Offset.add_add, Nat.reduceAdd, r, w, sx1, Option.some.injEq, exists_eq_left']
  refine ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _), ?_,
    by triv, ?_⟩
  · simp only [cnt, Mem.readW_writeW_self64]
  · rw [goOn_flag]

/-- `ZF` clear. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some false := by
  apply WP.of_runBlock
  simp only [Cfg.again, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.zf_arithFlags, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), rfl, by decide⟩

/-- `ZF` set. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some true ∧
      t'.gpr .rax = t.gpr .rax := by
  apply WP.of_runBlock
  simp only [Cfg.stop, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), rfl, by simp, RegUpd.gpr_setReg_of_ne _ _ (by decide)⟩

/-! ## Wiping the frame -/

theorem zeroN_ok {u : State} (hc : Ctx L g m₀ u) : ∀ k ≤ 16,
    WP isa (.block ((List.range k).map fun j => .store (stk (8 * j)) .rcx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hc k (by omega_arith)) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have w := hc.inFrW (d := 24 + 8 * k) (n := 8) (by omega_arith) (by omega_arith)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hc.rsp,
      Offset.add_add, hwr, w, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨hrd, trivial, trivial, hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)))⟩

theorem zeroH_ok {t : State} (hc : Ctx L g m₀ t) : ∀ k ≤ L.e - 2, ∀ u : State,
    u.wr = t.wr → u.gpr .rsp = t.gpr .rsp →
    WP isa (.block ((List.range k).map fun j => .store (stk (fBl + 8 + 8 * j)) .rcx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [L.HIGH] u.mem u'.mem
  | 0, _, u, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk, u, hwu, hsu => by
    have he := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroH_ok hc k (by omega_arith) u hwu hsu) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have w := hc.inFrW (d := 256 + 8 * k) (n := 8) (by omega_arith) (by omega_arith)
    rw [← hwu, ← hwr] at w
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hsu, hc.rsp, fBl,
      Offset.add_add, show 24 + (224 + 8 + 8 * k) = 256 + 8 * k by omega_arith, w, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨hrd, hwr, trivial, hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)))⟩

/-- `K`, `V` and the words above the pointers but `D` and `B` cleared, keeping `rax`. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .rax = t.gpr .rax ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩, L.HIGH] t.mem t'.mem := by
  have hx : extra - 2 = L.e - 2 := by rw [L.he]; rfl
  have h := Ctx.of_keep (Q := fun t' => t'.gpr .rax = t.gpr .rax) hL hc (is := Cfg.wipe)
    (ws := [⟨L.B + BitVec.ofNat 64 24, 128⟩, L.HIGH]) ?_ ?_ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact safe_low L (by omega_arith)
      · exact .inr (.inr (.inr (sub_refl _)))
  · exact WP.mono h fun _ ⟨hc', hf, ha⟩ => ⟨hc', ha, hf⟩
  · rw [Cfg.wipe, WP.block_append_iff, WP.block_append_iff, hx]
    have h₁ : WP isa (.block [.alu32 .xor .rcx (.reg .rcx)]) t fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧
        u.wr = t.wr ∧ u.mem = t.mem ∧ u.gpr .rax = t.gpr .rax := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
        Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
        Option.some.injEq, exists_eq_left']
      exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv⟩
    refine WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, ha⟩ => WP.mono (zeroN_ok hcu 16 (by omega_arith))
      fun u' ⟨hrd', hwr', hg, hf⟩ => WP.mono (zeroH_ok hcu (L.e - 2) (Nat.le_refl _) u' hwr'
        (by rw [hg]))
        fun u'' ⟨hrd'', hwr'', hg'', hf''⟩ => ⟨hrd''.trans (hrd'.trans hrd), hwr''.trans (hwr'.trans hwr), ?_,
          by rw [hg'', hg, ha]⟩
    rw [← hm]
    exact (hf.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (hf''.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  · rw [Cfg.wipe]; rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-! ### `Ecdsa.Rfc6979.X86_64.Wide`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: P-521's shifts, and the candidate's `V`s

For P-521 (`big`), whose scalars are longer than any digest and whose `n`
has fewer bits than them: the `Q` bytes at an offset above the frame's
pointers, shifted right in place through the words at `scratch + 2560`
(`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`), as for
the candidate `T`'s first `Q` bytes (`candTop_ok`); zero words above the
pointers (`zero9_ok`); and `genT` with one more `V` (`genT_succ`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Mont (wordsVal Outside off)
open VG.Proof.Mont.X86_64 (Scr KeepRegs)
open VG.Proof.Weierstrass.X86_64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) : Scr t L.scr 8192 :=
  ⟨hdi, by rw [hc.wr]; simp, hL.nc⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (hdi : s'.gpr .rdi = s.gpr .rdi)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨hdi.trans h.rdi, hwr ▸ h.wr, h.nowrap⟩

/-- `rcx ← -1`. -/
theorem ones_ok (u : State) : WP isa (.block [.movImm64 .rcx (BitVec.allOnes 64)]) u fun u' =>
    u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr .rcx = BitVec.allOnes 64 ∧
      ∀ r, r ≠ .rcx → u'.gpr r = u.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `conv o s`: the `Q` bytes at `rsp + o`, above the frame's pointers,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 600) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h4, hw9, hQ8, hQ66, hQw, hwQ⟩ := P.sizes
  obtain hW' := P.sizesW hW
  have he := L.he
  have hnb := hL.nb
  refine WP.of_syms ?_
  rw [Cfg.conv, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := o) (by omega_arith)) fun u₁ h₁ => ?_
  obtain hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .rsi = L.B + BitVec.ofNat 64 (24 + o) := h₁.val
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .rsi) (by decide) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (fun d hd => by rw [hsi₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith))
    (by rw [hsi₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr) (n := P.w) (o := 2560) (sh := s) (by omega_arith)
    hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine WP.mono (ones_ok u₃) fun u₄ ⟨hm₄, hrd₄, hwr₄, hcx₄, hg₄⟩ => ?_
  obtain hsp₄ : u₄.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hg₄ _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.keep _ (by decide), hc.rsp]
  obtain hwr₄' : u₄.wr = t.wr := by rw [hwr₄, k₃.wr, k₂.wr, h₁.ctx.wr, hc.wr]
  obtain hdst : u₄.gpr .rsp + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by rw [hsp₄, Offset.add_add]
  refine WP.mono (storeBytes_ok (scr_keep (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr)
      ((hg₄ _ (by decide)).trans (k₃.gpr _ (by decide))) (hwr₄.trans k₃.wr))
    (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .rsp) (by decide) (by decide) true
    (by rw [hcx₄]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [hdst, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄']; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ hsy => ?_
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  obtain hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem u₅.mem := by
    obtain f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    obtain f₅ := frame_of_outside O₅ (by omega_arith)
    rw [add_ofNat_zero, hm₄] at f₅
    rw [h₁.mem] at f₂
    exact (f₂.sub fun r hr => ⟨⟨L.scr + BitVec.ofNat 64 2560, 72⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
    rw [k₅.gpr _ (by simp [h₁', h₃]), hg₄ _ h₂, k₃.gpr _ (by simp [h₁', h₃]), k₂.gpr _ (by simp [h₁']),
      h₁.keep _ h₄]
  refine ⟨hc.keep hL (by rw [k₅.rd, hrd₄, k₃.rd, k₂.rd, h₁.ctx.rd, hc.rd]) (by rw [k₅.wr, hwr₄']) (hg _ (by decide)
      (by decide) (by decide) (by decide)) (fun r hr hr' => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide)) (ne_cs hr (by decide))) hf (hsy := hsy) fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₅
    simp only [ite_true] at hb₅
    rw [hb₅, hm₄, hv₃, hv₂, hsi₁, ecdsa_bytesAt, h₁.mem]

/-- A zero word at `rsp + o`, above the frame's pointers. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 232 ≤ o)
    (ho₂ : 24 + o + 8 ≤ 240 + 8 * L.e) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax), .store (stk o) .rax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  obtain w := hc.inFrW (d := 24 + o) (n := 8) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    State.store64, ea_stk, hc.rsp, Offset.add_add, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq,
    ite_false, ite_true, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, w,
    Option.bind_some, Option.some.injEq, exists_eq_left', xor_self_zx]
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem
      (u.mem.writeW (L.B + BitVec.ofNat 64 (24 + o)) (0 : BitVec 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL rfl rfl (by triv) (fun r hr _ => ?_) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) ho₂) rfl,
    fun r hr => ?_, hf, fun k hk => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ne_cs hr (by decide : Reg.rax ∉ calleeSaved), ite_false]
  · simp only [hr, ite_false]
  · rw [bytesAt_take _ _ (k := 8 * 1) (by omega_arith), bytesAt_of_readW (k := 1) _ _ 0 fun j hj => by
      rw [show j = 0 by omega_arith, Nat.mul_zero, add_ofNat_zero, Mem.readW_writeW_self64],
      show (List.range (8 * 1)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
        List.replicate 8 0 by decide, List.take_replicate, Nat.min_eq_left hk]

/-! ## Zero words, and copies into the frame -/

/-- Nine zero words at `rsp + o`, above the frame's pointers. -/
theorem zero9_ok (hL : L.Ok) {o : Nat} (ho₁ : 232 ≤ o) (ho₂ : 24 + o + 72 ≤ 240 + 8 * L.e) :
    ∀ k ≤ 9, ∀ {u : State}, Ctx L g m₀ u →
    WP isa (.block ((List.range k).flatMap fun j => [.alu32 .xor .rax (.reg .rax), .store (stk (o + 8 * j)) .rax])) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
        Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, hc => WP.of_runBlock ⟨u, rfl, hc, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc => by
    have := hL.nb
    have := L.he
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zero9_ok hL ho₁ ho₂ k (by omega_using [hk]) hc) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (zeroF_ok hL hc₁ (o := o + 8 * k) (by omega_using [ho₁]) (by omega_using [ho₂, hk])) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
    refine ⟨hc₂, fun r hr => (hg₂ r hr).trans (hg₁ r hr), hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by omega_using [hk])⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega_using [], Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 24 + o + 8 * k = 24 + (o + 8 * k) by omega_using [], hb₂ 8 (Nat.le_refl _),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_arith) (by omega_arith)) (by omega_using [hk]), hb₁, List.replicate_append_replicate]

/-! ## The candidate -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K k V).1.length = k * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) (hsh : P.R.sh ≠ 0) (hsh8 : P.R.sh < 8) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + fT), P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fT)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + fT)) P.Q) >>> P.R.sh) := by
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hdi₁, _⟩ => ?_
  refine WP.mono (conv_ok hL hW hc₁ hdi₁ (o := fT) (s := P.R.sh) (by decide) (by decide) (by omega_using [hsh]) (by omega_using [hsh8]))
    fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  rw [hm₁] at hf₂ hb₂
  exact ⟨hc₂, hf₂, hb₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end


/-!
# Deterministic ECDSA on x86-64: the digest into `X`

The byte loop `cpLoop`, `rcx` bytes from `rsi` to `rdi` with `Ctx` kept, for
a destination the code may write apart from the source (`cp_ok`), and `X`
(`prepX_ok`): `Q - m` zero bytes, then the digest's first `m = min(D, Q)`,
its length the smaller of the frame's `D` and `Q` (`min_ok`, by `cmovae`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Impl.Mgf1.X86_64 (ix byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.RsaOaep.X86_64 (StepOk stepR_ok byteLoop_ok ea_ix)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## A byte loop -/

structure CpI (u₀ : State) (p q : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x

theorem cpRaw_ok {u₀ : State} {p q : Addr} {n : Nat} (hs : StepOk (.reg .rcx) n u₀ [.rax, .r8])
    (hn : 0 < n) (hpn : n < 2 ^ 63) (hw : InRegions u₀.wr p n)
    (hsrc : ∀ i < n, InRegions (u₀.rd ++ u₀.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1)
    (hdi : u₀.gpr .rdi = p) (hsi : u₀.gpr .rsi = q) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa Cfg.cpLoop u₀ fun u' =>
      Keep [.rax, .r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (CpI u₀ p q) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  obtain hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  obtain hsv : v.gpr .rsi = q := (I.keep.gpr (by decide)).trans hsi
  obtain hea : ∀ b : Addr, b + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = b + BitVec.ofNat 64 j := fun b => by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  obtain hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 := by
    obtain ⟨R, hR, hc⟩ := hw
    refine ⟨R, I.keep.2.2 ▸ hR, hc.byte ?_⟩
    rw [BitVec.add_comm p, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hpn, hj])]
    exact hj
  obtain hrd : InRegions (v.rd ++ v.wr) (q + BitVec.ofNat 64 j) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hsrc j hj
  obtain hq : v.mem (q + BitVec.ofNat 64 j) = u₀.mem (q + BitVec.ofNat 64 j) := by
    rw [I.mem, ifn]
    exact fun h => hd j hj (by
      simp only [Region.Contains] at h ⊢; omega_using [hj, h])
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (u₀.mem (q + BitVec.ofNat 64 j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [Cfg.cpBody, ea_ix, hdv, hsv, I.r8, hea, hin, hrd, hq]
    simp
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl, ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega_using []) (by omega_using [hpn, hj]))]
    congr 1
    rw [BitVec.add_comm p, BitVec.add_sub_cancel]
  · rw [ifn he]
    obtain hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    obtain iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega_using [hne]
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- `n` bytes from `q` (`rsi`) to `p` (`rdi`), `n` in `rcx`, by `cpLoop`:
`Ctx` kept, for a destination the code may write apart from the source. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {p q : Addr} {n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 63) (hcx : u.gpr .rcx = BitVec.ofNat 64 n) (hdi : u.gpr .rdi = p) (hsi : u.gpr .rsi = q)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 0) (hpn : p.toNat + n ≤ 2 ^ 64) (hw : InRegions u.wr p n)
    (hs : Safe L ⟨p, n⟩) (hsrc : ∀ i < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    WP isa Cfg.cpLoop u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .rax → r ≠ .r8 → u'.gpr r = u.gpr r) ∧
      Frame [⟨p, n⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem q n := by
  refine WP.mono_syms (cpRaw_ok (stepR_ok hn' u (by decide) (by decide) hcx) hn hn' hw hsrc hd hdi hsi h8)
    fun u' ⟨hk, hm⟩ hsy => ?_
  obtain hg : ∀ r, r ≠ .rax → r ≠ .r8 → u'.gpr r = u.gpr r := fun r h₁ h₂ =>
    hk.gpr (by simp [h₁, h₂])
  obtain hf : Frame [⟨p, n⟩] u.mem u'.mem := fun x hx => by
    rw [hm x, ifn (hx _ (List.mem_singleton_self _))]
  refine ⟨hc.keep hL hk.2.1 hk.2.2 (hg _ (by decide) (by decide))
      (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs) hsy, hg, hf, ?_⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  rw [hm, ifp (Offset.contains_base _ (d := i) (by omega) (by omega)), BitVec.add_comm p, BitVec.add_sub_cancel]

/-! ## `X` -/

/-- `cmp rcx, rax; cmovae rcx, rax`: the smaller of the two in `rcx`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 a) (hax : u.gpr .rax = BitVec.ofNat 64 b) :
    WP isa (.block [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)]) u
      (Upd L g m₀ u .rcx (BitVec.ofNat 64 (min a b))) := by
  apply WP.of_runBlock
  obtain hta : (u.gpr .rcx).toNat = a := by rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  obtain htb : (u.gpr .rax).toNat = b := by rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, hta, htb, h,
      RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r _ => by rw [RegUpd.gpr_arithFlags], rfl,
      by rw [RegUpd.gpr_arithFlags, hcx, Nat.min_eq_left (by omega_using [h])], fun r _ => by rw [RegUpd.gpr_arithFlags]⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, hta, htb, h,
      RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.not_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r hr => by
        rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl,
      by rw [RegUpd.gpr_setReg_self, hax, Nat.min_eq_right (by omega_using [h])],
      fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩

/-- `rdi = rsp + o - rcx`, the digest in `rsi` and `r8 = 0`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 o)), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdi = L.B + BitVec.ofNat 64 (24 + o) - u.gpr .rcx ∧ u'.gpr .rsi = L.dg ∧
      u'.gpr .r8 = BitVec.ofNat 64 0 ∧ ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → u'.gpr r = u.gpr r := by
  obtain h216 := hc.inFr (d := 216) (by decide) (by have := L.he; omega_using [])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execAlu32, readSrc, readSrc32,
    State.setReg32, State.load64, ea_stk, hc.rsp, sx32 ho, Offset.add_add, fDigest, Nat.reduceAdd, h216, ite_true, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, reduceCtorEq, ite_false,
    hc.pDg, xor_self_zx, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, rfl,
    fun r h₁ h₂ h₃ => by simp only [h₁, h₂, h₃, ite_false]⟩

theorem sub_min (B : Addr) {a b c : Nat} (h : c ≤ b) :
    B + BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 c = B + BitVec.ofNat 64 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega_using [h], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The arguments of `X`'s copy: `X` cleared, `rcx = m = min(D, Q)`, the
digest in `rsi`, `X + Q - m` in `rdi` and `r8 = 0`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fX)) (8 * 9) = List.replicate (8 * 9) 0 ∧
      u.gpr .rcx = BitVec.ofNat 64 (min P.H.D P.Q) ∧
      u.gpr .rdi = L.B + BitVec.ofNat 64 (24 + fX + (P.Q - min P.H.D P.Q)) ∧ u.gpr .rsi = L.dg ∧
      u.gpr .r8 = BitVec.ofNat 64 0 := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fX) (by decide) (by simp only [fX]; omega_using [he]) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .rcx (.mem (stk fDl)), .mov32 .rax (.imm (BitVec.ofNat 32 P.Q)), .alu .cmp .rcx (.reg .rax),
      .cmov .ae .rcx (.reg .rax), .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fX + P.Q))),
      .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.mov .rcx (.mem (stk fDl))] ++ [.mov32 .rax (.imm (BitVec.ofNat 32 P.Q))] ++
      [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)] ++
      [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fX + P.Q))),
        .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega_using [])) fun u₂ h₂ => ?_
  refine WP.mono (mov32_ok hL h₂.ctx (d := .rax) (by decide) (n := P.Q) (by omega_using [hQ66])) fun u₃ h₃ => ?_
  obtain hcx₃ : u₃.gpr .rcx = BitVec.ofNat 64 P.H.D := by
    rw [h₃.keep _ (by decide), h₂.val, hc₁.dl hT]
  refine WP.mono (min_ok hL h₃.ctx (a := P.H.D) (b := P.Q) (by omega_using [hD64]) (by omega_using [hQ66]) hcx₃ h₃.val) fun u₄ h₄ => ?_
  refine WP.mono (xTail_ok hL h₄.ctx (o := fX + P.Q) (by simp only [fX]; omega_using [hQ66]))
    fun u₅ ⟨hc₅, hm₅, hdi₅, hsi₅, h8₅, hg₅⟩ => ?_
  obtain hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [h₄.val, ← Nat.add_assoc, sub_min _ hm] at hdi₅
  obtain hm₄ : u₅.mem = u₁.mem := by rw [hm₅, h₄.mem, h₃.mem, h₂.mem]
  exact ⟨hc₅, hm₄ ▸ hf₁, hm₄ ▸ hb₁, by rw [hg₅ _ (by decide) (by decide) (by decide), h₄.val], hdi₅, hsi₅, h8₅⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fX)) P.Q =
        List.replicate (P.Q - min P.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) := by
  have he := L.he
  have hnb := hL.nb
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, hcx₅, hdi₅, hsi₅, h8₅⟩ => ?_)
  obtain hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  obtain hm8 : 8 ≤ min P.H.D P.Q := by omega_using [hD16, hQ8]
  refine WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (24 + fX + (P.Q - min P.H.D P.Q))) (q := L.dg)
      (n := min P.H.D P.Q) (by omega_using [hD16, hQ8]) (by omega_using [hD64]) hcx₅
      hdi₅ hsi₅ h8₅ ?_ (hc₅.inFrW (by omega_using []) (by simp only [fX]; omega_using [he, hQ66]))
      (safe_high L (by simp only [fX]; omega_using []) (by simp only [fX]; omega_using [he, hQ66]))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 248 + 8 * L.e) (by simp only [fX]; omega_using [he, hQ66]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))))
    fun u ⟨hc', _, hf, hb⟩ => ?_
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fX + _) (by simp only [fX]; omega_using [hQ66]),
      Nat.mod_eq_of_lt (by simp only [fX]; omega_using [he, hnb, hQ66])]
    simp only [fX]; omega_using [he, hnb, hQ66]
  obtain hdn' : min P.H.D P.Q ≤ dn := by omega_using [hdn]
  obtain hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 24 + fX) (n := 72) (k := 248 + 8 * L.e)
        (by simp only [fX]; omega_using [he]) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega_using [hD64])
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by simp only [fX]; omega_using [hQ66])⟩
  · rw [show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega_using [], Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega_using [],
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fX]; omega_using [hQ66]) (by simp only [fX]; omega_using [hQ66])) (by omega_using [hQ66]),
      hdg]
    rw [bytesAt_take _ _ (k := 72) (by omega_using [hQ66]), hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [hQ66])]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_using [hs], Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The arguments of the copy of `core`'s digest, if `big`: `rcx = D`, the
digest in `rsi`, `Xc + Q - 1 - D` in `rdi` and `r8 = 0`. -/
theorem xcArgs_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧ u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
      u.gpr .rdi = L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D)) ∧ u.gpr .rsi = L.dg ∧
      u.gpr .r8 = BitVec.ofNat 64 0 := by
  have he := L.he
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega_using [he]) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, _, _, _⟩ => ?_
  rw [hlen, show ([.mov .rcx (.mem (stk fDl)), .mov .rdi (.reg .rsp),
      .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.mov .rcx (.mem (stk fDl))] ++
      [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))),
        .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega_using [])) fun u₂ h₂ => ?_
  obtain hcx₂ : u₂.gpr .rcx = BitVec.ofNat 64 P.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega_using [hQ66]))
    fun u₃ ⟨hc₃, _, hdi₃, hsi₃, h8₃, hg₃⟩ => ?_
  obtain hx : 24 + (fXc + P.Q - 1 - P.H.D) = 24 + fXc + (P.Q - 1 - P.H.D) := by omega_using [hQD]
  rw [hcx₂, sub_min _ (by omega_using [hQD]), hx] at hdi₃
  exact ⟨hc₃, by rw [hg₃ _ (by decide) (by decide) (by decide), hcx₂], hdi₃, hsi₃, h8₃⟩

/-- If `big`: the digest copied for `core`, with `Ctx` kept. -/
theorem xcCopy_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) : WP isa (.seq (.block (cfgOf P).xcArgs) Cfg.cpLoop) t (Ctx L g m₀) := by
  have he := L.he
  have hnb := hL.nb
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u ⟨hcu, hcx, hdi, hsi, h8⟩ => ?_)
  refine WP.mono (cp_ok hL hcu (p := L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) hcx hdi hsi h8 ?_ (hcu.inFrW (by omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (fun i hi => hcu.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 248 + 8 * L.e) (by simp only [fXc]; omega_using [he, hQ66, hQD]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega_using [hdn, hi]) (by omega_using [hD64, hi])))) fun _ h => h.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fXc + _) (by simp only [fXc]; omega_using [hQ66]),
    Nat.mod_eq_of_lt (by simp only [fXc]; omega_using [he, hnb, hQ66])]
  simp only [fXc]; omega_using [he, hnb, hQ66, hQD]

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := L.he
  have hnb := hL.nb
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hsl := P.R.nBits_len
  obtain hnb5 := (P.R.sizesW hW).2.2
  obtain hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_using [hsl]
  obtain hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_using [hsl, hnb5]
  have hlen : (cfgOf P).len = P.Q := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq ?_
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega_using [he]) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .rcx (.mem (stk fDl)), .mov .rdi (.reg .rsp),
      .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.mov .rcx (.mem (stk fDl))] ++
      [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))),
        .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega_using [])) fun u₂ h₂ => ?_
  obtain hcx₂ : u₂.gpr .rcx = BitVec.ofNat 64 P.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega_using [hQ66]))
    fun u₃ ⟨hc₃, hm₃, hdi₃, hsi₃, h8₃, hg₃⟩ => ?_
  obtain hx : 24 + (fXc + P.Q - 1 - P.H.D) = 24 + fXc + (P.Q - 1 - P.H.D) := by omega_using [hQD]
  rw [hcx₂, sub_min _ (by omega_using [hQD]), hx] at hdi₃
  obtain hm₁ : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  obtain hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 24 + fXc) (n := 72) (k := 248 + 8 * L.e)
        (by simp only [fXc]; omega_using [he]) a h₂) (Region.sub_prefix hdn a h₁)) (by omega_using [hD64])
  refine WP.seq (WP.mono (cp_ok hL hc₃ (p := L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) (by rw [hg₃ _ (by decide) (by decide) (by decide), hcx₂])
      hdi₃ hsi₃ h8₃ ?_ (hc₃.inFrW (by omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (fun i hi => hc₃.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 248 + 8 * L.e) (by simp only [fXc]; omega_using [he, hQ66, hQD]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))))
    fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fXc + _) (by simp only [fXc]; omega_using [hQ66]),
      Nat.mod_eq_of_lt (by simp only [fXc]; omega_using [he, hnb, hQ66])]
    simp only [fXc]; omega_using [he, hnb, hQ66, hQD]
  rw [hsc, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc₄) fun u₅ ⟨hc₅, hm₅, hdi₅, _⟩ => ?_
  refine WP.mono (conv_ok hL hW hc₅ hdi₅ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega_using [hsl])
    (by omega_using [])) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hm₁ ▸ hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hm₅ ▸ hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [hQ66])⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    obtain hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (24 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      obtain h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (n := a + n) (k := 8 * 9) (by omega_using [han])
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [han]), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    obtain hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      obtain e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (P.Q - 1 - P.H.D)
        (P.H.D + 1)
      obtain e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (24 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.H.D)) P.H.D 1
      rw [show P.Q - 1 - P.H.D + (P.H.D + 1) = P.Q by omega_using [hQD]] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      obtain p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (P.Q - 1 - P.H.D) =
          List.replicate (P.Q - 1 - P.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fXc]; omega_using [hQ66]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using [hQ66]), hm₁]
        have := hz 0 (P.Q - 1 - P.H.D) (by omega_using [hQ66])
        rwa [Nat.add_zero] at this
      obtain p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_using [])) (by simp only [fXc]; omega_using [hQ66, hQD]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using []), hm₁, show 24 + fXc + (P.Q - 1 - P.H.D) + P.H.D = 24 + fXc + (P.Q - 1 - P.H.D + P.H.D) by omega_using []]
        exact hz (P.Q - 1 - P.H.D + P.H.D) 1 (by omega_using [hQ66, hQD])
      rw [e, e', hb₄, hm₁, hdg, p₁, p₃]
    rw [hb₆, hm₅, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.X86_64
