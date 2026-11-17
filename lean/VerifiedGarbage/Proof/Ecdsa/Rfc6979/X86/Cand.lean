module

-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Ecdsa.Rfc6979.X86.Blocks`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): the blocks between the calls

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): `V = 0x01…` and
`K = 0x00…` (`initKV_ok`), the number of candidates (`initCnt_ok`), the
arguments of `core` (`coreArgs_ok`), whether to go on (`goOn_ok`,
`again_ok`, `stop_ok`), and the wiping of the frame with our caller's
registers restored (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The `4 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 32) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (4 * j)) 32 = w) :
    Spec.Sha256.bytesAt m q (4 * k) = (List.range (4 * k)).map fun i => w.extractLsb' (8 * (i % 4)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 4 * (i / 4) + i % 4 by omega_arith, Proof.Weierstrass.byte_word32 m q (i / 4) (Nat.mod_lt _ (by decide)),
    h _ (by omega_arith)]
  congr 2; omega_arith

/-! ## `V` and `K` -/

theorem kvN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : BitVec 32} (ha : u.gpr .eax = a)
    (hb : u.gpr .ecx = b) : ∀ k ≤ 16,
    WP isa (.block ((List.range k).flatMap fun j => [.store (stk (fV + 4 * j)) .eax,
      .store (stk (fK + 4 * j)) .ecx])) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (140 + 4 * j)) 32 = a ∧
        u'.mem.readW (L.B + BitVec.ofNat 64 (76 + 4 * j)) 32 = b
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    have nB := hL.nB
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hL hc ha hb k (by omega_arith)) fun u₁ ⟨hrd, hwr, hg, hf, hv⟩ => ?_
    have e₁ : addr L.F (fV + 4 * k) = L.B + BitVec.ofNat 64 (140 + 4 * k) := by
      rw [hL.addrF (by simp only [fV]; omega_arith)]; congr 2; simp only [fV]; omega_arith
    have e₂ : addr L.F (fK + 4 * k) = L.B + BitVec.ofNat 64 (76 + 4 * k) := by
      rw [hL.addrF (by simp only [fK]; omega_arith)]; congr 2; simp only [fK]; omega_arith
    have esp₁ : u₁.gpr .esp = L.F := by rw [hg, hc.esp]
    refine wp_stm esp₁ (by rw [e₁, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => ?_
    refine wp_stm (B := L.F) (by rw [v₂.gpr, esp₁]) (by rw [e₂, v₂.wr, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
      fun u₃ v₃ => WP.block_nil ?_
    rw [e₁, hg, ha] at v₂; rw [e₂, v₂.gpr, hg, hb] at v₃
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 616 → y + 4 ≤ 616 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    have hm₃ : u₃.mem = (u₁.mem.writeW (L.B + BitVec.ofNat 64 (140 + 4 * k)) a).writeW
        (L.B + BitVec.ofNat 64 (76 + 4 * k)) b := by rw [v₃.mem, v₂.mem]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    refine ⟨by rw [v₃.rd, v₂.rd, hrd], by rw [v₃.wr, v₂.wr, hwr], by rw [v₃.gpr, v₂.gpr, hg],
      hf.trans hf₃, fun j hj => ?_⟩
    rw [hm₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hv j hj
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, Mem.readW_writeW_self32]
      exact ⟨rfl, rfl⟩

theorem kv_bytes (m : Mem) (B : Addr) (w : BitVec 32) (o : Nat)
    (h : ∀ j < 16, m.readW (B + BitVec.ofNat 64 (o + 4 * j)) 32 = w) :
    Spec.Sha256.bytesAt m (B + BitVec.ofNat 64 o) 64 =
      (List.range 64).map fun i => w.extractLsb' (8 * (i % 4)) 8 :=
  bytesAt_of_readW (k := 16) m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 140) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) n = List.replicate n 0 := by
  rw [Cfg.initKV, WP.block_append_iff]
  refine wp_movi fun u₁ v₁ => wp_movi fun u₂ v₂ => WP.block_nil ?_
  have hc₂ : Ctx L g m₀ u₂ := (Upd.of_wp hL (Upd.of_wp hL hc (by decide) v₁).ctx (by decide) v₂).ctx
  refine WP.mono_syms (kvN_ok hL hc₂ (a := 0x01010101) (by rw [v₂.other _ (by decide), v₁.gpr]) v₂.gpr 16 (by omega_arith))
    fun u' ⟨hrd', hwr', hg, hf, hv⟩ hsy =>
      ⟨hc₂.keep (hsy := hsy) hL hrd' hwr' (by rw [hg]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)),
      by rw [v₂.mem, v₁.mem] at hf; exact hf, fun n hn => ?_, fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (140 : Nat) = 140 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (0x01010101 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (76 : Nat) = 76 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

/-- The number of candidates left, in the frame. -/
abbrev cnt {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 232) 32

theorem cnt_addr (hL : L.Ok) : addr L.F fCnt = L.B + BitVec.ofNat 64 232 := hL.addrF (by simp only [fCnt]; omega_arith)

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 232, 4⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 32 P.I.tries := by
  simp only [Cfg.initCnt, cfgOf, stk]
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [cnt_addr hL, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => WP.block_nil ?_
  rw [cnt_addr hL, v₁.gpr, v₁.mem] at v₂
  have hf : Frame [⟨L.B + BitVec.ofNat 64 232, 4⟩] t.mem u₂.mem := by
    rw [v₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)), hf, ?_⟩
  simp only [cnt, v₂.mem, Mem.readW_writeW_self32]

/-! ## `core`'s arguments -/

/-- The digest and `k` `core` reads: `X` (or, if `big`, the digest shifted
left by `sh` bits, at `fXc`) and `T`, in the frame. -/
abbrev dgArg (P : RfcHash) {dn : Nat} (L : Lay dn) : BitVec 32 := L.F + BitVec.ofNat 32 (cfgOf P).fDg
abbrev kArg {dn : Nat} (L : Lay dn) : BitVec 32 := L.F + BitVec.ofNat 32 fT

/-- Where they are. -/
abbrev dgAddr (P : RfcHash) {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (76 + (cfgOf P).fDg)
abbrev kAddr {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (76 + fT)

theorem fDg_le (P : RfcHash) : (cfgOf P).fDg ≤ 304 := by
  simp only [Cfg.fDg]; split <;> decide

theorem dgArg_w (hL : L.Ok) : (dgArg P L).setWidth 64 = dgAddr P L := hL.addrF (by have := fDg_le P; omega_arith)

theorem kArg_w (hL : L.Ok) : (kArg L).setWidth 64 = kAddr L := hL.addrF (by decide)

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .edi = L.a0 ∧
      t'.gpr .esi = L.a1 ∧ t'.gpr .edx = dgArg P L ∧ t'.gpr .ecx = kArg L ∧ t'.gpr .ebp = L.sc := by
  rw [show (cfgOf P).coreArgs = [.mov .edi (argM 0)] ++ ([.mov .esi (argM 1)] ++
      (Cfg.fr .edx (cfgOf P).fDg ++ (Cfg.fr .ecx fT ++ [.mov .ebp (argM 4)]))) from rfl]
  refine WP.block_append (WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 0) (by omega_arith)) fun u₁ h₁ => ?_)
  refine WP.block_append (WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega_arith)) fun u₂ h₂ => ?_)
  refine WP.block_append (WP.mono (fr_ok hL h₂.ctx (d := .edx) (by decide) _) fun u₃ h₃ => ?_)
  refine WP.block_append (WP.mono (fr_ok hL h₃.ctx (d := .ecx) (by decide) fT) fun u₄ h₄ => ?_)
  refine WP.mono (arg_ok hL h₄.ctx (d := .ebp) (by decide) (i := 4) (by omega_arith)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-! ## Whether to go on -/

theorem goOn_flag (a c : BitVec 32) :
    ((if decide (a.toNat < (1 : BitVec 32).toNat) then BitVec.allOnes 32 else 0) &&& c &&&
        ((if decide (a.toNat < (1 : BitVec 32).toNat) then BitVec.allOnes 32 else 0) &&& c) == 0) =
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
  · simp only [ha, decide_true, ite_true, BitVec.allOnes_and, true_and]
    by_cases hc : c = 0
    · subst hc; rfl
    · simp only [hc, decide_true, Bool.not_true, ne_eq, not_false_eq_true, beq_eq_false_iff_ne]
  · simp only [ha, decide_false, false_and]
    simp

/-- One candidate fewer; `ZF` is clear iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 232, 4⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .eax = t.gpr .eax ∧
      t'.zf = some (!decide (t.gpr .eax = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  simp only [Cfg.goOn, stk]
  refine wp_ldm hc.esp (by rw [cnt_addr hL]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u₁ v₁ => ?_
  refine wp_subi fun u₂ v₂ _ _ => ?_
  refine wp_stm (B := L.F) (by rw [v₂.other _ (by decide), v₁.other _ (by decide), hc.esp])
    (by rw [cnt_addr hL, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₃ v₃ => ?_
  refine wp_cmpi fun u₄ v₄ cf₄ _ => wp_sbb_self cf₄ fun u₅ v₅ => wp_and fun u₆ v₆ => wp_test fun u₇ v₇ zf₇ =>
    WP.block_nil ?_
  rw [cnt_addr hL] at v₁ v₃
  have eax₃ : u₃.gpr .eax = t.gpr .eax := by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide)]
  have cx₃ : u₃.gpr .ecx = cnt L t.mem - 1 := by rw [v₃.gpr, v₂.gpr, v₁.gpr]
  have hm₃ : u₃.mem = t.mem.writeW (L.B + BitVec.ofNat 64 232) (cnt L t.mem - 1) := by
    rw [v₃.mem, v₂.mem, v₁.mem, v₂.gpr, v₁.gpr]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 232, 4⟩] t.mem u₇.mem := by
    rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, hm₃]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms]) hL (by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd])
      (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide),
        v₁.other _ (by decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    hf, by rw [cnt, v₇.mem, v₆.mem, v₅.mem, v₄.mem, hm₃, Mem.readW_writeW_self32],
    by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, eax₃], ?_⟩
  rw [zf₇, v₆.gpr, v₅.gpr, v₅.other .ecx (by decide), v₄.gpr, cx₃, eax₃, goOn_flag]

/-- `ZF` clear. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some false :=
  wp_movi fun u₁ v₁ => wp_test fun u₂ v₂ zf₂ => WP.block_nil
    ⟨(Upd.of_wp hL hc (by decide) v₁).ctx.regs (hsy := v₂.syms) hL v₂.rd v₂.wr v₂.mem (by rw [v₂.gpr]),
      by rw [v₂.mem, v₁.mem], by rw [zf₂, v₁.gpr]; decide⟩

/-- `ZF` set. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some true ∧
      t'.gpr .eax = t.gpr .eax :=
  wp_movi fun u₁ v₁ => wp_test fun u₂ v₂ zf₂ => WP.block_nil
    ⟨(Upd.of_wp hL hc (by decide) v₁).ctx.regs (hsy := v₂.syms) hL v₂.rd v₂.wr v₂.mem (by rw [v₂.gpr]),
      by rw [v₂.mem, v₁.mem], by rw [zf₂, v₁.gpr]; decide, by rw [v₂.gpr, v₁.other _ (by decide)]⟩

/-! ## The wiping -/

/-- `k` zero words stored at the frame's start: only `K` and `V` change. -/
theorem zeroN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : ∀ k ≤ 32,
    WP isa (.block ((List.range k).map fun j => .store (stk (4 * j)) .ecx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    have nB := hL.nB
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hL hc k (by omega_arith)) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have e : addr L.F (4 * k) = L.B + BitVec.ofNat 64 (76 + 4 * k) := hL.addrF (by omega_arith)
    refine wp_stm (B := L.F) (by rw [hg, hc.esp]) (by rw [e, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
      fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr], by rw [v₂.gpr, hg], hf.trans ?_⟩
    rw [v₂.mem, e]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))

/-- One of our caller's registers, restored. -/
theorem restoreOne_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {r : Reg} {d : Nat} (hp : (r, d) ∈ saved)
    (hr : r ≠ .esp) : WP isa (.block [.mov r (.mem (stk d))]) u (Upd L g m₀ u r (g r)) := by
  have ho := saved_off _ hp
  have e : addr L.F d = L.B + BitVec.ofNat 64 (76 + d) := hL.addrF (by omega_arith)
  have hs := hc.saved (r, d) hp
  dsimp only at hs
  refine wp_ldm hc.esp (by rw [e]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun _ v₁ => WP.block_nil ?_
  rw [e, hs] at v₁
  exact Upd.of_wp hL hc hr v₁

/-- Our caller's registers, restored. -/
theorem restoreRegs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.restoreRegs) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .eax = u.gpr .eax ∧
      ∀ p ∈ saved, u'.gpr p.1 = g p.1 := by
  rw [show Cfg.restoreRegs = [.mov .ebx (.mem (stk 128))] ++ ([.mov .esi (.mem (stk 132))] ++
    ([.mov .edi (.mem (stk 136))] ++ [.mov .ebp (.mem (stk 140))])) from rfl]
  refine WP.block_append (WP.mono (restoreOne_ok hL hc (by decide) (by decide)) fun u₁ h₁ => ?_)
  refine WP.block_append (WP.mono (restoreOne_ok hL h₁.ctx (by decide) (by decide)) fun u₂ h₂ => ?_)
  refine WP.block_append (WP.mono (restoreOne_ok hL h₂.ctx (by decide) (by decide)) fun u₃ h₃ => ?_)
  refine WP.mono (restoreOne_ok hL h₃.ctx (by decide) (by decide)) fun u₄ h₄ =>
    ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, fun p hp => ?_⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.keep _ (by decide)]
  · simp only [saved, fSave, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
    · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
    · rw [h₄.keep _ (by decide), h₃.val]
    · exact h₄.val

/-- `k` zero words stored at the frame's top. -/
theorem zeroH_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : ∀ k ≤ 90,
    WP isa (.block ((List.range k).map fun j => .store (stk (fTlen + 4 * j)) .ecx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [L.HIGH] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    have nB := hL.nB
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroH_ok hL hc k (by omega_arith)) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have e : addr L.F (fTlen + 4 * k) = L.B + BitVec.ofNat 64 (228 + 4 * k) := by
      rw [hL.addrF (by simp only [fTlen]; omega_arith)]; simp only [fTlen]; congr 2; omega_arith
    refine wp_stm (B := L.F) (by rw [hg, hc.esp]) (by rw [e, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
      fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr], by rw [v₂.gpr, hg], hf.trans ?_⟩
    rw [v₂.mem, e]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`eax`
kept), and our caller's registers back. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .eax = t.gpr .eax ∧
      Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩, L.HIGH] t.mem t'.mem ∧
      ∀ p ∈ saved, t'.gpr p.1 = g p.1 := by
  rw [Cfg.wipe]
  refine WP.block_append (WP.block_append (WP.block_append (wp_movi fun u₁ v₁ => WP.block_nil ?_)))
  have hc₁ := (Upd.of_wp hL hc (by decide) v₁).ctx
  refine WP.mono_syms (zeroN_ok hL hc₁ 32 (Nat.le_refl _)) fun u₂ ⟨hrd, hwr, hg, hf⟩ hsy => ?_
  have hc₂ : Ctx L g m₀ u₂ := hc₁.keep (hsy := hsy) hL hrd hwr (by rw [hg]) hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith))
  refine WP.mono_syms (zeroH_ok hL hc₂ 90 (Nat.le_refl _)) fun u₃ ⟨hrd₃, hwr₃, hg₃, hf₃⟩ hsy₃ => ?_
  have hc₃ : Ctx L g m₀ u₃ := hc₂.keep (hsy := hsy₃) hL hrd₃ hwr₃ (by rw [hg₃]) hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr (sub_refl _))))
  refine WP.mono (restoreRegs_ok hL hc₃) fun t' ⟨hc', hm', ha', hs'⟩ => ⟨hc', ?_, ?_, hs'⟩
  · rw [ha', hg₃, hg, v₁.other _ (by decide)]
  · rw [hm', ← v₁.mem]
    exact (hf.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans
      (hf₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`, at
`fT` in the frame, its length at `fTlen`: empty (`tInit_ok`), then, while it
is shorter than `Q` bytes, `V = HMAC_K(V)` appended to it (`step_ok`:
`hmacVR_ok`, `keepArgs_ok`, `cpLoop_ok`, `tStep_ok`), which the loop does
`nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is then
`genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by `sh`
bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} (L : Lay dn) (m : Mem) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (kAddr L) n

/-! ## The blocks -/

theorem tlen_addr (hL : L.Ok) : addr L.F fTlen = L.B + BitVec.ofNat 64 (76 + fTlen) := hL.addrF (by decide)

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] t.mem t'.mem ∧ tlen L t'.mem = 0 := by
  simp only [Cfg.tInit, stk]
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [tlen_addr hL, v₁.wr]; exact hc.inFrW (by decide) (by decide) hL) fun u₂ v₂ => WP.block_nil ?_
  rw [tlen_addr hL, v₁.gpr, v₁.mem] at v₂
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] t.mem u₂.mem := by
    rw [v₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr])
    (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide)), hf, ?_⟩
  simp only [tlen, v₂.mem, Mem.readW_writeW_self32]

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`esi`, `T + a` in `ebx`, `ecx = D`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 32 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .esi = L.F + BitVec.ofNat 32 fV ∧ u.gpr .ebx = L.F + BitVec.ofNat 32 (fT + a) ∧
      u.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by
  rw [Cfg.keepArgs, show ([.alu .add .ebx (.mem (stk fTlen)), .mov .ecx (.mem (stk fDl))] : List Instr) =
    [.alu .add .ebx (.mem (stk fTlen))] ++ [.mov .ecx (.mem (stk fDl))] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) fV) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .ebx) (by decide) fT) fun u₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addF_ok hL h₂.ctx (d := .ebx) (by decide) (o := fTlen) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₄ h₄ => ?_
  refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₄.keep _ (by decide), h₃.val, h₂.val, h₂.mem, h₁.mem,
      show t.mem.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32 = tlen L t.mem from rfl, ha, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · rw [h₄.val, h₃.mem, h₂.mem, h₁.mem, hc.dl hT]

/-- `T` longer by `D` bytes, and the carry flag set iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 32 a) (hn : a + P.F.H.D < 2 ^ 32) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 32 (a + P.F.H.D) ∧ u'.cf = some (decide (a + P.F.H.D < P.Q)) := by
  obtain hQ : P.Q < 2 ^ 32 := by nums
  rw [show (cfgOf P).tStep = [.mov .eax (.mem (stk fTlen))] ++ [.alu .add .eax (.mem (stk fDl))] ++
      [.store (stk fTlen) .eax, .alu .cmp .eax (.imm (BitVec.ofNat 32 P.Q))] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .eax) (by decide) (o := fTlen) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (addF_ok hL h₁.ctx (d := .eax) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  obtain hax : u₂.gpr .eax = BitVec.ofNat 32 (a + P.F.H.D) := by
    rw [h₂.val, h₁.val, h₁.mem, hc.dl hT, show u.mem.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32 = tlen L u.mem
      from rfl, ha, BitVec.ofNat_add_ofNat]
  have hc₂ := h₂.ctx
  refine wp_stm (B := L.F) hc₂.esp (by rw [tlen_addr hL]; exact hc₂.inFrW (by decide) (by decide) hL)
    fun u₃ v₃ => wp_cmpi fun u₄ v₄ cf₄ _ => WP.block_nil ?_
  rw [tlen_addr hL, hax] at v₃
  obtain hm : u₄.mem = u₂.mem.writeW (L.B + BitVec.ofNat 64 (76 + fTlen)) (BitVec.ofNat 32 (a + P.F.H.D)) := by
    rw [v₄.mem, v₃.mem]
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] u₂.mem u₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.gpr]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide)),
    by rw [h₂.mem, h₁.mem] at hf; exact hf, by rw [tlen, hm, Mem.readW_writeW_self32], ?_⟩
  rw [cf₄, v₃.gpr, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hQ]

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
saved registers, `T`'s length, and `T`. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 204⟩, ⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩, ⟨kAddr L, 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)
  t : tOf L u.mem (j * P.F.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat} (hj : (j + 1) * P.F.H.D ≤ 136)
    {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      u'.cf = some (decide ((j + 1) * P.F.H.D < P.Q)) := by
  have hnb := hL.nB
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  obtain hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  obtain hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  obtain hl₁ : tlen L u₁.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_using [hfTl])
      · exact Offset.disjoint_base _ (by omega_using [hfTl]) (by omega_using [hfTl])) (by decide)
  obtain ht₁ : Spec.Sha256.bytesAt u₁.mem (kAddr L) (j * P.F.H.D) = Spec.Sha256.bytesAt u.mem (kAddr L) (j * P.F.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_using [hj, hjD, hfT])
      · exact Offset.disjoint_base _ (by omega_using [hfT]) (by omega_using [hj, hjD, hfT])) (by omega_using [hj, hjD])
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, hsi₂, hbx₂, hcx₂⟩ => ?_)
  obtain eS : (L.F + BitVec.ofNat 32 fV).setWidth 64 = L.B + BitVec.ofNat 64 (76 + fV) := hL.frv (by decide)
  obtain eD : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64 = kAddr L + BitVec.ofNat 64 (j * P.F.H.D) := by
    rw [hL.frv (by omega_using [hj, hjD, hfT]), Offset.add_add, Nat.add_assoc]
  have hnB := hL.nB
  obtain hr₂ : InRegions (u₂.rd ++ u₂.wr) ((L.F + BitVec.ofNat 32 fV).setWidth 64) P.F.H.D := by
    rw [eS]
    exact ⟨L.FR, by rw [hc₂.rd, hc₂.wr]; simp,
      Offset.contains _ (by decide) (by omega_using [hD64, hfV]) (by omega_using [])⟩
  obtain hw₂ : InRegions u₂.wr ((L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64) P.F.H.D := by
    rw [eD, Offset.add_add]; exact hc₂.inFrW (by omega_using []) (by omega_using [hj, hjD, hfT]) hL
  obtain hsep₂ : Region.Disjoint ⟨(L.F + BitVec.ofNat 32 fV).setWidth 64, P.F.H.D⟩
      ⟨(L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64, P.F.H.D⟩ := by
    rw [eS, eD, Offset.add_add]
    exact Offset.disjoint _ (.inl (by omega_using [hD64, hfV, hfT])) (by omega_using [hD64, hfV])
      (by omega_using [hj, hjD, hfT])
  obtain hsf₂ : Safe L ⟨(L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64, P.F.H.D⟩ := by
    rw [eD, Offset.add_add]; exact safe_high L (by omega_using [hfT]) (by omega_using [hj, hjD, hfT])
  obtain hS₂ : (L.F + BitVec.ofNat 32 fV).toNat + P.F.H.D ≤ 2 ^ 32 := by
    rw [hL.frN (by decide)]; have := hL.e28; have := hL.e588; omega_using [hD64, hfV]
  obtain hD₂ : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).toNat + P.F.H.D ≤ 2 ^ 32 := by
    rw [hL.frN (by omega_using [hj, hjD, hfT])]; have := hL.e28; have := hL.e588; omega_using [hj, hjD, hfT]
  refine WP.seq (WP.mono (cpLoop_ok hL hc₂ (by omega_using [hD16]) (by omega_using [hD64]) hS₂ hD₂ hr₂ hw₂ hsep₂ hsf₂
      hsi₂ hbx₂ hcx₂) fun u₃ ⟨hc₃, hf₃, hb₃, _⟩ => ?_)
  rw [eD, hm₂] at hf₃ hb₃
  rw [eS] at hb₃
  obtain hl₃ : tlen L u₃.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add]
      exact Offset.disjoint _ (.inl (by omega_using [hfT, hfTl])) (by omega_using [hfTl])
        (by omega_using [hj, hjD, hfT])) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega_using [hj, hjD])) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  obtain kp : ∀ {o n : Nat}, 76 ≤ o → o + n ≤ 204 →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_using [hfTl, h₂])) (by omega_using [h₂]) (by omega_using [hfTl]))
        (by omega_using [h₂]),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Offset.add_add]
          exact Offset.disjoint _ (.inl (by omega_using [hfT, h₂])) (by omega_using [h₂]) (by omega_using [hj, hjD, hfT])) (by omega_using [h₂])]
  obtain hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 76) P.F.H.D from rfl,
      kp (by decide) (by omega_using [hD64])]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 204⟩, by simp, sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨kAddr L, 136⟩, by simp, Offset.sub_base _ (by omega_using [hj, hjD])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, sub_refl _⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 140) P.F.H.D from rfl,
      kp (by decide) (by omega_using [hD64]), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (kAddr L) ((j + 1) * P.F.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_using [hfT, hfTl])) (by omega_using [hj, hjD, hfT])
          (by omega_using [hfTl])) (by omega_using [hj, hjD]),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [Offset.add_add]
        exact Offset.disjoint _ (.inr (by omega_using [hfT, hfTl])) (by omega_using [hj, hjD, hfT])
          (by omega_using [hfTl])) (by omega_using [hD64]),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hj, hjD])) (by omega_using [hj, hjD]),
      ht₁, show Spec.Sha256.bytesAt u.mem (kAddr L) (j * P.F.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D = vOf P L u₁.mem from rfl, hv₁,
      hI.k, hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame hf₃ fun r hr => ?_).frame hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add]
      exact (hL.stk_scr (d := 76 + fT + j * P.F.H.D) (n := P.F.H.D) (by omega_using [hj, hjD, hfT]) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (d := 76 + fTlen) (n := 4) (by omega_using [hfTl]) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.F.H.D - 1) / P.F.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.F.H.D < P.Q := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega_using [hD16]), Nat.succ_mul (j + 1)]
  omega_using [hD16]

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.F.H.D ≤ P.Q + P.F.H.D - 1 ∧ P.Q ≤ P.nV * P.F.H.D := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  obtain e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  obtain e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega_using [hD16])
  obtain e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega_using [hD16])).mpr (by omega_using [hQ8])
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega_using [e₁, e₂, e₃]

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  obtain e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega_using [hD16])
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  obtain h₁ : N * (8 * P.F.H.D) = 8 * (N * P.F.H.D) := Nat.mul_left_comm _ _ _
  obtain h₂ : (N + 1) * (8 * P.F.H.D) = 8 * (N * P.F.H.D) + 8 * P.F.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega_using [hl, e₁, h₁]) (by omega_using [hl, e₂, h₂])

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep .b) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  obtain hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.F.H.D)) (by omega_using [hND, hD64, hQ66])
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by show s'.cf = some true; rw [hcf, decide_eq_true ((nV_lt P j).mp hlt)],
      P.nV - (j + 1), by omega_using [hj], j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by show s'.cf = some false; rw [hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega_using [hj, hlt]]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  obtain kv0 : ∀ {o : Nat}, 76 ≤ o → o + P.F.H.D ≤ 204 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_using [hfTl, h₂])) (by omega_using [h₂]) (by omega_using [hfTl]))
      (by omega_using [hD64])
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, sub_refl _⟩
      k := kv0 (by decide) (by omega_using [hD64])
      v := kv0 (by decide) (by omega_using [hD64])
      len := by rw [hl₀, Nat.zero_mul]; rfl
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by omega_using [hfTl]) (by decide)).symm }

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  obtain hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  obtain hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kAddr L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kAddr L) (P.nV * P.F.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hb : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hb).2.2.1; omega_using [hl, this]
    rw [show (cfgOf P).candTop = .block [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero], hI₁.saved⟩
  · have hsh8 : P.R.sh < 8 := by omega_using [hl]
    obtain hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hb); omega_using [hl, this]
    refine WP.mono (candTop_ok hL hb hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    obtain kv : ∀ {o : Nat}, 76 ≤ o → o + P.F.H.D ≤ 204 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega_using [h₂]) (by decide)
        · exact Offset.disjoint _ (.inl (by omega_using [hfT, h₂])) (by omega_using [h₂]) (by omega_using [hQ66, hfT])) (by omega_using [hD64])
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega_using [hD64])).trans hI₁.k,
      (kv (by decide) (by omega_using [hD64])).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨kAddr L, 136⟩, by simp, Region.sub_prefix (by omega_using [hQ66])⟩
    · rw [hbu, hbits,
        ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (kAddr L) P.Q)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by omega_using [hQ66, hfT]) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.X86
