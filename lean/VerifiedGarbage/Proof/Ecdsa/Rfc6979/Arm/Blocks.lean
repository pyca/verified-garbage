module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run

/-!
# Deterministic ECDSA on 32-bit ARM: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates, in
`r9` (`initCnt_ok`), whether to go on (`goOn_ok`, `again_ok`, `stop_ok`),
and the wiping of the frame below the saved registers, by a loop of word
stores, with our caller's registers restored (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_movw wp_cmp wp_subs op2_reg op2_imm dpVal)

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

/-- Code that changes only flags keeps `Ctx`. -/
theorem Ctx.flags (hL : L.Ok) {t t' : State} (hc : Ctx L g m₀ t) (h : FupdS t t') : Ctx L g m₀ t' :=
  hc.keep hL h.rd h.wr h.sp (fun r _ => by rw [h.gpr]) (ws := []) (by rw [h.mem]; exact Frame.refl _ _)
    (by simp) h.syms

/-! ## `V` and `K` -/

theorem kvN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : BitVec 32} (ha : u.gpr .r0 = a)
    (hb : u.gpr .r1 = b) : ∀ k ≤ 16,
    WP isa (.block ((List.range k).flatMap fun j => [.str .r0 .r8 (fV + 4 * j), .str .r1 .r8 (fK + 4 * j)])) u
      fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
        Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u.mem u'.mem ∧
        ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (88 + 4 * j)) 32 = a ∧
          u'.mem.readW (L.B + BitVec.ofNat 64 (24 + 4 * j)) 32 = b
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hL hc ha hb k (by omega_arith)) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hv⟩ => ?_
    have e₁ : State.addr (L.fp + BitVec.ofNat 32 (fV + 4 * k)) = L.B + BitVec.ofNat 64 (88 + 4 * k) :=
      fpA' hL (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)
    have e₂ : State.addr (L.fp + BitVec.ofNat 32 (fK + 4 * k)) = L.B + BitVec.ofNat 64 (24 + 4 * k) :=
      fpA' hL (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
    have o₁ : fV + 4 * k < 4096 := by simp only [fV]; omega_arith
    have o₂ : fK + 4 * k < 4096 := by simp only [fK]; omega_arith
    have r8₁ : u₁.gpr .r8 = L.fp := by rw [hg, hc.r8]
    refine wp_strS (a := L.B + BitVec.ofNat 64 (88 + 4 * k)) o₁ (by rw [r8₁]; exact e₁)
      (by rw [hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₂ v₂ => ?_
    refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + 4 * k)) o₂ (by rw [v₂.gpr, r8₁]; exact e₂)
      (by rw [v₂.wr, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₃ v₃ => WP.block_nil ?_
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 240 → y + 4 ≤ 240 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    have hm₃ : u₃.mem = (u₁.mem.writeW (L.B + BitVec.ofNat 64 (88 + 4 * k)) a).writeW
        (L.B + BitVec.ofNat 64 (24 + 4 * k)) b := by
      rw [v₃.mem, v₂.mem, v₂.gpr, hg, ha, hb]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    refine ⟨by rw [v₃.rd, v₂.rd, hrd], by rw [v₃.wr, v₂.wr, hwr], by rw [v₃.sp, v₂.sp, hsp],
      by rw [v₃.gpr, v₂.gpr, hg], hf.trans hf₃, fun j hj => ?_⟩
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

theorem ones_word : ((0x0101 : BitVec 16) ++ ((0x0101 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    0x01010101 := by decide

theorem wp_movt' {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', UpdS s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ ⟨Upd.setReg _ _ _,rfl⟩)

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) n = List.replicate n 0 := by
  rw [Cfg.initKV, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movwS fun u₁ v₁ => wp_movt' fun u₂ v₂ => wp_movS (op2_imm (by decide)) fun u₃ v₃ => ?_
  have hc₃ : Ctx L g m₀ u₃ := ((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)
  have h0 : u₃.gpr .r0 = 0x01010101 := by rw [v₃.other _ (by decide), v₂.gpr, v₁.gpr, ones_word]
  have hm₃ : u₃.mem = t.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono_syms (kvN_ok hL hc₃ h0 v₃.gpr 16 (by omega_arith)) fun u' ⟨hrd', hwr', hsp', hg, hf, hv⟩ sy =>
      ⟨hc₃.keep hL hrd' hwr' hsp' (fun r _ => by rw [hg]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) sy,
      by rw [hm₃] at hf; exact hf, fun n hn => ?_, fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (88 : Nat) = 88 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (0x01010101 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (24 : Nat) = 24 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0#32 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

theorem initCnt_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r9 = BitVec.ofNat 32 P.I.tries :=
  movw_ok hc (d := .r9) (v := P.I.tries) (by decide) P.tries_lt fun t' c' m' v' _ => WP.block_nil ⟨c', m', v'⟩

/-! ## Whether to go on -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, with its carry: set iff no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', UpdS s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [exec, ho, Option.map_some]) (k _ ⟨Upd.subs _ _ _ _ _,rfl⟩ rfl)

/-- `mov`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', UpdS s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some])
    (k _ ⟨Upd.setReg _ _ _,rfl⟩ rfl)

/-- `adc`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', UpdS s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [exec, ho, Option.map_some]) (k _ ⟨Upd.setReg _ _ _,rfl⟩)

end

/-- The decision's arithmetic: `(C - 1) & count`, `C` set iff `r ≥ 1`, is nonzero iff `r = 0` and
`count ≠ 0`. -/
theorem decide_go (r cnt : BitVec 32) :
    (!((((0#32 + 0#32 + (if decide ((1#32 : BitVec 32).toNat ≤ r.toNat) = true then 1 else 0) - 1#32 : BitVec 32) &&& cnt)
      - 0#32) == 0)) = decide (r = 0 ∧ cnt ≠ 0) := by
  by_cases h : r = 0
  · subst h
    have hc : decide ((1#32 : BitVec 32).toNat ≤ (0 : BitVec 32).toNat) = false := by decide
    have e1 : (0#32 + 0#32 + (if false = true then 1 else 0) - 1#32 : BitVec 32) = BitVec.allOnes 32 := by decide
    have e2 : cnt - 0#32 = cnt := BitVec.sub_zero cnt
    rw [hc, e1, BitVec.allOnes_and, e2]
    by_cases h' : cnt = 0
    · subst h'; decide
    · have h'' : cnt ≠ 0#32 := h'
      simp [h'']
  · have h0 : r ≠ 0#32 := h
    have hr : decide ((1#32 : BitVec 32).toNat ≤ r.toNat) = true := by
      rcases Nat.eq_zero_or_pos r.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e]; rfl)) h
      · exact decide_eq_true e
    have e3 : (0#32 + 0#32 + (if true = true then 1 else 0) - 1#32 : BitVec 32) = 0 := by decide
    have e4 : (0 : BitVec 32) &&& cnt = 0 := BitVec.zero_and
    rw [hr, e3, e4]
    simp [h0]

/-- One candidate fewer, and `Z` clear iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.gpr .r1 = t.gpr .r1 ∧
      isa.eval .ne t' = some (decide (t.gpr .r0 = 0 ∧ t.gpr .r9 - 1 ≠ 0)) := by
  simp only [Cfg.goOn]
  refine wp_dpS (op2_imm (by decide)) fun u₁ v₁ => wp_subsC (op2_imm (by decide)) fun u₂ v₂ c₂ => ?_
  refine wp_movC (op2_imm (by decide)) fun u₃ v₃ c₃ => wp_adc (op2_imm (by decide)) fun u₄ v₄ => ?_
  refine wp_dpS (op2_imm (by decide)) fun u₅ v₅ => wp_dpS (op2_reg _ _) fun u₆ v₆ => ?_
  refine wp_cmpS (op2_imm (by decide)) fun u₇ v₇ z₇ => WP.block_nil ?_
  have hc₆ : Ctx L g m₀ u₆ := (((((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)).upd v₄
    (by decide)).upd v₅ (by decide)).upd v₆ (by decide)
  have K : Rest [.r9, .r10, .r7] t u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans <|
    (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans (v₆.rest (by simp))
  have r9₅ : u₅.gpr .r9 = t.gpr .r9 - 1 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      dpVal]; rfl
  have r9₆ : u₆.gpr .r9 = t.gpr .r9 - 1 := by rw [v₆.other _ (by decide), r9₅]
  have r0₁ : u₁.gpr .r0 = t.gpr .r0 := v₁.other _ (by decide)
  refine ⟨hc₆.flags hL v₇, by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₇.gpr]; exact r9₆,
    by rw [v₇.gpr, K.gpr _ (by decide)], by rw [v₇.gpr, K.gpr _ (by decide)], ?_⟩
  show some (!u₇.z) = _
  rw [z₇, v₆.gpr, dpVal, v₅.gpr, dpVal, v₄.gpr, v₃.gpr, c₃, c₂, r9₅, r0₁]
  exact congrArg some (decide_go _ _)

theorem flag_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {v : Nat} (hv : v < 2) :
    WP isa (.block [.mov .r7 (.imm (BitVec.ofNat 32 v)), .cmp .r7 (.imm 0)]) t fun t' => Ctx L g m₀ t' ∧
      t'.mem = t.mem ∧ (∀ r, r ≠ .r7 → t'.gpr r = t.gpr r) ∧ isa.eval .ne t' = some (decide (v = 1)) :=
  wp_movS (op2_imm (by rcases (by omega_arith : v = 0 ∨ v = 1) with rfl | rfl <;> decide)) fun u₁ v₁ =>
    wp_cmpS (op2_imm (by decide)) fun u₂ v₂ z₂ => WP.block_nil
      ⟨(hc.upd v₁ (by decide)).flags hL v₂, by rw [v₂.mem, v₁.mem], fun r hr => by rw [v₂.gpr, v₁.other _ hr],
      by
        show some (!u₂.z) = _
        rw [z₂, v₁.gpr]
        rcases (by omega_arith : v = 0 ∨ v = 1) with rfl | rfl <;> decide⟩

/-- `Z` clear: go on. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 ∧
      isa.eval .ne t' = some true :=
  WP.mono (flag_ok hL hc (v := 1) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-- `Z` set: stop. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r0 = t.gpr .r0 ∧
      isa.eval .ne t' = some false :=
  WP.mono (flag_ok hL hc (v := 0) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-! ## The wiping -/

/-- What the wipe's loop keeps after `i` words. -/
structure WipeI (t : State) (L : Lay dn) (i : Nat) (u : State) : Prop where
  r12 : u.gpr .r12 = L.fp + BitVec.ofNat 32 (4 * i)
  r3 : u.gpr .r3 = BitVec.ofNat 32 (wipeWords - i)
  other : ∀ r, r ≠ .r3 → r ≠ .r12 → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  frame : Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem u.mem

/-- The loop of word stores: `wipeWords` words from the frame's base. -/
theorem wipeLoop_ok (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.fp)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 wipeWords) :
    WP isa (.loop (.block Cfg.wipeBody) .ne) t fun t' => WipeI t L wipeWords t' := by
  have hb := hL.B_fit
  refine WP.loop (M := isa) (body := .block Cfg.wipeBody) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = wipeWords - i ∧ i < wipeWords ∧ WipeI t L i u) ?_ (wipeWords - 0) _
    ⟨0, rfl, by decide, by rw [h12, Nat.mul_zero, BitVec.add_zero], by rw [h3]; rfl, fun _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  rintro k u ⟨i, rfl, hi, I⟩
  have hw : wipeWords = 117 := rfl
  have ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 0) = L.B + BitVec.ofNat 64 (24 + 4 * i) := by
    rw [I.r12, BitVec.add_zero, hL.fpA (by omega_arith)]
  refine wp_str (a := L.B + BitVec.ofNat 64 (24 + 4 * i)) (by decide) ea
    (by rw [I.wr, hwr]; exact ⟨L.FR, by simp, Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩)
    fun u₁ v₁ => wp_dp (op2_imm (by decide)) fun u₂ v₂ => wp_subs (op2_imm (by decide)) fun u₃ v₃ z₃ => ?_
  refine WP.block_nil ?_
  have e3 : u₃.gpr .r3 = BitVec.ofNat 32 (wipeWords - (i + 1)) := by
    rw [v₃.gpr, v₂.other _ (by decide), v₁.gpr, I.r3, VG.Proof.AesGcm.Arm.dec32 hi (by decide)]
  have hz : u₃.z = decide (i + 1 = wipeWords) := by
    rw [z₃, v₂.other _ (by decide), v₁.gpr, I.r3, VG.Proof.AesGcm.Arm.dec32 hi (by decide),
      VG.Proof.AesGcm.Arm.z_dec hi (by decide)]
  have I' : WipeI t L (i + 1) u₃ := by
    refine ⟨?_, e3, fun r h₁ h₂ => ?_, by rw [v₃.rd, v₂.rd, v₁.rd, I.rd], by rw [v₃.wr, v₂.wr, v₁.wr, I.wr],
      by rw [v₃.sp, v₂.sp, v₁.sp, I.sp], I.frame.trans ?_⟩
    · rw [v₃.other _ (by decide), v₂.gpr, dpVal, v₁.gpr, I.r12, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.mul_succ]
    · rw [v₃.other _ h₁, v₂.other _ h₂, v₁.gpr, I.other _ h₁ h₂]
    · rw [v₃.mem, v₂.mem, v₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = wipeWords) := VG.Proof.AesGcm.Arm.eval_ne' hz
  by_cases he : i + 1 = wipeWords
  · left; exact ⟨by rw [ev]; simp [he], he ▸ I'⟩
  · right; exact ⟨by rw [ev]; simp [he], wipeWords - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

theorem saved_nodup : (Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst).Nodup := by decide

/-- The frame below the saved registers cleared, and our caller's registers
back: the result kept. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa Cfg.wipe t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t'.gpr p.1 = g p.1) ∧ t'.gpr .r0 = t.gpr .r0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem t'.mem := by
  have hb := hL.B_fit
  unfold Cfg.wipe
  refine WP.seq ?_
  simp only [Cfg.wipeArgs]
  refine wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => wp_movw fun u₃ v₃ => ?_
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wipeLoop_ok hL (t := u₃) (by rw [v₃.wr, v₂.wr, v₁.wr, hc.wr])
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hc.r8])
    (by rw [v₃.gpr, movw_val (by decide)])) fun u₄ I => ?_)
  refine wp_mov (op2_reg _ _) fun u₅ v₅ => ?_
  have h8 : u₄.gpr .r8 = L.fp := by
    rw [I.other _ (by decide) (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
      hc.r8]
  have hs : VG.Proof.Mont.Arm.Scr u₅ (L.B + BitVec.ofNat 64 24) 512 :=
    ⟨by rw [v₅.gpr, h8]; exact hL.fpA0, ⟨512, by omega_arith, by omega_arith,
      by rw [v₅.wr, I.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]; simp⟩,
      by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by omega_arith⟩
  refine WP.mono (Proof.Weierstrass.Arm.ldrs_ok hs _ (fun p hp => by have := saved_off p hp; omega_arith)
    saved_nodup (by decide)) fun u₆ ⟨hm₆, K₆, hv₆⟩ => ⟨?_, ?_, ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [K₆.rd, v₅.rd, I.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [K₆.wr, v₅.wr, I.wr, v₃.wr, v₂.wr, v₁.wr]
  · rw [K₆.sp, v₅.sp, I.sp, v₃.sp, v₂.sp, v₁.sp]
  · have hfr : Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem u₅.mem := by
      rw [v₅.mem, ← v₁.mem, ← v₂.mem, ← v₃.mem]; exact I.frame
    rw [hv₆ p hp, VG.Proof.Mont.off, Offset.add_add,
      hfr.readW (r := ⟨L.B + BitVec.ofNat 64 492, 36⟩) (Offset.contains _ (by have := saved_off p hp; omega_arith)
        (by have := saved_off p hp; omega_arith) (by omega_arith))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have : wipeWords = 117 := rfl
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)]
    exact hc.saved p hp
  · rw [K₆.gpr _ (by decide), v₅.other _ (by decide), I.other _ (by decide) (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide)]
  · rw [hm₆, v₅.mem, ← v₁.mem, ← v₂.mem, ← v₃.mem]; exact I.frame

end VG.Proof.Ecdsa.Rfc6979.Arm
