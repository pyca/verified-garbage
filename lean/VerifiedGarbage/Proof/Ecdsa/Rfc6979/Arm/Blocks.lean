import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup

/-!
# Deterministic ECDSA on 32-bit ARM: the blocks between the calls

As on x86 (`Proof/Ecdsa/Rfc6979/X86/Blocks.lean`): `V = 0x01…` and
`K = 0x00…` (`initKV_ok`), the number of candidates, in `r9`
(`initCnt_ok`), whether to go on (`goOn_ok`, `again_ok`, `stop_ok`), and the
wiping of the frame with our caller's registers restored (`wipe_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_movw wp_cmp op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

/-- The `4 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 32) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (4 * j)) 32 = w) :
    Spec.Sha256.bytesAt m q (4 * k) = (List.range (4 * k)).map fun i => w.extractLsb' (8 * (i % 4)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 4 * (i / 4) + i % 4 by omega, Proof.Weierstrass.byte_word32 m q (i / 4) (Nat.mod_lt _ (by decide)),
    h _ (by omega)]
  congr 2; omega

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
    refine WP.mono (kvN_ok hL hc ha hb k (by omega)) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hv⟩ => ?_
    have e₁ : State.addr (L.fp + BitVec.ofNat 32 (fV + 4 * k)) = L.B + BitVec.ofNat 64 (88 + 4 * k) :=
      fpA' hL (by simp only [fV]; omega) (by simp only [fV]; omega)
    have e₂ : State.addr (L.fp + BitVec.ofNat 32 (fK + 4 * k)) = L.B + BitVec.ofNat 64 (24 + 4 * k) :=
      fpA' hL (by simp only [fK]; omega) (by simp only [fK]; omega)
    have o₁ : fV + 4 * k < 4096 := by simp only [fV]; omega
    have o₂ : fK + 4 * k < 4096 := by simp only [fK]; omega
    have r8₁ : u₁.gpr .r8 = L.fp := by rw [hg, hc.r8]
    refine wp_str (a := L.B + BitVec.ofNat 64 (88 + 4 * k)) o₁ (by rw [r8₁]; exact e₁)
      (by rw [hwr]; exact hc.inFrW (by omega) (by omega)) fun u₂ v₂ => ?_
    refine wp_str (a := L.B + BitVec.ofNat 64 (24 + 4 * k)) o₂ (by rw [v₂.gpr, r8₁]; exact e₂)
      (by rw [v₂.wr, hwr]; exact hc.inFrW (by omega) (by omega)) fun u₃ v₃ => WP.block_nil ?_
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 224 → y + 4 ≤ 224 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
    have hm₃ : u₃.mem = (u₁.mem.writeW (L.B + BitVec.ofNat 64 (88 + 4 * k)) a).writeW
        (L.B + BitVec.ofNat 64 (24 + 4 * k)) b := by
      rw [v₃.mem, v₂.mem, v₂.gpr, hg, ha, hb]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    refine ⟨by rw [v₃.rd, v₂.rd, hrd], by rw [v₃.wr, v₂.wr, hwr], by rw [v₃.sp, v₂.sp, hsp],
      by rw [v₃.gpr, v₂.gpr, hg], hf.trans hf₃, fun j hj => ?_⟩
    rw [hm₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide)]
      exact hv j hj
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
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
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (Upd.setReg _ _ _))

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) n = List.replicate n 0 := by
  rw [Cfg.initKV, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movw fun u₁ v₁ => wp_movt' fun u₂ v₂ => wp_mov (op2_imm (by decide)) fun u₃ v₃ => ?_
  have hc₃ : Ctx L g m₀ u₃ := ((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)
  have h0 : u₃.gpr .r0 = 0x01010101 := by rw [v₃.other _ (by decide), v₂.gpr, v₁.gpr, ones_word]
  have hm₃ : u₃.mem = t.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono (kvN_ok hL hc₃ h0 v₃.gpr 16 (by omega)) fun u' ⟨hrd', hwr', hsp', hg, hf, hv⟩ =>
      ⟨hc₃.keep hL hrd' hwr' hsp' (fun r _ => by rw [hg]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
      by rw [hm₃] at hf; exact hf, fun n hn => ?_, fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (88 : Nat) = 88 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (0x01010101 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (24 : Nat) = 24 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

theorem initCnt_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = BitVec.ofNat 32 8 :=
  movw_ok hc (d := .r9) (v := 8) (by decide) (by decide) fun t' c' m' v' _ => WP.block_nil ⟨c', m', v'⟩

/-! ## Whether to go on -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, with its carry: set iff no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [exec, ho, Option.map_some]) (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `adc`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-- The decision's arithmetic: `(C - 1) & count`, `C` set iff `r ≥ 1`, is nonzero iff `r = 0` and
`count ≠ 0`. -/
theorem decide_go (r cnt : BitVec 32) :
    (!((((0 + 0 + (if decide ((1 : BitVec 32).toNat ≤ r.toNat) = true then 1 else 0) - 1 : BitVec 32) &&& cnt) - 0)
      == 0)) = decide (r = 0 ∧ cnt ≠ 0) := by
  by_cases h : r = 0
  · subst h
    have hc : decide ((1 : BitVec 32).toNat ≤ (0 : BitVec 32).toNat) = false := by decide
    have e1 : (0 + 0 + (if false = true then 1 else 0) - 1 : BitVec 32) = BitVec.allOnes 32 := by decide
    have e2 : cnt - (0 : BitVec 32) = cnt := BitVec.sub_zero cnt
    rw [hc, e1, BitVec.allOnes_and, e2]
    by_cases h' : cnt = 0
    · subst h'; decide
    · have h'' : cnt ≠ 0#32 := h'
      simp [h'']
  · have h0 : r ≠ 0#32 := h
    have hr : decide ((1 : BitVec 32).toNat ≤ r.toNat) = true := by
      rcases Nat.eq_zero_or_pos r.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e]; rfl)) h
      · exact decide_eq_true e
    have e3 : (0 + 0 + (if true = true then 1 else 0) - 1 : BitVec 32) = 0 := by decide
    have e4 : (0 : BitVec 32) &&& cnt = 0 := BitVec.zero_and
    rw [hr, e3, e4]
    simp [h0]

/-- One candidate fewer, and `Z` clear iff the signature failed and candidates are left. -/
theorem goOn_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.gpr .r1 = t.gpr .r1 ∧
      isa.eval .ne t' = some (decide (t.gpr .r0 = 0 ∧ t.gpr .r9 - 1 ≠ 0)) := by
  simp only [Cfg.goOn]
  refine wp_dp (op2_imm (by decide)) fun u₁ v₁ => wp_subsC (op2_imm (by decide)) fun u₂ v₂ c₂ => ?_
  refine wp_movC (op2_imm (by decide)) fun u₃ v₃ c₃ => wp_adc (op2_imm (by decide)) fun u₄ v₄ => ?_
  refine wp_dp (op2_imm (by decide)) fun u₅ v₅ => wp_dp (op2_reg _ _) fun u₆ v₆ => ?_
  refine wp_cmp (op2_imm (by decide)) fun u₇ v₇ z₇ => WP.block_nil ?_
  have hc₆ : Ctx L g m₀ u₆ := (((((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)).upd v₄
    (by decide)).upd v₅ (by decide)).upd v₆ (by decide)
  have K : Rest [.r9, .r10, .r7] t u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans <|
    (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans (v₆.rest (by simp))
  have r9₅ : u₅.gpr .r9 = t.gpr .r9 - 1 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      dpVal]
  have r9₆ : u₆.gpr .r9 = t.gpr .r9 - 1 := by rw [v₆.other _ (by decide), r9₅]
  have r0₁ : u₁.gpr .r0 = t.gpr .r0 := v₁.other _ (by decide)
  refine ⟨⟨by rw [v₇.rd]; exact hc₆.rd, by rw [v₇.wr]; exact hc₆.wr, by rw [v₇.sp]; exact hc₆.sp,
      by rw [v₇.gpr]; exact hc₆.r4, by rw [v₇.gpr]; exact hc₆.r5, by rw [v₇.gpr]; exact hc₆.r6,
      by rw [v₇.gpr]; exact hc₆.r8, by rw [v₇.gpr]; exact hc₆.r11, fun p hp => by rw [v₇.mem]; exact hc₆.saved p hp,
      by rw [v₇.mem]; exact hc₆.frame⟩,
    by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₇.gpr]; exact r9₆,
    by rw [v₇.gpr, K.gpr _ (by decide)], by rw [v₇.gpr, K.gpr _ (by decide)], ?_⟩
  show some (!u₇.z) = _
  rw [z₇, v₆.gpr, dpVal, v₅.gpr, dpVal, v₄.gpr, v₃.gpr, c₃, c₂, r9₅, r0₁, decide_go]

theorem flag_ok {t : State} (hc : Ctx L g m₀ t) {v : Nat} (hv : v < 2) :
    WP isa (.block [.mov .r7 (.imm (BitVec.ofNat 32 v)), .cmp .r7 (.imm 0)]) t fun t' => Ctx L g m₀ t' ∧
      t'.mem = t.mem ∧ (∀ r, r ≠ .r7 → t'.gpr r = t.gpr r) ∧ isa.eval .ne t' = some (decide (v = 1)) :=
  wp_mov (op2_imm (by rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> decide)) fun u₁ v₁ =>
    wp_cmp (op2_imm (by decide)) fun u₂ v₂ z₂ => WP.block_nil
      ⟨⟨by rw [v₂.rd]; exact (hc.upd v₁ (by decide)).rd, by rw [v₂.wr]; exact (hc.upd v₁ (by decide)).wr,
        by rw [v₂.sp]; exact (hc.upd v₁ (by decide)).sp, by rw [v₂.gpr]; exact (hc.upd v₁ (by decide)).r4,
        by rw [v₂.gpr]; exact (hc.upd v₁ (by decide)).r5, by rw [v₂.gpr]; exact (hc.upd v₁ (by decide)).r6,
        by rw [v₂.gpr]; exact (hc.upd v₁ (by decide)).r8, by rw [v₂.gpr]; exact (hc.upd v₁ (by decide)).r11,
        fun p hp => by rw [v₂.mem]; exact (hc.upd v₁ (by decide)).saved p hp,
        by rw [v₂.mem]; exact (hc.upd v₁ (by decide)).frame⟩,
      by rw [v₂.mem, v₁.mem], fun r hr => by rw [v₂.gpr, v₁.other _ hr],
      by
        show some (!u₂.z) = _
        rw [z₂, v₁.gpr]
        rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> decide⟩

/-- `Z` clear: go on. -/
theorem again_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 ∧
      isa.eval .ne t' = some true :=
  WP.mono (flag_ok hc (v := 1) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-- `Z` set: stop. -/
theorem stop_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r0 = t.gpr .r0 ∧
      isa.eval .ne t' = some false :=
  WP.mono (flag_ok hc (v := 0) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-! ## The wiping -/

/-- `k` zero words stored at the frame's start, through `r12`: only `K`, `V` and `h` change. -/
theorem zeroN_ok (hL : L.Ok) {u : State} (hwr : u.wr = [L.FR, L.OUT, L.SCR]) (h12 : u.gpr .r12 = L.fp) :
    ∀ k ≤ 40, WP isa (.block ((List.range k).map fun j => .str .r1 .r12 (4 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] u.mem u'.mem
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hL hwr h12 k (by omega)) fun u₁ ⟨hrd, hwr₁, hsp, hg, hf⟩ => ?_
    have e : State.addr (L.fp + BitVec.ofNat 32 (4 * k)) = L.B + BitVec.ofNat 64 (24 + 4 * k) := hL.fpA (by omega)
    refine wp_str (a := L.B + BitVec.ofNat 64 (24 + 4 * k)) (by omega) (by rw [hg, h12]; exact e)
      (by rw [hwr₁, hwr]; exact ⟨L.FR, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩)
      fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr₁], by rw [v₂.sp, hsp],
        by rw [v₂.gpr, hg], hf.trans ?_⟩
    rw [v₂.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem zeros_map : Cfg.zeros.map (fun p => Instr.str p.1 .r12 p.2) =
    (List.range 40).map fun j => .str .r1 .r12 (4 * j) := by
  simp only [Cfg.zeros, List.map_map]; rfl

theorem saved_nodup : (Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst).Nodup := by decide

/-- The frame cleared, and our caller's registers back: the result and `out` kept. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t'.gpr p.1 = g p.1) ∧ t'.gpr .r0 = t.gpr .r0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] t.mem t'.mem := by
  simp only [Cfg.wipe, zeros_map, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => ?_
  have h12 : u₂.gpr .r12 = L.fp := by rw [v₂.other _ (by decide), v₁.gpr, hc.r8]
  have hwr₂ : u₂.wr = [L.FR, L.OUT, L.SCR] := by rw [v₂.wr, v₁.wr, hc.wr]
  rw [WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hwr₂ h12 40 (Nat.le_refl _)) fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hf₃⟩ => ?_
  have hb := hL.B_fit
  have hs : VG.Proof.Mont.Arm.Scr u₃ (L.B + BitVec.ofNat 64 24) 200 :=
    ⟨by rw [hg₃, h12]; exact hL.fpA0, ⟨200, by omega, by omega, by rw [hwr₃, hwr₂]; simp⟩,
      by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by omega⟩
  refine WP.mono (Proof.Ecdsa.Arm.ldrs_ok hs _ (fun p hp => (saved_off p hp).2) saved_nodup (by decide))
    fun u₄ ⟨hm₄, K₄, hv₄⟩ => ⟨?_, ?_, ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [K₄.rd, hrd₃, v₂.rd, v₁.rd]
  · rw [K₄.wr, hwr₃, v₂.wr, v₁.wr]
  · rw [K₄.sp, hsp₃, v₂.sp, v₁.sp]
  · have hfr : Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] t.mem u₃.mem := by rw [← v₁.mem, ← v₂.mem]; exact hf₃
    rw [hv₄ p hp, VG.Proof.Mont.off, Offset.add_add,
      hfr.readW (r := ⟨L.B + BitVec.ofNat 64 188, 36⟩) (Offset.contains _ (by have := saved_off p hp; omega)
        (by have := saved_off p hp; omega) (by omega))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    exact hc.saved p hp
  · rw [K₄.gpr _ (by decide), hg₃, v₂.other _ (by decide), v₁.other _ (by decide)]
  · rw [hm₄, ← v₁.mem, ← v₂.mem]; exact hf₃

end VG.Proof.Ecdsa.Rfc6979.Arm
