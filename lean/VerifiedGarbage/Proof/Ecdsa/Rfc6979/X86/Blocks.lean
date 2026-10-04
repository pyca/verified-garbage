import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Deterministic ECDSA on x86 (32-bit): the blocks between the calls

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Blocks.lean`): `V = 0x01…` and
`K = 0x00…` (`initKV_ok`), the number of candidates (`initCnt_ok`), the
arguments of `core` (`coreArgs_ok`), whether to go on (`goOn_ok`,
`again_ok`, `stop_ok`), and the wiping of the frame with our caller's
registers restored (`wipe_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS)

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
    refine WP.mono (kvN_ok hL hc ha hb k (by omega)) fun u₁ ⟨hrd, hwr, hg, hf, hv⟩ => ?_
    have e₁ : addr L.F (fV + 4 * k) = L.B + BitVec.ofNat 64 (140 + 4 * k) := by
      rw [hL.addrF (by simp only [fV]; omega)]; congr 2; simp only [fV]; omega
    have e₂ : addr L.F (fK + 4 * k) = L.B + BitVec.ofNat 64 (76 + 4 * k) := by
      rw [hL.addrF (by simp only [fK]; omega)]; congr 2; simp only [fK]; omega
    have esp₁ : u₁.gpr .esp = L.F := by rw [hg, hc.esp]
    refine wp_stm esp₁ (by rw [e₁, hwr]; exact hc.inFrW (by omega) (by omega) hL) fun u₂ v₂ => ?_
    refine wp_stm (B := L.F) (by rw [v₂.gpr, esp₁]) (by rw [e₂, v₂.wr, hwr]; exact hc.inFrW (by omega) (by omega) hL)
      fun u₃ v₃ => WP.block_nil ?_
    rw [e₁, hg, ha] at v₂; rw [e₂, v₂.gpr, hg, hb] at v₃
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 276 → y + 4 ≤ 276 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
    have hm₃ : u₃.mem = (u₁.mem.writeW (L.B + BitVec.ofNat 64 (140 + 4 * k)) a).writeW
        (L.B + BitVec.ofNat 64 (76 + 4 * k)) b := by rw [v₃.mem, v₂.mem]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    refine ⟨by rw [v₃.rd, v₂.rd, hrd], by rw [v₃.wr, v₂.wr, hwr], by rw [v₃.gpr, v₂.gpr, hg],
      hf.trans hf₃, fun j hj => ?_⟩
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

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 140) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) n = List.replicate n 0 := by
  rw [Cfg.initKV, WP.block_append_iff]
  refine wp_movi fun u₁ v₁ => wp_movi fun u₂ v₂ => WP.block_nil ?_
  have hc₂ : Ctx L g m₀ u₂ := (Upd.of_wp hL (Upd.of_wp hL hc (by decide) v₁).ctx (by decide) v₂).ctx
  refine WP.mono (kvN_ok hL hc₂ (a := 0x01010101) (by rw [v₂.other _ (by decide), v₁.gpr]) v₂.gpr 16 (by omega))
    fun u' ⟨hrd', hwr', hg, hf, hv⟩ =>
      ⟨hc₂.keep hL hrd' hwr' (by rw [hg]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
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
abbrev cnt {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 236) 32

theorem cnt_addr (hL : L.Ok) : addr L.F fCnt = L.B + BitVec.ofNat 64 236 := hL.addrF (by decide)

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 32 8 := by
  simp only [Cfg.initCnt, cfgOf, stk]
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [cnt_addr hL, v₁.wr]; exact hc.inFrW (by omega) (by omega) hL) fun u₂ v₂ => WP.block_nil ?_
  rw [cnt_addr hL, v₁.gpr, v₁.mem] at v₂
  have hf : Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] t.mem u₂.mem := by
    rw [v₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)), hf, ?_⟩
  simp only [cnt, v₂.mem, Mem.readW_writeW_self32]

/-! ## `core`'s arguments -/

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .edi = L.a0 ∧
      t'.gpr .esi = L.a1 ∧ t'.gpr .edx = L.a2 ∧ t'.gpr .ecx = L.F + BitVec.ofNat 32 64 ∧ t'.gpr .ebp = L.a3 := by
  rw [show Cfg.coreArgs = [.mov .edi (argM 0)] ++ ([.mov .esi (argM 1)] ++ ([.mov .edx (argM 2)] ++
    (Cfg.fr .ecx fV ++ [.mov .ebp (argM 3)]))) from rfl]
  refine WP.block_append (WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 0) (by omega)) fun u₁ h₁ => ?_)
  refine WP.block_append (WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega)) fun u₂ h₂ => ?_)
  refine WP.block_append (WP.mono (arg_ok hL h₂.ctx (d := .edx) (by decide) (i := 2) (by omega)) fun u₃ h₃ => ?_)
  refine WP.block_append (WP.mono (fr_ok hL h₃.ctx (d := .ecx) (by decide) fV) fun u₄ h₄ => ?_)
  refine WP.mono (arg_ok hL h₄.ctx (d := .ebp) (by decide) (i := 3) (by omega)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.val]; rfl

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
        show a.toNat = 0; omega))
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
      Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .eax = t.gpr .eax ∧
      t'.zf = some (!decide (t.gpr .eax = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  simp only [Cfg.goOn, stk]
  refine wp_ldm hc.esp (by rw [cnt_addr hL]; exact hc.inFr (by omega) (by omega) hL) fun u₁ v₁ => ?_
  refine wp_subi fun u₂ v₂ _ _ => ?_
  refine wp_stm (B := L.F) (by rw [v₂.other _ (by decide), v₁.other _ (by decide), hc.esp])
    (by rw [cnt_addr hL, v₂.wr, v₁.wr]; exact hc.inFrW (by omega) (by omega) hL) fun u₃ v₃ => ?_
  refine wp_cmpi fun u₄ v₄ cf₄ _ => wp_sbb_self cf₄ fun u₅ v₅ => wp_and fun u₆ v₆ => wp_test fun u₇ v₇ zf₇ =>
    WP.block_nil ?_
  rw [cnt_addr hL] at v₁ v₃
  have eax₃ : u₃.gpr .eax = t.gpr .eax := by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide)]
  have cx₃ : u₃.gpr .ecx = cnt L t.mem - 1 := by rw [v₃.gpr, v₂.gpr, v₁.gpr]
  have hm₃ : u₃.mem = t.mem.writeW (L.B + BitVec.ofNat 64 236) (cnt L t.mem - 1) := by
    rw [v₃.mem, v₂.mem, v₁.mem, v₂.gpr, v₁.gpr]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] t.mem u₇.mem := by
    rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, hm₃]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL (by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd])
      (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide),
        v₁.other _ (by decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    hf, by rw [cnt, v₇.mem, v₆.mem, v₅.mem, v₄.mem, hm₃, Mem.readW_writeW_self32],
    by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, eax₃], ?_⟩
  rw [zf₇, v₆.gpr, v₅.gpr, v₅.other .ecx (by decide), v₄.gpr, cx₃, eax₃, goOn_flag]

/-- `ZF` clear. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some false :=
  wp_movi fun u₁ v₁ => wp_test fun u₂ v₂ zf₂ => WP.block_nil
    ⟨(Upd.of_wp hL hc (by decide) v₁).ctx.regs hL v₂.rd v₂.wr v₂.mem (by rw [v₂.gpr]),
      by rw [v₂.mem, v₁.mem], by rw [zf₂, v₁.gpr]; decide⟩

/-- `ZF` set. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some true ∧
      t'.gpr .eax = t.gpr .eax :=
  wp_movi fun u₁ v₁ => wp_test fun u₂ v₂ zf₂ => WP.block_nil
    ⟨(Upd.of_wp hL hc (by decide) v₁).ctx.regs hL v₂.rd v₂.wr v₂.mem (by rw [v₂.gpr]),
      by rw [v₂.mem, v₁.mem], by rw [zf₂, v₁.gpr]; decide, by rw [v₂.gpr, v₁.other _ (by decide)]⟩

/-! ## The wiping -/

/-- `k` zero words stored at the frame's start: only `K`, `V` and `h` change. -/
theorem zeroN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : ∀ k ≤ 40,
    WP isa (.block ((List.range k).map fun j => .store (stk (4 * j)) .ecx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    have nB := hL.nB
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hL hc k (by omega)) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have e : addr L.F (4 * k) = L.B + BitVec.ofNat 64 (76 + 4 * k) := hL.addrF (by omega)
    refine wp_stm (B := L.F) (by rw [hg, hc.esp]) (by rw [e, hwr]; exact hc.inFrW (by omega) (by omega) hL)
      fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr], by rw [v₂.gpr, hg], hf.trans ?_⟩
    rw [v₂.mem, e]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- One of our caller's registers, restored. -/
theorem restoreOne_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {r : Reg} {d : Nat} (hp : (r, d) ∈ saved)
    (hr : r ≠ .esp) : WP isa (.block [.mov r (.mem (stk d))]) u (Upd L g m₀ u r (g r)) := by
  have ho := saved_off _ hp
  have e : addr L.F d = L.B + BitVec.ofNat 64 (76 + d) := hL.addrF (by omega)
  have hs := hc.saved (r, d) hp
  dsimp only at hs
  refine wp_ldm hc.esp (by rw [e]; exact hc.inFr (by omega) (by omega) hL) fun _ v₁ => WP.block_nil ?_
  rw [e, hs] at v₁
  exact Upd.of_wp hL hc hr v₁

/-- Our caller's registers, restored. -/
theorem restore_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.restore) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .eax = u.gpr .eax ∧
      ∀ p ∈ saved, u'.gpr p.1 = g p.1 := by
  rw [show Cfg.restore = [.mov .ebx (.mem (stk 164))] ++ ([.mov .esi (.mem (stk 168))] ++
    ([.mov .edi (.mem (stk 172))] ++ [.mov .ebp (.mem (stk 176))])) from rfl]
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

/-- `K`, `V` and `h` cleared (`eax` kept), and our caller's registers back. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .eax = t.gpr .eax ∧
      Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] t.mem t'.mem ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 := by
  rw [Cfg.wipe]
  refine WP.block_append (WP.block_append (wp_movi fun u₁ v₁ => WP.block_nil ?_))
  have hc₁ := (Upd.of_wp hL hc (by decide) v₁).ctx
  refine WP.mono (zeroN_ok hL hc₁ 40 (Nat.le_refl _)) fun u₂ ⟨hrd, hwr, hg, hf⟩ => ?_
  have hc₂ : Ctx L g m₀ u₂ := hc₁.keep hL hrd hwr (by rw [hg]) hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega))
  refine WP.mono (restore_ok hL hc₂) fun t' ⟨hc', hm', ha', hs'⟩ => ⟨hc', ?_, ?_, hs'⟩
  · rw [ha', hg, v₁.other _ (by decide)]
  · rw [hm', ← v₁.mem]; exact hf

end VG.Proof.Ecdsa.Rfc6979.X86
