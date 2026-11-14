module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Divstep.WordDef
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbLoops
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! # The batched inverse on RISC-V: the divsteps

`wstepCode_ok`: one divstep's code leaves in `t6`, `a4`, `t0`–`t4` the words
of `Proof/Divstep/WordDef.lean`'s `wstep` of their values; `wsteps_ok`: `k` of
them, `wsteps k`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Divstep (WSt wstep)

/-- The words of a divstep: `d f g u v q r` in `t6`, `a4`, `t0`–`t4`. -/
def regsW (s : State) : WSt :=
  ⟨s.gpr .t6, s.gpr .a4, s.gpr .t0, s.gpr .t1, s.gpr .t2, s.gpr .t3, s.gpr .t4⟩

/-- The registers the divsteps and the array operations change. -/
abbrev kRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .a7]

theorem wstepCode_ok (s : State) :
    WP isa (.block wstepCode) s fun t => (regsW t = wstep (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [wstepCode, regsW, fin64_exec_li_zero]
  simp only [wstep, Divstep.shl1]
  rfl

/-- `k` divsteps, unrolled. -/
theorem wsteps_ok (k : Nat) (s : State) :
    WP isa (.block (wsteps k)) s fun t =>
      (regsW t = Divstep.wsteps k (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  induction k generalizing s with
  | zero => exact WP.block_nil ⟨⟨rfl, rfl⟩, Keep.refl _ _⟩
  | succ k ih =>
    rw [wsteps, List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (wstepCode_ok s) fun t ⟨⟨e, m⟩, k₁⟩ => WP.mono (ih t) fun u ⟨⟨e₂, m₂⟩, k₂⟩ =>
      ⟨⟨by rw [e₂, e]; rfl, m₂.trans m⟩, Keep.trans' k₁ k₂⟩

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: its array operations

Over `ν = ⌈n / 2⌉` words (`nu n`) of the key operations' arrays, `n` in
`s8`: `mac_ok` (`[o] = [a] + k [b]`), `csub_ok`, `signSel_ok`; the
borrowed registers' spill and restore (`spill_ok`, `restore_ok`,
`spill_restore`); and the passes' straight-line blocks (`passSetup_ok`,
`fgFirst_ok`, `fgTop_ok`, `abFirst_ok`, `abLast_ok`) with their ends as
`shr_nat` and `mredRaw_nat` read them (`fg_end`, `ab_end`).
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.RISCV64.Loops (loopRegs Ahead)
open VG.RISCV64.RegUpd

/-! ## The context -/

/-- The working space, and `n` in `s8`. -/
structure Ctx (s : State) (B : Addr) (Z w N n : Nat) : Prop where
  ws : Ws s B Z w N
  s8 : s.gpr .s8 = BitVec.ofNat 64 n
  npos : 1 ≤ n
  nw : n ≤ 2 * w
  room : 15 ≤ N
  wbig : 4 ≤ w

theorem Ctx.of_keep {s t : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n)
    (k : Keep kRegs s t) : Ctx t B Z w N n :=
  ⟨h.ws.of_keep k, (k.gpr (by decide)).trans h.s8, h.npos, h.nw, h.room, h.wbig⟩

/-- A block that keeps `s8`–`s11` keeps the context. -/
theorem Ctx.of_keep' {s t : State} {B : Addr} {Z w N n : Nat} {rs : List Reg} (h : Ctx s B Z w N n)
    (k : Keep rs s t) (h8 : .s8 ∉ rs := by decide) (h9 : .s9 ∉ rs := by decide) (h10 : .s10 ∉ rs := by decide)
    (h11 : .s11 ∉ rs := by decide) : Ctx t B Z w N n :=
  ⟨h.ws.of_keep k h9 h10 h11, (k.gpr h8).trans h.s8, h.npos, h.nw, h.room, h.wbig⟩

/-- The words the inverse works on, `⌈n / 2⌉`. -/
abbrev nu (n : Nat) : Nat := (n + 1) / 2

theorem Ctx.nu1 {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) : 1 ≤ nu n := by
  have := h.npos; unfold nu; omega_using [this]

theorem Ctx.nuw {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) : nu n ≤ w := by
  have := h.nw; unfold nu; omega_using [this]

/-- `n` digits fit in `ν` words. -/
theorem pow_nu (n : Nat) : 2 ^ (32 * n) ≤ 2 ^ (64 * nu n) :=
  Nat.pow_le_pow_right (by decide) (by unfold nu; omega_using [])

/-! ## Blocks -/

/-- `ldW r o`: `r` := the window's 64-bit word at `o`. -/
theorem ldW_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {r : Reg}
    (h10 : r ≠ .s10) (h11 : r ≠ .s11) {o : Nat} (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (off B (arr w aW + o)) 64)) Q) :
    WP isa (.block (ldW r o ++ rest)) s Q := by
  have fit := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega_using [this])
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  rw [ldW, List.append_assoc]
  refine ptr_ok h.ws h10 h11 (by decide) ?_
  rw [WP.block_append_iff]
  have hs := h.ws.scr
  have hl : InRegions ((s.write r (off B (arr w aW))).rd ++ (s.write r (off B (arr w aW))).wr)
      ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o) 8 := by
    simp only [gpr_write, ↓reduceIte, rd_write, wr_write, off_add]
    exact hs.ld (d := arr w aW + o) (n := 8) (by omega_using [ho, fit, hS, this])
  have ha : ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o).toNat % 8 = 0 := by
    simp only [gpr_write, ↓reduceIte, off_add]
    exact hs.al8 (by omega_using [ho, fit, hS, this]) (by have := arr_al w aW; omega_using [ho8, this])
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (by omega_using [ho]) ha hl,
    gpr_write, ↓reduceIte, off_add, mem_write, Option.some.injEq, exists_eq_left', write_write]
  exact k

/-- Arrays apart are each ahead of the other, for `k` words (`8 k ≤ S w`). -/
theorem ahead_k {w o a k : Nat} (h : o ≠ a) (hk : 8 * k ≤ S w) : Ahead (arr w o) (arr w a) k := by
  have := arr_disj (w := w) h
  unfold Ahead; omega_using [hk, this]

/-- Arrays equal or apart: `o` is ahead of `a`, for `k` words (`8 k ≤ S w`). -/
theorem ahead_any (w o a k : Nat) (hk : 8 * k ≤ S w) : Ahead (arr w o) (arr w a) k := by
  by_cases e : o = a
  · subst e; exact .inl (Nat.le_refl _)
  · exact ahead_k e hk

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

theorem ofNat_half {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h])]

/-! ## The borrowed registers -/

/-- `stD rs o`: the registers `rs` stored to the words from offset `o` of
`t0`'s address. -/
theorem stD_ok {B : Addr} {Z d : Nat} (hd8 : d % 8 = 0) :
    ∀ (rs : List Reg) (o : Nat) (s : State), Scr s B Z → s.gpr .t0 = off B d → o % 8 = 0 →
      d + o + 8 * rs.length ≤ Z → o + 8 * rs.length ≤ 2048 →
      WP isa (.block (stD rs o)) s fun u => Keep [] s u ∧ Outside B (d + o) (8 * rs.length) s.mem u.mem ∧
        ∀ i (hi : i < rs.length), word u.mem B (d + o + 8 * i) = s.gpr rs[i]
  | [], _, _, _, _, _, _, _ => WP.block_nil ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun i hi => absurd hi (by simp)⟩
  | r :: rs, o, s, hs, h0, ho8, hZ, ho => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at hZ ho ⊢
    rw [stD, show (Instr.store .d r .t0 o :: stD rs (o + 8)) = [Instr.store .d r .t0 o] ++ stD rs (o + 8) from rfl,
      WP.block_append_iff]
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (d + o)) (s.gpr r)) ?_ (by rfl) (by rfl))
      fun u ⟨mu, ku⟩ => ?_
    · brun [h0, off_add, (show o < 2048 by omega_using [ho]), hs.st (show d + o + 8 ≤ Z by omega_using [hZ]),
        hs.al8 (show d + o + 8 ≤ Z by omega_using [hZ]) (by omega_using [hd8, ho8])]
    have h0' : u.gpr .t0 = off B d := (ku.gpr (by simp)).trans h0
    have e1 : d + (o + 8) + 8 * rs.length ≤ Z := by omega_using [hZ]
    have e2 : o + 8 + 8 * rs.length ≤ 2048 := by omega_using [ho]
    refine WP.mono (stD_ok hd8 rs (o + 8) u (hs.congr ku.2.2) h0' (by omega_using [ho8]) e1 e2)
      fun v ⟨kv, ov, rv⟩ => ⟨(ku.trans kv).mono (by simp), ?_, fun i hi => ?_⟩
    · rw [mu] at ov
      exact ((writeW_outside _ B _ (d := d + o) (by omega_using [hZ, hnw])).mono (by omega_using []) (by omega_using [])).trans
        (ov.mono (by omega_using []) (by omega_using []))
    · cases i with
      | zero =>
        rw [Nat.mul_zero, Nat.add_zero, ov.word (by omega_using []) (by omega_using [hZ, hnw]), mu, word_writeW_self]; rfl
      | succ j =>
        rw [show d + o + 8 * (j + 1) = d + (o + 8) + 8 * j by omega_using [], rv j (by simp at hi; omega_using [hi]),
          List.getElem_cons_succ]
        exact ku.gpr (by simp)

/-- `ldD rs o`: the registers `rs` (distinct, not `t0`) loaded from the words
from offset `o` of `t0`'s address. -/
theorem ldD_ok {B : Addr} {Z d : Nat} (hd8 : d % 8 = 0) :
    ∀ (rs : List Reg) (o : Nat) (s : State), Scr s B Z → s.gpr .t0 = off B d → .t0 ∉ rs → rs.Nodup →
      o % 8 = 0 → d + o + 8 * rs.length ≤ Z → o + 8 * rs.length ≤ 2048 →
      WP isa (.block (ldD rs o)) s fun u => Keep rs s u ∧ u.mem = s.mem ∧
        ∀ i (hi : i < rs.length), u.gpr rs[i] = word s.mem B (d + o + 8 * i)
  | [], _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨Keep.refl _ _, rfl, fun i hi => absurd hi (by simp)⟩
  | r :: rs, o, s, hs, h0, ht0, hnd, ho8, hZ, ho => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at hZ ho ⊢
    simp only [List.mem_cons, not_or] at ht0
    rw [List.nodup_cons] at hnd
    rw [ldD, show (Instr.load .d r .t0 o :: ldD rs (o + 8)) = [Instr.load .d r .t0 o] ++ ldD rs (o + 8) from rfl,
      WP.block_append_iff]
    have hl : WP isa (.block [Instr.load .d r .t0 o]) s fun u =>
        u.gpr r = word s.mem B (d + o) ∧ u.mem = s.mem ∧ Keep [r] s u := by
      have ha : (s.gpr .t0 + BitVec.ofNat 64 o).toNat % 8 = 0 := by
        rw [h0, off_add]; exact hs.al8 (by omega_using [hZ]) (by omega_using [hd8, ho8])
      have hr : InRegions (s.rd ++ s.wr) (s.gpr .t0 + BitVec.ofNat 64 o) 8 := by
        rw [h0, off_add]; exact hs.ld (by omega_using [hZ])
      refine WP.of_runBlock ?_
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (show o < 2048 by omega_using [ho]) ha hr]
      refine ⟨_, rfl, ?_, ?_, Keep.write _ _ _⟩
      · simp only [gpr_write, ↓reduceIte, h0, off_add]
      · rfl
    refine WP.mono hl fun u ⟨ur, mu, ku⟩ => ?_
    have h0' : u.gpr .t0 = off B d := (ku.gpr (by simp [ht0.1])).trans h0
    have e1 : d + (o + 8) + 8 * rs.length ≤ Z := by omega_using [hZ]
    have e2 : o + 8 + 8 * rs.length ≤ 2048 := by omega_using [ho]
    refine WP.mono (ldD_ok hd8 rs (o + 8) u (hs.congr ku.2.2) h0' ht0.2 hnd.2 (by omega_using [ho8]) e1 e2)
      fun v ⟨kv, mv, rv⟩ => ⟨(ku.trans kv).mono (by simp), mv.trans mu, fun i hi => ?_⟩
    · cases i with
      | zero => rw [List.getElem_cons_zero, kv.gpr hnd.1, ur, Nat.mul_zero, Nat.add_zero]
      | succ j =>
        rw [List.getElem_cons_succ, rv j (by simp at hi; omega_using [hi]), mu,
          show d + (o + 8) + 8 * j = d + o + 8 * (j + 1) by omega_using []]

/-- `spill`: the borrowed registers to words 0–5 of arrays 11 and 12. -/
theorem spill_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) :
    WP isa (.block spill) s fun u => Keep [.t0] s u ∧ Keys.Frame B w [aT1, aT2] [] s.mem u.mem ∧
      (∀ i (hi : i < spill1.length), word u.mem B (arr w aT1 + 8 * i) = s.gpr spill1[i]) ∧
      ∀ i (hi : i < spill2.length), word u.mem B (arr w aT2 + 8 * i) = s.gpr spill2[i] := by
  have r1 : aT1 < N := by have := h.room; unfold aT1; omega_using [this]
  have r2 : aT2 < N := by have := h.room; unfold aT2; omega_using [this]
  have f1 := h.ws.arr_fit r1
  have f2 := h.ws.arr_fit r2
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have a1 := arr_al w aT1
  have a2 := arr_al w aT2
  have d12 := arr_disj (w := w) (show aT1 ≠ aT2 by decide)
  rw [spill, List.append_assoc, List.append_assoc]
  refine ptr_ok h.ws (by decide) (by decide) (by decide) ?_
  rw [WP.block_append_iff]
  refine WP.mono (stD_ok a1 spill1 0 _ (h.ws.scr.congr rfl) (by simp [gpr_write]) rfl (by simp [spill1]; omega_using [f1, hS, this])
    (by simp [spill1])) fun u ⟨ku, ou, ru⟩ => ?_
  have hu := h.ws.of_keep (((Keep.write _ .t0 _).trans ku).mono (rs' := [.t0]) (by simp))
  refine ptr_ok hu (by decide) (by decide) (by decide) ?_
  refine WP.mono (stD_ok a2 spill2 0 _ (hu.scr.congr rfl) (by simp [gpr_write]) rfl (by simp [spill2]; omega_using [f2, hS, this])
    (by simp [spill2])) fun v ⟨kv, ov, rv⟩ => ?_
  have kuv : Keep [.t0] s v :=
    ((((Keep.write _ .t0 _).trans ku).trans (Keep.write _ .t0 _)).trans kv).mono (by simp)
  simp only [mem_write, Nat.add_zero] at ou ov ru rv
  refine ⟨kuv, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · exact (Keys.Frame.of_arr (o := aT1) (d := 0) (by simpa only [Nat.add_zero] using ou)
      (by simp [spill1]; omega_using [hS, this]) (by simp)).trans
      (Keys.Frame.of_arr (o := aT2) (d := 0) (by simpa only [Nat.add_zero] using ov) (by simp [spill2]; omega_using [hS, this])
        (by simp))
  · rw [ov.word (by simp only [spill1, spill2, List.length_cons, List.length_nil] at hi ⊢; omega_using [hS, this, d12, hi])
      (by simp only [spill1, List.length_cons, List.length_nil] at hi; omega_using [f1, hS, this, hnw, hi]), ru i hi]
    simp only [gpr_write]
    have : spill1[i] ≠ .t0 := by
      have := List.getElem_mem hi; intro e; rw [e] at this; simp [spill1] at this
    simp [this]
  · rw [rv i hi]
    have hne : spill2[i] ≠ .t0 := by
      have := List.getElem_mem hi; intro e; rw [e] at this; simp [spill2] at this
    rw [gpr_write, ku.gpr (by simp), gpr_write]
    simp only [hne, ↓reduceIte]

/-- `restore`: the borrowed registers back from words 0–5 of arrays 11 and 12. -/
theorem restore_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) :
    WP isa (.block restore) s fun u => Keep (.t0 :: (spill1 ++ spill2)) s u ∧ u.mem = s.mem ∧
      (∀ i (hi : i < spill1.length), u.gpr spill1[i] = word s.mem B (arr w aT1 + 8 * i)) ∧
      ∀ i (hi : i < spill2.length), u.gpr spill2[i] = word s.mem B (arr w aT2 + 8 * i) := by
  have r1 : aT1 < N := by have := h.room; unfold aT1; omega_using [this]
  have r2 : aT2 < N := by have := h.room; unfold aT2; omega_using [this]
  have f1 := h.ws.arr_fit r1
  have f2 := h.ws.arr_fit r2
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have a1 := arr_al w aT1
  have a2 := arr_al w aT2
  rw [restore, List.append_assoc, List.append_assoc]
  refine ptr_ok h.ws (by decide) (by decide) (by decide) ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldD_ok a1 spill1 0 _ (h.ws.scr.congr rfl) (by simp [gpr_write]) (by decide) (by decide) rfl
    (by simp [spill1]; omega_using [f1, hS, this]) (by simp [spill1])) fun u ⟨ku, mu, ru⟩ => ?_
  have hu := h.ws.of_keep (((Keep.write _ .t0 _).trans ku).mono (rs' := .t0 :: spill1) (by simp)) (by decide)
    (by decide) (by decide)
  refine ptr_ok hu (by decide) (by decide) (by decide) ?_
  refine WP.mono (ldD_ok a2 spill2 0 _ (hu.scr.congr rfl) (by simp [gpr_write]) (by decide) (by decide) rfl
    (by simp [spill2]; omega_using [f2, hS, this]) (by simp [spill2])) fun v ⟨kv, mv, rv⟩ => ?_
  simp only [mem_write, Nat.add_zero] at mu mv ru rv
  refine ⟨((((Keep.write _ .t0 _).trans ku).trans (Keep.write _ .t0 _)).trans kv).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind),
    by rw [mv, mu], fun i hi => ?_, fun i hi => ?_⟩
  · have hne : spill1[i] ∉ spill2 := by
      have := List.getElem_mem hi; revert this; generalize spill1[i] = r; revert r; decide
    have hne0 : spill1[i] ≠ .t0 := by
      have := List.getElem_mem hi; intro e; rw [e] at this; simp [spill1] at this
    rw [kv.gpr hne, gpr_write]
    simp only [hne0, ↓reduceIte]
    rw [ru i hi]
  · rw [rv i hi, mu]

/-- The borrowed registers back where they were: what changes only `kRegs`
around a spill and a restore changes only `kRegs`. -/
theorem spill_restore {s u v x : State} {B : Addr} {w : Nat}
    (k1 : Keep [.t0] s u)
    (r1 : ∀ i (hi : i < spill1.length), word u.mem B (arr w aT1 + 8 * i) = s.gpr spill1[i])
    (r2 : ∀ i (hi : i < spill2.length), word u.mem B (arr w aT2 + 8 * i) = s.gpr spill2[i])
    (k2 : Keep (kRegs ++ (spill1 ++ spill2)) u v)
    (w1 : ∀ i < 6, word v.mem B (arr w aT1 + 8 * i) = word u.mem B (arr w aT1 + 8 * i))
    (w2 : ∀ i < 6, word v.mem B (arr w aT2 + 8 * i) = word u.mem B (arr w aT2 + 8 * i))
    (k3 : Keep (.t0 :: (spill1 ++ spill2)) v x)
    (l1 : ∀ i (hi : i < spill1.length), x.gpr spill1[i] = word v.mem B (arr w aT1 + 8 * i))
    (l2 : ∀ i (hi : i < spill2.length), x.gpr spill2[i] = word v.mem B (arr w aT2 + 8 * i)) :
    Keep kRegs s x := by
  refine ⟨fun r hr => ?_, k3.2.1.trans (k2.2.1.trans k1.2.1), k3.2.2.trans (k2.2.2.trans k1.2.2)⟩
  by_cases h1 : r ∈ spill1
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h1
    rw [l1 i hi, w1 i (by simpa [spill1] using hi), r1 i hi]
  by_cases h2 : r ∈ spill2
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h2
    rw [l2 i hi, w2 i (by simpa [spill2] using hi), r2 i hi]
  have ht0 : r ≠ .t0 := fun e => hr (by rw [e]; decide)
  rw [k3.gpr (by simp only [List.mem_cons, List.mem_append, not_or]; exact ⟨ht0, h1, h2⟩),
    k2.gpr (by simp only [List.mem_append, not_or]; exact ⟨hr, h1, h2⟩), k1.gpr (by simp [ht0])]

/-! ## Counts -/

theorem cntN_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN) t fun x => (x.gpr .t3 = BitVec.ofNat 64 (nu n) ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  have := h.nw; have := h.ws.wle
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN, h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega_arith)]

theorem cntN1_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN1) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  have := h.nw; have := h.ws.wle
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN1, cntN, h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega_arith)]

/-! ## `lin` -/

/-! ## `shr` -/

/-- An arithmetic shift by 59, unsigned: the top bits, and the sign's ones above them. -/
theorem sshr59_toNat (x : BitVec 64) :
    (x.sshiftRight 59).toNat = if 2 ^ 63 ≤ x.toNat then x.toNat / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 else x.toNat / 2 ^ 59 := by
  have hx := x.isLt
  cases hm : x.msb
  · have hu : x.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega_using [this]
    rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ite_eq_right (by omega_using [hu])]
  · have hu : 2 ^ 63 ≤ x.toNat := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega_using [this]
    rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_not, ite_eq_left hu]
    omega_using []

/-- The top five bits of a word, sign-extended, are its arithmetic shift by 59. -/
theorem sext59 (x : BitVec 64) : ((x >>> 59) <<< 59).sshiftRight 59 = x.sshiftRight 59 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have ey : ((x >>> 59) <<< 59).toNat = x.toNat / 2 ^ 59 * 2 ^ 59 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have : x.toNat / 2 ^ 59 < 2 ^ 5 := Nat.div_lt_of_lt_mul (by omega_using [])
    omega_arith
  rw [sshr59_toNat, sshr59_toNat, ey]
  have : x.toNat / 2 ^ 59 * 2 ^ 59 / 2 ^ 59 = x.toNat / 2 ^ 59 := Nat.mul_div_cancel _ (Nat.two_pow_pos 59)
  rw [this]
  have : (2 ^ 63 ≤ x.toNat / 2 ^ 59 * 2 ^ 59) ↔ 2 ^ 63 ≤ x.toNat := by omega_using []
  simp only [this]

/-- `L + M X` modulo `M K`, for `L < M`. -/
theorem mod_split {L M X K : Nat} (hL : L < M) : (L + M * X) % (M * K) = L + M * (X % K) := by
  have e : L + M * X = L + M * (X % K) + M * K * (X / K) := by
    conv_lhs => rw [← Nat.mod_add_div X K]
    rw [Nat.mul_add, Nat.mul_assoc]; omega_using []
  rw [e, Nat.add_mul_mod_self_left]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · apply Nat.mod_eq_of_lt
    have := Nat.mod_lt X hK
    have : M * (X % K) + M ≤ M * K := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega_using [hL, this]

/-- The arithmetic of `shr`: the low words and the top word's arithmetic
shift are `shr_nat`'s `(V + 2 H (2^64 - 1 if V ≥ H)) / 2^59 mod 2 H`. -/
theorem shr_arith64 {L Vlo M : Nat} (x : BitVec 64) (hVlo : Vlo < M)
    (hL : L + M * (x.toNat / 2 ^ 59) = (Vlo + M * x.toNat) / 2 ^ 59) (hLM : L < M) :
    L + M * (x.sshiftRight 59).toNat =
      (Vlo + M * x.toNat + 2 * (M * 2 ^ 63) * (if M * 2 ^ 63 ≤ Vlo + M * x.toNat then 2 ^ 64 - 1 else 0)) /
        2 ^ 59 % (2 * (M * 2 ^ 63)) := by
  have hx := x.isLt
  rw [sshr59_toNat]
  have e2 : 2 * (M * 2 ^ 63) = M * 2 ^ 64 := by rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ac_rfl
  by_cases hneg : 2 ^ 63 ≤ x.toNat
  · have hc : M * 2 ^ 63 ≤ Vlo + M * x.toNat := by
      have := Nat.mul_le_mul_left M hneg; omega_using [this]
    rw [ite_eq_left hneg, ite_eq_left hc, e2]
    have e3 : M * 2 ^ 64 * (2 ^ 64 - 1) = 2 ^ 59 * (M * (2 ^ 5 * (2 ^ 64 - 1))) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl]; ac_rfl
    rw [e3, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 59), ← hL, Nat.add_assoc, ← Nat.mul_add, mod_split hLM]
    have inner : (x.toNat / 2 ^ 59 + 2 ^ 5 * (2 ^ 64 - 1)) % 2 ^ 64 = x.toNat / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 := by
      omega_using []
    rw [inner]
  · have hc : ¬ M * 2 ^ 63 ≤ Vlo + M * x.toNat := by
      have : M * (x.toNat + 1) ≤ M * 2 ^ 63 := Nat.mul_le_mul_left M (by omega_using [hneg])
      rw [Nat.mul_add_one] at this; omega_using [hVlo, this]
    rw [ite_eq_right hneg, ite_eq_right hc, Nat.mul_zero, Nat.add_zero, e2, ← hL, mod_split hLM,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-! ## `mac` -/

/-- The pointers of three arrays, a count and no carry. -/
theorem setup_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n → WP isa (.block cnt) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.t3] t x)
    (ho : o < 2048) (ha : a < 2048) (hb : b < 2048) :
    WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ ([.li .t4 0] : List Instr))) s fun t =>
      Ctx t B Z w N n ∧ t.mem = s.mem ∧ t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧
      t.gpr .t2 = off B (arr w b) ∧ t.gpr .t3 = BitVec.ofNat 64 K ∧ t.gpr .t4 = 0 ∧
      Keep [.t0, .t1, .t2, .t3, .t4] s t := by
  rw [show ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ ([.li .t4 0] : List Instr) =
    VG.Impl.Rsa.RISCV64.Keys.ptrs o a b ++ (cnt ++ ([.li .t4 0] : List Instr)) by
      simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
  refine ptrs_ok h.ws ho ha hb fun t p0 p1 p2 kt mt => ?_
  have ht := h.of_keep (kt.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (hcnt t ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun y => y.gpr .t4 = 0 ∧ y.mem = x.mem) (by brun [fin64_exec_li_zero]; try rfl) (by rfl) (by rfl))
    fun y ⟨⟨y4, ym⟩, ky⟩ => ?_
  have k0 : Keep [.t0, .t1, .t2, .t3, .t4] s y := ((kt.trans kx).trans ky).mono (by decide)
  refine ⟨h.of_keep (k0.mono (by decide)), ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, y4, k0⟩
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p0
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p1
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p2
  · rw [ky.gpr (by decide)]; exact x3

/-- `[o] = [a] + k [b]` (`mac`), `K` words, `k` in `a5`; `o` equal to `a`
and to `b`, or apart from them. -/
theorem mac_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n → WP isa (.block cnt) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.t3] t x)
    (hK1 : 1 ≤ K) (hK : K ≤ w + 1) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) :
    WP isa (mac o a b cnt) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) K + 2 ^ (64 * K) * (t.gpr .t4).toNat =
        wordsVal s.mem B (arr w a) K + (s.gpr .a5).toNat * wordsVal s.mem B (arr w b) K ∧
      t.gpr .t0 = off B (arr w o + 8 * K) ∧ t.gpr .a5 = s.gpr .a5 ∧ t.gpr .a7 = s.gpr .a7 ∧
      Outside B (arr w o) (8 * K) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := arr_al w o
  have := arr_al w a
  have := arr_al w b
  rw [mac, macSetup, WP.seq_iff]
  refine WP.mono (setup_ok h hcnt (by omega_using [ho, hN]) (by omega_using [ha, hN]) (by omega_using [hb, hN])) fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  have k5 : t1.gpr .a5 = s.gpr .a5 := k1.gpr (by decide)
  refine WP.mono (macLoop_ok h1.ws.scr p0 p1 p2 p3 hK1 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_using [this]) (by omega_using [hK, fo, hS]) (by omega_using [hK, fa, hS]) (by omega_using [hK, fb, hS])
    (ahead_any w o a K (by omega_using [hK, hS])) (ahead_any w o b K (by omega_using [hK, hS])))
    fun t2 ⟨qeq, q0, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))
  rw [m1, k5, p4] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega_using [hK, hS]) (by simp), by simpa using qeq, q0, (k2.gpr (by decide)).trans k5,
    (k2.gpr (by decide)).trans (k1.gpr (by decide)), out2, k⟩

/-! ## `mred` -/

/-- An arithmetic shift by 63, unsigned: all ones for a negative word. -/
theorem sshr63_toNat (x : BitVec 64) :
    (x.sshiftRight 63).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  have hx := x.isLt
  cases hm : x.msb
  · have hu : x.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega_using [this]
    rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ite_eq_right (by omega_using [hu])]
    omega_using [hu]
  · have hu : 2 ^ 63 ≤ x.toNat := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega_using [this]
    rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_not, ite_eq_left hu]
    omega_using [hu]

/-- The top half of `ν + 1` words, from the top word's sign. -/
theorem half_top {Wlo A : Nat} (x : Nat) (hW : Wlo < A) :
    (A * 2 ^ 63 ≤ Wlo + A * x) ↔ 2 ^ 63 ≤ x := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hx => ?_
    have : A * (x + 1) ≤ A * 2 ^ 63 := Nat.mul_le_mul_left A hx
    rw [Nat.mul_add_one] at this; omega_using [hW, h, this]
  · intro h; have := Nat.mul_le_mul_left A h; omega_using [this]

/-- The arithmetic of `mred`'s top: `k m` added to the low words (`hmac`),
the carry into word `ν` and the sign and its carry into word `ν + 1` give
`mredRaw_nat`'s `E`. -/
theorem mred_arith64 {L Wlo P k A : Nat} (top c : BitVec 64) (hWlo : Wlo < A) (hL : L < A)
    (hmac : L + A * c.toNat = Wlo + k * P) :
    L + A * (top + c).toNat + A * 2 ^ 64 * (top.sshiftRight 63 + (if top + c < c then (1 : BitVec 64) else 0)).toNat =
      (Wlo + A * top.toNat + A * 2 ^ 64 * (if A * 2 ^ 63 ≤ Wlo + A * top.toNat then 2 ^ 64 - 1 else 0) + k * P) %
        (A * 2 ^ 64 * 2 ^ 64) := by
  have ht := top.isLt; have hc := c.isLt
  have e1 : (top + c).toNat = (top.toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have ecy : (if top + c < c then (1 : BitVec 64) else 0).toNat = (top.toNat + c.toNat) / 2 ^ 64 := by
    by_cases hlt : top + c < c
    · rw [ite_eq_left hlt]; rw [BitVec.lt_def, e1] at hlt; simp; omega_using [hlt]
    · rw [ite_eq_right hlt]; rw [BitVec.lt_def, e1] at hlt; simp; omega_using [hlt]
  simp only [half_top _ hWlo]
  have eT2 : (top.sshiftRight 63 + (if top + c < c then (1 : BitVec 64) else 0)).toNat =
      ((if 2 ^ 63 ≤ top.toNat then 2 ^ 64 - 1 else 0) + (top.toNat + c.toNat) / 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_add, sshr63_toNat, ecy]
  rw [e1, eT2]
  generalize hS : (if 2 ^ 63 ≤ top.toNat then 2 ^ 64 - 1 else 0) = Sv
  have hSv : Sv = 0 ∨ Sv = 2 ^ 64 - 1 := by rw [← hS]; split <;> simp
  have hr : Wlo + A * top.toNat + A * 2 ^ 64 * Sv + k * P = L + A * (top.toNat + c.toNat + 2 ^ 64 * Sv) := by
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]; omega_using [hmac]
  have inner : (top.toNat + c.toNat) % 2 ^ 64 + 2 ^ 64 * ((Sv + (top.toNat + c.toNat) / 2 ^ 64) % 2 ^ 64) =
      (top.toNat + c.toNat + 2 ^ 64 * Sv) % (2 ^ 64 * 2 ^ 64) := by
    rcases hSv with h | h <;> subst h <;> omega_using []
  rw [hr, Nat.mul_assoc A (2 ^ 64) (2 ^ 64), mod_split hL, ← inner, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- `ptr r j` at the head of a block, run: `r` holds the address of array `j`. -/
theorem runBlock_ptr (B : Addr) (w : Nat) {s : State} {r : Reg} {j : Nat} (rest : List Instr)
    (h10 : s.gpr .s10 = BitVec.ofNat 64 (S w)) (h11 : s.gpr .s11 = B) (hr10 : r ≠ .s10) (hr11 : r ≠ .s11)
    (hj : j < 2048) :
    runBlock isa (ptr r j ++ rest) s = runBlock isa rest (s.write r (off B (arr w j))) := by
  simp only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, exec_li_nat hj, exec_mul,
    exec_add, exec_addi_nat (show hdr < 2048 by decide), gpr_write, ite_true, Ne.symm hr10, Ne.symm hr11,
    ite_false, write_write, h10, h11, ptr_val]

theorem ofNat_shl3 {k : Nat} (h : 8 * k < 2 ^ 64) : BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [h])]
  omega_using [h]

/-! ## The passes' blocks -/

/-- The registers `passSetup` writes. -/
abbrev setupRegs : List Reg := [.a5, .a7, .s1, .s2, .s3, .s4, .s5, .t0, .t1, .t4, .a4, .a0, .a1]

/-- `passSetup a b`: the matrix from the window, three of its masks, the
pointers at arrays `a` and `b`, and the accumulators zero. -/
theorem passSetup_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {a b : Nat}
    (ha : a < 2048) (hb : b < 2048) :
    WP isa (.block (passSetup a b)) s fun t => Ctx t B Z w N n ∧ t.mem = s.mem ∧
      t.gpr .a5 = s.mem.readW (off B (arr w aW + wU)) 64 ∧ t.gpr .a7 = s.mem.readW (off B (arr w aW + wV)) 64 ∧
      t.gpr .s1 = s.mem.readW (off B (arr w aW + wQ)) 64 ∧ t.gpr .s2 = s.mem.readW (off B (arr w aW + wR)) 64 ∧
      t.gpr .s3 = (t.gpr .a5).sshiftRight 63 ∧ t.gpr .s4 = (t.gpr .a7).sshiftRight 63 ∧
      t.gpr .s5 = (t.gpr .s1).sshiftRight 63 ∧
      t.gpr .t0 = off B (arr w a) ∧ t.gpr .t1 = off B (arr w b) ∧
      t.gpr .t4 = 0 ∧ t.gpr .a4 = 0 ∧ t.gpr .a0 = 0 ∧ t.gpr .a1 = 0 ∧ Keep setupRegs s t := by
  rw [passSetup, ldMat]
  simp only [List.append_assoc]
  refine ldW_ok h (by decide) (by decide) (by decide) (by decide) ?_
  have h1 := h.of_keep' (Keep.write s .a5 (s.mem.readW (off B (arr w aW + wU)) 64))
  refine ldW_ok h1 (by decide) (by decide) (by decide) (by decide) ?_
  have h2 := h1.of_keep' (Keep.write _ .a7 (s.mem.readW (off B (arr w aW + wV)) 64))
  refine ldW_ok h2 (by decide) (by decide) (by decide) (by decide) ?_
  have h3 := h2.of_keep' (Keep.write _ .s1 (s.mem.readW (off B (arr w aW + wQ)) 64))
  refine ldW_ok h3 (by decide) (by decide) (by decide) (by decide) ?_
  have h4 := h3.of_keep' (Keep.write _ .s2 (s.mem.readW (off B (arr w aW + wR)) 64))
  simp only [mem_write] at h1 h2 h3 h4 ⊢
  refine WP.mono (WP.keep [.s3, .s4, .s5, .t0, .t1, .t4, .a4, .a0, .a1] (Q := fun t =>
      t.gpr .s3 = (s.mem.readW (off B (arr w aW + wU)) 64).sshiftRight 63 ∧
      t.gpr .s4 = (s.mem.readW (off B (arr w aW + wV)) 64).sshiftRight 63 ∧
      t.gpr .s5 = (s.mem.readW (off B (arr w aW + wQ)) 64).sshiftRight 63 ∧
      t.gpr .t0 = off B (arr w a) ∧ t.gpr .t1 = off B (arr w b) ∧
      t.gpr .t4 = 0 ∧ t.gpr .a4 = 0 ∧ t.gpr .a0 = 0 ∧ t.gpr .a1 = 0 ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨t3, t4', t5, t0, t1, z4, za4, za0, za1, tm⟩, kt⟩ => ?_
  · brun [runBlock_ptr B w, h.ws.s10, h.ws.s11, ha, hb, fin64_exec_li_zero, mem_write]
    all_goals rfl
  have k0 : Keep setupRegs s t :=
    ((((((Keep.write s .a5 _).trans (Keep.write _ .a7 _)).trans (Keep.write _ .s1 _)).trans
      (Keep.write _ .s2 _)).trans kt).mono (by decide))
  have g : ∀ r, r ∉ [Reg.s3, .s4, .s5, .t0, .t1, .t4, .a4, .a0, .a1] → t.gpr r = _ := fun r hr => kt.gpr hr
  refine ⟨h.of_keep' k0, tm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, t0, t1, z4, za4, za0, za1, k0⟩
  · rw [g _ (by decide)]; simp [gpr_write]
  · rw [g _ (by decide)]; simp [gpr_write]
  · rw [g _ (by decide)]; simp [gpr_write]
  · rw [g _ (by decide)]; simp [gpr_write]
  · rw [t3, g .a5 (by decide)]; simp [gpr_write]
  · rw [t4', g .a7 (by decide)]; simp [gpr_write]
  · rw [t5, g .s1 (by decide)]; simp [gpr_write]

/-- Word 0 of the pass over `f` and `g` (at `dF`, `dG`): `r`'s mask, both
accumulators' terms, and their low words' top bits. -/
theorem fgFirst_ok {t : State} {B : Addr} {Z dF dG : Nat} (hs : Scr t B Z)
    (p0 : t.gpr .t0 = off B dF) (p1 : t.gpr .t1 = off B dG) (hF : dF + 8 ≤ Z) (hG : dG + 8 ≤ Z)
    (hF8 : dF % 8 = 0) (hG8 : dG % 8 = 0)
    (m3 : t.gpr .s3 = (t.gpr .a5).sshiftRight 63) (m4 : t.gpr .s4 = (t.gpr .a7).sshiftRight 63)
    (m5 : t.gpr .s5 = (t.gpr .s1).sshiftRight 63) :
    WP isa (.block (([.shift .sra .d .s6 .s2 63] : List Instr) ++ fgHead 0 ++ fgShift)) t fun u =>
      let x := word t.mem B dF
      let y := word t.mem B dG
      (u.gpr .s6 = (t.gpr .s2).sshiftRight 63 ∧
        u.gpr .t4 = hi2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4) (t.gpr .a4) ∧
        u.gpr .a4 = (hi2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4) (t.gpr .a4)).sshiftRight 63 ∧
        u.gpr .a2 = lo2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4) >>> 59 ∧
        u.gpr .a0 = hi2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0) (t.gpr .a1) ∧
        u.gpr .a1 = (hi2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0) (t.gpr .a1)).sshiftRight 63 ∧
        u.gpr .a3 = lo2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0) >>> 59 ∧ u.mem = t.mem) ∧
      Keep [.s6, .t2, .t4, .t5, .t6, .a4, .a0, .a1, .a2, .a3] t u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [fgHead, fgShift, term, hi2, lo2, BitVec.add_zero, p0, p1, m3, m4, m5, off_add,
    hs.ld (show dF + 8 ≤ Z by omega_using [hF]), hs.ld (show dG + 8 ≤ Z by omega_using [hG]),
    hs.al8 (show dF + 8 ≤ Z by omega_using [hF]) (by omega_using [hF8]), hs.al8 (show dG + 8 ≤ Z by omega_using [hG]) (by omega_using [hG8])]
  all_goals done

/-- The top words of the new `f` and `g`: the last five bits, sign-extended. -/
theorem fgTop_ok {t : State} {B : Addr} {Z dF dG : Nat} (hs : Scr t B Z)
    (p0 : t.gpr .t0 = off B dF) (p1 : t.gpr .t1 = off B dG) (hF : dF + 8 ≤ Z) (hG : dG + 8 ≤ Z)
    (hF8 : dF % 8 = 0) (hG8 : dG % 8 = 0) :
    WP isa (.block fgTop) t fun u =>
      u.mem = (t.mem.writeW (off B dF) ((t.gpr .a2 <<< 59).sshiftRight 59)).writeW (off B dG)
        ((t.gpr .a3 <<< 59).sshiftRight 59) ∧ Keep [.t2] t u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [fgTop, p0, p1, hs.st (show dF + 8 ≤ Z by omega_using [hF]), hs.st (show dG + 8 ≤ Z by omega_using [hG]),
    hs.al8 (show dF + 8 ≤ Z by omega_using [hF]) (by omega_using [hF8]), hs.al8 (show dG + 8 ≤ Z by omega_using [hG]) (by omega_using [hG8])]

/-- Word 0 of the pass over `a` and `b` (at `dA`, `dB`, `m` at `dM`): both
accumulators' terms, `k₁ = t₀ iv` and `k₂`, and `k m₀` added with no
carry. -/
theorem abFirst_ok {t : State} {B : Addr} {Z w N n dA dB dM : Nat} (h : Ctx t B Z w N n)
    (p0 : t.gpr .t0 = off B dA) (p1 : t.gpr .t1 = off B dB) (p2 : t.gpr .t2 = off B dM)
    (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z)
    (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (m3 : t.gpr .s3 = (t.gpr .a5).sshiftRight 63) (m4 : t.gpr .s4 = (t.gpr .a7).sshiftRight 63)
    (m5 : t.gpr .s5 = (t.gpr .s1).sshiftRight 63) :
    WP isa (.block abFirst) t fun u =>
      let x := word t.mem B dA
      let y := word t.mem B dB
      let mw := word t.mem B dM
      let iv := t.mem.readW (off B (arr w aW + wIv)) 64
      let l1 := lo2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4)
      let l2 := lo2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0)
      (u.gpr .a2 = l1 * iv ∧ u.gpr .a3 = l2 * iv ∧
        u.gpr .t4 = hi2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4) (t.gpr .a4) ∧
        u.gpr .a4 = (hi2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4) (t.gpr .a4)).sshiftRight 63 ∧
        u.gpr .a6 = macC (l1 * iv) mw l1 (t.gpr .a6) ∧
        u.gpr .a0 = hi2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0) (t.gpr .a1) ∧
        u.gpr .a1 = (hi2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0) (t.gpr .a1)).sshiftRight 63 ∧
        u.gpr .s0 = macC (l2 * iv) mw l2 (t.gpr .s0) ∧ u.mem = t.mem) ∧
      Keep [.a2, .a3, .t4, .t5, .t6, .a4, .a0, .a1, .a6, .s0, .s6] t u := by
  have hs := h.ws.scr
  have fW := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega_using [this])
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have := arr_al w aW
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [abFirst, abHead, termR, macW, abShift, term, hi2, lo2, macS, macC, ldW, word, BitVec.add_zero, List.append_assoc,
    runBlock_ptr B w, h.ws.s10, h.ws.s11, (show aW < 2048 by decide), wIv, p0, p1, p2, m3, m4, m5, off_add,
    hs.ld (show dA + 8 ≤ Z by omega_using [hA]), hs.ld (show dB + 8 ≤ Z by omega_using [hB]),
    hs.ld (show dM + 8 ≤ Z by omega_using [hM]), hs.ld (show arr w aW + 40 + 8 ≤ Z by omega_arith),
    hs.al8 (show dA + 8 ≤ Z by omega_using [hA]) (by omega_using [hA8]), hs.al8 (show dB + 8 ≤ Z by omega_using [hB]) (by omega_using [hB8]),
    hs.al8 (show dM + 8 ≤ Z by omega_using [hM]) (by omega_using [hM8]), hs.al8 (show arr w aW + 40 + 8 ≤ Z by omega_arith) (by omega_using [this])]
  all_goals first | done | exact ⟨rfl, rfl⟩

/-- Word `ν` of the pass over `a` and `b` (pointers at word `ν - 1`, at
`dA`, `dB`): both accumulators' terms; the low words with the carries are
words `ν - 1`, and the low words' signs with the carries out words `ν`. -/
theorem abLast_ok {t : State} {B : Addr} {Z dA dB : Nat} (hs : Scr t B Z)
    (p0 : t.gpr .t0 = off B dA) (p1 : t.gpr .t1 = off B dB) (hA : dA + 16 ≤ Z) (hB : dB + 16 ≤ Z)
    (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0)
    (m3 : t.gpr .s3 = (t.gpr .a5).sshiftRight 63) (m4 : t.gpr .s4 = (t.gpr .a7).sshiftRight 63)
    (m5 : t.gpr .s5 = (t.gpr .s1).sshiftRight 63) :
    WP isa (.block abLast) t fun u =>
      let x := word t.mem B (dA + 8)
      let y := word t.mem B (dB + 8)
      let l1 := lo2 (t.gpr .a5) (t.gpr .a7) x y (t.gpr .t4)
      let l2 := lo2 (t.gpr .s1) (t.gpr .s2) x y (t.gpr .a0)
      u.mem = (((t.mem.writeW (off B dA) (l1 + t.gpr .a6)).writeW (off B (dA + 8))
          (l1.sshiftRight 63 + (if l1 + t.gpr .a6 < t.gpr .a6 then (1 : BitVec 64) else 0))).writeW (off B dB)
          (l2 + t.gpr .s0)).writeW (off B (dB + 8))
          (l2.sshiftRight 63 + (if l2 + t.gpr .s0 < t.gpr .s0 then (1 : BitVec 64) else 0)) ∧
      Keep [.t4, .t5, .t6, .a4, .a0, .a1, .s6] t u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [abLast, abHead, termR, term, hi2, lo2, p0, p1, m3, m4, m5, off_add,
    hs.ld (show dA + 8 + 8 ≤ Z by omega_using [hA]), hs.ld (show dB + 8 + 8 ≤ Z by omega_using [hB]),
    hs.st (show dA + 8 ≤ Z by omega_using [hA]), hs.st (show dB + 8 ≤ Z by omega_using [hB]),
    hs.st (show dA + 8 + 8 ≤ Z by omega_using [hA]), hs.st (show dB + 8 + 8 ≤ Z by omega_using [hB]),
    hs.al8 (show dA + 8 + 8 ≤ Z by omega_using [hA]) (by omega_using [hA8]), hs.al8 (show dB + 8 + 8 ≤ Z by omega_using [hB]) (by omega_using [hB8]),
    hs.al8 (show dA + 8 ≤ Z by omega_using [hA]) (by omega_using [hA8]), hs.al8 (show dB + 8 ≤ Z by omega_using [hB]) (by omega_using [hB8])]
  all_goals done

/-- The end of the pass over `f` and `g`: the stored words with the top
word are `shr_nat`'s shift of the low words `V ≡ u F + v G`. -/
theorem fg_end {u v : Int} {F G k R : Nat} {lo hi prev : BitVec 64} (h : FGAcc u v F G k R lo hi prev)
    (hR : R < 2 ^ (64 * k)) :
    ∃ V : Nat, V < 2 ^ (64 * (k + 1)) ∧ (V : Int) % 2 ^ (64 * (k + 1)) = (u * F + v * G) % 2 ^ (64 * (k + 1)) ∧
      R + 2 ^ (64 * k) * ((prev <<< 59).sshiftRight 59).toNat =
        (V + 2 * (2 ^ (64 * k) * 2 ^ 63) * (if 2 ^ (64 * k) * 2 ^ 63 ≤ V then 2 ^ 64 - 1 else 0)) / 2 ^ 59 %
          (2 * (2 ^ (64 * k) * 2 ^ 63)) := by
  obtain ⟨A, last, hA, hp, hlin, hshr, -, -⟩ := h
  have hl := last.isLt
  refine ⟨A + 2 ^ (64 * k) * last.toNat, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * k)) (show last.toNat + 1 ≤ 2 ^ 64 by omega_using [])
    rw [Nat.mul_add_one] at this
    rw [Nat.mul_succ, Nat.pow_add]; omega_using [hA, this]
  · rw [← hlin, Int.add_mul_emod_self_left]
  · rw [hp, sext59]
    exact shr_arith64 last hA hshr hR

/-- The end of the pass over `a` and `b`, at word `n + 1 = ν` where `m`'s is
zero: the stored words with the last two are `mredRaw_nat`'s `E / 2^64` for
the low words `W ≡ u Da + v Db`. -/
theorem ab_end {c1 c2 : BitVec 64} {k w0 Da Db P n R : Nat} {lo hi c : BitVec 64} (x y : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (h : ABAcc c1.toInt c2.toInt k w0 Da Db P n R lo hi c) (hR : R < 2 ^ (64 * n)) :
    ∃ W : Nat, W < 2 ^ (64 * (n + 2)) ∧ W % 2 ^ 64 = w0 ∧
      (W : Int) % 2 ^ (64 * (n + 2)) = (c1.toInt * ((Da + 2 ^ (64 * (n + 1)) * x.toNat : Nat) : Int) +
        c2.toInt * ((Db + 2 ^ (64 * (n + 1)) * y.toNat : Nat) : Int)) % 2 ^ (64 * (n + 2)) ∧
      R + 2 ^ (64 * n) * (lo2 c1 c2 x y lo + c).toNat + 2 ^ (64 * (n + 1)) *
          ((lo2 c1 c2 x y lo).sshiftRight 63 + (if lo2 c1 c2 x y lo + c < c then (1 : BitVec 64) else 0)).toNat =
        (W + 2 ^ (64 * (n + 1)) * 2 ^ 64 * (if 2 ^ (64 * (n + 1)) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) + k * P) %
          (2 ^ (64 * (n + 1)) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64 := by
  obtain ⟨A, hA, hw0, hlin, hmac, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have hl := (lo2 c1 c2 x y lo).isLt
  have eM : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
  refine ⟨A + 2 ^ (64 * (n + 1)) * (lo2 c1 c2 x y lo).toNat, ?_, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) (show (lo2 c1 c2 x y lo).toNat + 1 ≤ 2 ^ 64 by omega_using [])
    rw [Nat.mul_add_one] at this
    rw [show 64 * (n + 2) = 64 * (n + 1) + 64 by omega_using [], Nat.pow_add]; omega_using [hA, this]
  · rw [eM, Nat.mul_assoc, Nat.add_mul_mod_self_left]; exact hw0
  · have := lin_inv_step (u := c1.toInt) (v := c2.toInt) (S0 := 0) (W := A) (by rw [Int.add_zero]; exact hlin) e
    rw [Int.add_zero, show 64 * (n + 1) + 64 = 64 * (n + 2) by omega_using []] at this
    rw [← this, Int.add_mul_emod_self_left]
  · have m := mred_arith64 (L := 2 ^ 64 * R) (Wlo := A) (P := P) (k := k) (A := 2 ^ (64 * (n + 1)))
      (lo2 c1 c2 x y lo) c hA (by rw [eM]; exact Nat.mul_lt_mul_of_pos_left hR (Nat.two_pow_pos 64))
      (by rw [eM, Nat.mul_assoc, ← Nat.mul_add]; exact hmac)
    rw [← m, eM]
    have : 2 ^ 64 * R + 2 ^ 64 * 2 ^ (64 * n) * (lo2 c1 c2 x y lo + c).toNat +
        2 ^ 64 * 2 ^ (64 * n) * 2 ^ 64 *
          ((lo2 c1 c2 x y lo).sshiftRight 63 + (if lo2 c1 c2 x y lo + c < c then (1 : BitVec 64) else 0)).toNat =
        2 ^ 64 * (R + 2 ^ (64 * n) * (lo2 c1 c2 x y lo + c).toNat + 2 ^ 64 * 2 ^ (64 * n) *
          ((lo2 c1 c2 x y lo).sshiftRight 63 + (if lo2 c1 c2 x y lo + c < c then (1 : BitVec 64) else 0)).toNat) := by
      rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [this, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)]

/-! ## `csub` -/

/-- The mask `0 - y` of a borrow `y`. -/
theorem mask_of_borrow (y : BitVec 64) (hy : y.toNat ≤ 1) :
    BitVec.ofNat 64 0 - y = if decide (y.toNat = 1) then BitVec.allOnes 64 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with e | e
  · have : y = 0#64 := BitVec.eq_of_toNat_eq e
    subst this; rfl
  · have : y = 1#64 := BitVec.eq_of_toNat_eq e
    subst this; rfl

/-- `[o] = [x] - m` where it does not borrow, else `[x]` (`csub`), `ν + 1`
words, through `[sc]`. -/
theorem csub_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o x sc : Nat}
    (ho : o < N) (hx : x < N) (hsc : sc < N) (hN : N ≤ 256) (hsx : sc ≠ x)
    (hsm : sc ≠ aMz) (hos : o ≠ sc) {p X : Nat} (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p)
    (hX : wordsVal s.mem B (arr w x) (nu n + 1) = X) :
    WP isa (csub o x sc) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o, sc] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (nu n + 1) = (if p ≤ X then X - p else X) ∧ Keep kRegs s t := by
  have hm : aMz < N := by have := h.room; unfold aMz; omega_using [this]
  have fo := h.ws.arr_fit ho
  have fx := h.ws.arr_fit hx
  have fs := h.ws.arr_fit hsc
  have fm := h.ws.arr_fit hm
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have := arr_al w o
  have := arr_al w x
  have := arr_al w sc
  have := arr_al w aMz
  rw [csub]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by omega_using [hsc, hN]) (by omega_using [hx, hN]) (by omega_using [hN, hm]))
    fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (Loops.subLoop_ok h1.ws.scr p0 p1 p2 p3 (by rw [p4]; decide)
    (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_using [this]) (by omega_arith) (by omega_arith) (by omega_arith)
    (ahead_k hsx (by omega_arith)) (ahead_k hsm (by omega_arith)))
    fun t2 ⟨b4, veq, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  rw [m1, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [m1] at out2
  rw [WP.seq_iff]
  -- The mask of the borrow.
  have hb2 : WP isa (.block (ptr .t0 o ++ ptr .t1 sc ++ ptr .t2 x ++ cntN1 ++
      ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr))) t2 fun t => Ctx t B Z w N n ∧ t.mem = t2.mem ∧
      t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w sc) ∧ t.gpr .t2 = off B (arr w x) ∧
      t.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧ t.gpr .t4 = BitVec.ofNat 64 0 - t2.gpr .t4 ∧ Keep kRegs t2 t := by
    rw [show ptr .t0 o ++ ptr .t1 sc ++ ptr .t2 x ++ cntN1 ++ ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr) =
      VG.Impl.Rsa.RISCV64.Keys.ptrs o sc x ++ (cntN1 ++ ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr)) by
        simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
    refine ptrs_ok h2.ws (by omega_using [ho, hN]) (by omega_using [hsc, hN]) (by omega_using [hx, hN]) fun t q0 q1 q2 kt mt => ?_
    have ht := h2.of_keep (kt.mono (by decide))
    rw [WP.block_append_iff]
    refine WP.mono (cntN1_ok ht) fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
    have y4 : y.gpr .t4 = t2.gpr .t4 := (ky.gpr (by decide)).trans (kt.gpr (by decide))
    refine WP.mono (WP.keep [.t5, .t4] (Q := fun z => z.gpr .t4 = BitVec.ofNat 64 0 - t2.gpr .t4 ∧ z.mem = y.mem)
      (by brun [y4, fin64_exec_li_zero]; try rfl) (by rfl) (by rfl)) fun z ⟨⟨z4, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs t2 z := ((kt.trans ky).trans kz).mono (by decide)
    refine ⟨h2.of_keep k0, zm.trans (ym.trans mt), ?_, ?_, ?_, ?_, z4, k0⟩
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q0
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q1
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q2
    · rw [kz.gpr (by decide)]; exact y3
  refine WP.mono hb2 fun t3 ⟨h3, m3, r0, r1, r2, r3, r4, k3⟩ => ?_
  refine WP.mono (Loops.selLoop_ok (b := decide ((t2.gpr .t4).toNat = 1)) h3.ws.scr
    r0 r1 r2 r3 (by rw [r4]; exact mask_of_borrow _ b4) (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (ahead_k hos (by omega_arith)) (ahead_any w o x (nu n + 1) (by omega_arith))) fun t4 ⟨seq, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 :=
    Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))) k3) (k4.mono (by decide))
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · rw [m3] at out4
    exact (Keys.Frame.of_arr (o := sc) (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega_arith)
      (by simp)).trans (Keys.Frame.of_arr (o := o) (d := 0) (by simpa only [Nat.add_zero] using out4)
        (by omega_arith) (by simp))
  · have vx : wordsVal t2.mem B (arr w x) (nu n + 1) = X := by
      rw [out2.wordsVal (by have := arr_disj (w := w) hsx; omega_arith) (by omega_arith)]; exact hX
    rw [seq, m3, vx]
    have hpR := wordsVal_lt s.mem B (arr w aMz) (nu n + 1)
    have hXR := wordsVal_lt s.mem B (arr w x) (nu n + 1)
    have hSR := wordsVal_lt t2.mem B (arr w sc) (nu n + 1)
    rw [hp] at hpR veq
    rw [hX] at hXR veq
    generalize 2 ^ (64 * (nu n + 1)) = R at hpR hXR hSR veq
    by_cases e : (t2.gpr .t4).toNat = 1
    · rw [e] at veq; simp only [e, decide_true, ↓reduceIte]
      have : ¬ p ≤ X := by omega_using [hSR, veq]
      simp only [this, ↓reduceIte]
    · have e0 : (t2.gpr .t4).toNat = 0 := by omega_using [b4, e]
      rw [e0] at veq; simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      have : p ≤ X := by omega_using [veq]
      simp only [this, ↓reduceIte]; omega_using [veq]

/-! ## Selection by a sign -/

theorem sshr63_mask (x : BitVec 64) :
    x.sshiftRight 63 = if decide (2 ^ 63 ≤ x.toNat) then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [sshr63_toNat]
  by_cases hx : 2 ^ 63 ≤ x.toNat
  · rw [ite_eq_left hx, decide_eq_true hx]; simp
  · rw [ite_eq_right hx, decide_eq_false hx]; rfl

/-- `signOf j`: the mask of `[j]`'s sign, its word `ν`'s top bit, into `t4`. -/
theorem signOf_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) {j : Nat} (hj : j < N)
    (hN : N ≤ 256) :
    WP isa (.block (signOf j)) t fun u => (u.mem = t.mem ∧
      u.gpr .t4 = if decide (2 ^ 63 ≤ (word t.mem B (arr w j + 8 * nu n)).toNat) then BitVec.allOnes 64 else 0) ∧
      Keep [.t1, .t3, .t4] t u := by
  have fj := h.ws.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nw
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have := arr_al w j
  have hs := h.ws.scr
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [signOf, topOf, cntN, List.append_assoc, runBlock_ptr B w, (show j < 2048 by omega_using [hj, hN]), h.ws.s10, h.ws.s11,
    h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega_arith), ofNat_shl3 (show 8 * nu n < 2 ^ 64 by omega_arith),
    off_add, hs.ld (show arr w j + 8 * nu n + 8 ≤ Z by omega_arith),
    hs.al8 (show arr w j + 8 * nu n + 8 ≤ Z by omega_arith) (by omega_using [this]), sshr63_mask]

/-- `[o] := [b]` if `[j] < 0` (its word `ν`'s top bit), else `[a]`, `ν + 1` words (`signSel`). -/
theorem signSel_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {j o a b : Nat}
    (hj : j < N) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (signSel j o a b) s
      fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
        wordsVal t.mem B (arr w o) (nu n + 1) =
          (if 2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat then wordsVal s.mem B (arr w b) (nu n + 1)
            else wordsVal s.mem B (arr w a) (nu n + 1)) ∧
        Outside B (arr w o) (8 * (nu n + 1)) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have := arr_al w o
  have := arr_al w a
  have := arr_al w b
  rw [signSel, WP.seq_iff, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (signOf_ok h hj hN) fun t1 ⟨⟨m1, r4⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [← List.append_assoc, ← List.append_assoc]
  refine ptrs_ok h1.ws (by omega_using [ho, hN]) (by omega_using [ha, hN]) (by omega_using [hb, hN]) fun t2 p0 p1 p2 k2 m2 => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (cntN1_ok h2) fun t3 ⟨⟨p3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have q4 : t3.gpr .t4 = t1.gpr .t4 := (k3.gpr (by decide)).trans (k2.gpr (by decide))
  refine WP.mono (Loops.selLoop_ok (b := decide (2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat)) h3.ws.scr
    (by rw [k3.gpr (by decide)]; exact p0) (by rw [k3.gpr (by decide)]; exact p1)
    (by rw [k3.gpr (by decide)]; exact p2) p3 (by rw [q4, r4]) (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_using [this]) (by omega_arith) (by omega_arith) (by omega_arith) (ahead_any w o a (nu n + 1) (by omega_arith)) (ahead_k hob (by omega_arith)))
    fun t4 ⟨v4, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide)))
    (k3.mono (by decide))) (k4.mono (by decide))
  rw [m3, m2, m1] at v4 out4
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega_arith)
    (by simp), ?_, out4, k⟩
  rw [v4]
  simp only [decide_eq_true_eq]

/-! ## Zeroing -/

/-- `zeroW j`: `[j]`'s `w + 1` words zeroed. -/
theorem zeroW_ok {s : State} {B : Addr} {Z w N n j : Nat} (h : Ctx s B Z w N n) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (8 * (w + 1)) s.mem t.mem ∧ wordsVal t.mem B (arr w j) (w + 1) = 0 ∧
      Keep kRegs s t := by
  have fj := h.ws.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := arr_al w j
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h.ws (by decide) (by decide) (by omega_using [hj, hN]) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.ws.s9, ofNat_succ]
  have k1 : Keep kRegs s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep kRegs s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (Loops.zeroLoop_ok (dO := arr w j) (n := w + 1) (h.of_keep k2).ws.scr (by rw [ky.gpr (by decide)]; exact u0)
    (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega_using []) (by omega_arith) (by omega_using [this]) (by omega_using [fj, hS])) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  exact ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Keys.Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega_using [hS]) (by simp), out, z, Keep.trans' k2 (kt.mono (by decide))⟩

end VG.Proof.Rsa.RISCV64.InvBatch
