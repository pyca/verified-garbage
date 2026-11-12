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
`s8`: `lin_ok` (`[o] ≡ u [a] + v [b]` modulo `2^(64 (ν + 1))`), `shr_ok`
(`[o] = [a] / 2^59`, as `Proof/Divstep/Tc.lean`'s `shr_nat` reads it),
`mac_ok` (`[o] = [a] + k [b]`).
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

/-- The words the inverse works on, `⌈n / 2⌉`. -/
abbrev nu (n : Nat) : Nat := (n + 1) / 2

theorem Ctx.nu1 {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) : 1 ≤ nu n := by
  have := h.npos; unfold nu; omega

theorem Ctx.nuw {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) : nu n ≤ w := by
  have := h.nw; unfold nu; omega

/-- `n` digits fit in `ν` words. -/
theorem pow_nu (n : Nat) : 2 ^ (32 * n) ≤ 2 ^ (64 * nu n) :=
  Nat.pow_le_pow_right (by decide) (by unfold nu; omega)

/-! ## Blocks -/

/-- `ldW r o`: `r` := the window's 64-bit word at `o`. -/
theorem ldW_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {r : Reg}
    (h10 : r ≠ .s10) (h11 : r ≠ .s11) {o : Nat} (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (off B (arr w aW + o)) 64)) Q) :
    WP isa (.block (ldW r o ++ rest)) s Q := by
  have fit := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega)
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  rw [ldW, List.append_assoc]
  refine ptr_ok h.ws h10 h11 (by decide) ?_
  rw [WP.block_append_iff]
  have hs := h.ws.scr
  have hl : InRegions ((s.write r (off B (arr w aW))).rd ++ (s.write r (off B (arr w aW))).wr)
      ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o) 8 := by
    simp only [gpr_write, ↓reduceIte, rd_write, wr_write, off_add]
    exact hs.ld (d := arr w aW + o) (n := 8) (by omega)
  have ha : ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o).toNat % 8 = 0 := by
    simp only [gpr_write, ↓reduceIte, off_add]
    exact hs.al8 (by omega) (by have := arr_al w aW; omega)
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (by omega) ha hl,
    gpr_write, ↓reduceIte, off_add, mem_write, Option.some.injEq, exists_eq_left', write_write]
  exact k

/-- Arrays apart are each ahead of the other, for `k` words (`8 k ≤ S w`). -/
theorem ahead_k {w o a k : Nat} (h : o ≠ a) (hk : 8 * k ≤ S w) : Ahead (arr w o) (arr w a) k := by
  have := arr_disj (w := w) h
  unfold Ahead; omega

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
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-! ## Counts -/

theorem cntN_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN) t fun x => (x.gpr .t3 = BitVec.ofNat 64 (nu n) ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  have := h.nw; have := h.ws.wle
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN, h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega)]

theorem cntN1_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN1) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  have := h.nw; have := h.ws.wle
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN1, cntN, h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega)]

/-! ## `lin` -/

/-- The setup of `lin`: the pointers, the coefficients, the count and no accumulator. -/
theorem linSetup_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {c1 c2 o a b : Nat}
    (ho : o < 2048) (ha : a < 2048) (hb : b < 2048)
    (hc1 : c1 + 8 ≤ 48) (hc1' : c1 % 8 = 0) (hc2 : c2 + 8 ≤ 48) (hc2' : c2 % 8 = 0) :
    WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ ldW .a5 c1 ++ ldW .a7 c2 ++ cntN1 ++
      ([.li .t4 0, .li .a4 0] : List Instr))) s fun t => Ctx t B Z w N n ∧ t.mem = s.mem ∧
      t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧ t.gpr .t2 = off B (arr w b) ∧
      t.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧ t.gpr .t4 = 0 ∧ t.gpr .a4 = 0 ∧
      t.gpr .a5 = s.mem.readW (off B (arr w aW + c1)) 64 ∧
      t.gpr .a7 = s.mem.readW (off B (arr w aW + c2)) 64 ∧ Keep kRegs s t := by
  rw [show ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ ldW .a5 c1 ++ ldW .a7 c2 ++ cntN1 ++
    ([.li .t4 0, .li .a4 0] : List Instr) = VG.Impl.Rsa.RISCV64.Keys.ptrs o a b ++
      (ldW .a5 c1 ++ (ldW .a7 c2 ++ (cntN1 ++ ([.li .t4 0, .li .a4 0] : List Instr)))) by
        simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
  refine ptrs_ok h.ws ho ha hb fun t p0 p1 p2 kt mt => ?_
  have ht := h.of_keep (kt.mono (by decide))
  refine ldW_ok ht (by decide) (by decide) hc1 hc1' ?_
  refine ldW_ok (ht.of_keep ((Keep.write _ .a5 _).mono (rs' := kRegs) (by decide))) (by decide) (by decide)
    hc2 hc2' ?_
  rw [WP.block_append_iff]
  refine WP.mono (cntN1_ok (ht.of_keep (((Keep.write _ .a5 _).trans (Keep.write _ .a7 _)).mono
    (rs' := kRegs) (by decide)))) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.t4, .a4] (Q := fun y => y.gpr .t4 = 0 ∧ y.gpr .a4 = 0 ∧ y.mem = x.mem)
    (by brun [fin64_exec_li_zero]; try rfl) (by rfl) (by rfl)) fun y ⟨⟨y4, ya, ym⟩, ky⟩ => ?_
  have k0 : Keep kRegs s y :=
    ((((kt.trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans kx).trans ky).mono (by decide)
  refine ⟨h.of_keep k0, ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, y4, ya, ?_, ?_, k0⟩
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p0
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p1
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p2
  · rw [ky.gpr (by decide)]; exact x3
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte, mt]
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, ↓reduceIte, mem_write, mt]

/-- `[o] ≡ c₁ [a] + c₂ [b]` modulo `2^(64 (ν + 1))` (`lin`), the coefficients
`u`, `v` of at most `2^61` the window's words at `c₁`, `c₂`. -/
theorem lin_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {c1 c2 o a b : Nat}
    {u v : Int} (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hc1 : c1 + 8 ≤ 48) (hc1' : c1 % 8 = 0) (hc2 : c2 + 8 ≤ 48) (hc2' : c2 % 8 = 0)
    (hu : s.mem.readW (off B (arr w aW + c1)) 64 = BitVec.ofInt 64 u)
    (hv : s.mem.readW (off B (arr w aW + c2)) 64 = BitVec.ofInt 64 v)
    (hu1 : u.natAbs ≤ 2 ^ 61) (hv1 : v.natAbs ≤ 2 ^ 61) :
    WP isa (lin c1 c2 o a b) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w o) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        (u * wordsVal s.mem B (arr w a) (nu n + 1) + v * wordsVal s.mem B (arr w b) (nu n + 1)) %
          2 ^ (64 * (nu n + 1)) ∧
      Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have := arr_al w o
  have := arr_al w a
  have := arr_al w b
  have tu : (BitVec.ofInt 64 u).toInt = u := BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  have tv : (BitVec.ofInt 64 v).toInt = v := BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  rw [lin, WP.seq_iff]
  refine WP.mono (linSetup_ok h (by omega) (by omega) (by omega) hc1 hc1' hc2 hc2')
    fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, pa, p5, p7, k1⟩ => ?_
  rw [hu] at p5
  rw [hv] at p7
  have a0 : acc (t1.gpr .t4) (t1.gpr .a4) = 0 := by rw [p4, pa]; rfl
  refine WP.mono (linLoop_ok h1.ws.scr p0 p1 p2 p3 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (ahead_k hoa (by omega)) (ahead_k hob (by omega))
    (by rw [p5, tu]; omega) (by rw [p5, tu]; omega) (by rw [p7, tv]; omega) (by rw [p7, tv]; omega)
    (by rw [a0]; decide) (by rw [a0]; decide))
    fun t2 ⟨qeq, _, _, _, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := Keep.trans' k1 (k2.mono (by decide))
  rw [m1, p5, p7, tu, tv, a0, Int.add_zero] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega)
    (by simp), ?_, k⟩
  rw [← qeq, Int.add_mul_emod_self_left]

/-! ## `shr` -/

/-- An arithmetic shift by 59, unsigned: the top bits, and the sign's ones above them. -/
theorem sshr59_toNat (x : BitVec 64) :
    (x.sshiftRight 59).toNat = if 2 ^ 63 ≤ x.toNat then x.toNat / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 else x.toNat / 2 ^ 59 := by
  have hx := x.isLt
  cases hm : x.msb
  · have hu : x.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ite_eq_right (by omega)]
  · have hu : 2 ^ 63 ≤ x.toNat := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_not, ite_eq_left hu]
    omega

/-- `L + M X` modulo `M K`, for `L < M`. -/
theorem mod_split {L M X K : Nat} (hL : L < M) : (L + M * X) % (M * K) = L + M * (X % K) := by
  have e : L + M * X = L + M * (X % K) + M * K * (X / K) := by
    conv_lhs => rw [← Nat.mod_add_div X K]
    rw [Nat.mul_add, Nat.mul_assoc]; omega
  rw [e, Nat.add_mul_mod_self_left]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · apply Nat.mod_eq_of_lt
    have := Nat.mod_lt X hK
    have : M * (X % K) + M ≤ M * K := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega

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
      have := Nat.mul_le_mul_left M hneg; omega
    rw [ite_eq_left hneg, ite_eq_left hc, e2]
    have e3 : M * 2 ^ 64 * (2 ^ 64 - 1) = 2 ^ 59 * (M * (2 ^ 5 * (2 ^ 64 - 1))) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl]; ac_rfl
    rw [e3, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 59), ← hL, Nat.add_assoc, ← Nat.mul_add, mod_split hLM]
    have inner : (x.toNat / 2 ^ 59 + 2 ^ 5 * (2 ^ 64 - 1)) % 2 ^ 64 = x.toNat / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 := by
      omega
    rw [inner]
  · have hc : ¬ M * 2 ^ 63 ≤ Vlo + M * x.toNat := by
      have : M * (x.toNat + 1) ≤ M * 2 ^ 63 := Nat.mul_le_mul_left M (by omega)
      rw [Nat.mul_add_one] at this; omega
    rw [ite_eq_right hneg, ite_eq_right hc, Nat.mul_zero, Nat.add_zero, e2, ← hL, mod_split hLM,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- `[o] = [a] / 2^59` (`shr`), `ν + 1` words, arithmetic, as
`Proof/Divstep/Tc.lean`'s `shr_nat` reads it (`H = 2^(64 ν) 2^63`). -/
theorem shr_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a : Nat}
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (shr o a) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (nu n + 1) =
        (wordsVal s.mem B (arr w a) (nu n + 1) + 2 * (2 ^ (64 * nu n) * 2 ^ 63) *
          (if 2 ^ (64 * nu n) * 2 ^ 63 ≤ wordsVal s.mem B (arr w a) (nu n + 1) then 2 ^ 64 - 1 else 0)) /
          2 ^ 59 % (2 * (2 ^ (64 * nu n) * 2 ^ 63)) ∧
      Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have da := arr_disj (w := w) hoa
  have := arr_al w o
  have := arr_al w a
  rw [shr]; simp only [seqs]; rw [WP.seq_iff]
  have hb1 : WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ cntN)) s fun t => Ctx t B Z w N n ∧
      t.mem = s.mem ∧ t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧
      t.gpr .t3 = BitVec.ofNat 64 (nu n) ∧ Keep kRegs s t := by
    refine ptr2_ok h.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) fun t p0 p1 kt mt => ?_
    have ht := h.of_keep (kt.mono (by decide))
    refine WP.mono (cntN_ok ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs s x := (kt.trans kx).mono (by decide)
    refine ⟨h.of_keep k0, xm.trans mt, ?_, ?_, x3, k0⟩
    · rw [kx.gpr (by decide)]; exact p0
    · rw [kx.gpr (by decide)]; exact p1
  refine WP.mono hb1 fun t1 ⟨h1, m1, p0, p1, p3, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (shrLoop_ok h1.ws.scr p0 p1 p3 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (ahead_k hoa (by omega))) fun t2 ⟨veq, q0, q1, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  have hs2 := h2.ws.scr
  refine WP.mono (WP.keep [.t5] (Q := fun t => t.mem = t2.mem.writeW (off B (arr w o + 8 * nu n))
      ((word t2.mem B (arr w a + 8 * nu n)).sshiftRight 59)) ?_ (by rfl) (by rfl)) fun t3 ⟨m3, k3⟩ => ?_
  · brun [q0, q1, hs2.ld (show arr w a + 8 * nu n + 8 ≤ Z by omega),
      hs2.st (show arr w o + 8 * nu n + 8 ≤ Z by omega),
      hs2.al8 (show arr w a + 8 * nu n + 8 ≤ Z by omega) (by omega),
      hs2.al8 (show arr w o + 8 * nu n + 8 ≤ Z by omega) (by omega)]
  have k : Keep kRegs s t3 := Keep.trans' (Keep.trans' k1 (k2.mono (by decide))) (k3.mono (by decide))
  rw [m1] at veq out2
  have out3 : Outside B (arr w o) (8 * (nu n + 1)) s.mem t3.mem := by
    rw [m3]; exact Loops.out_step _ out2 (by omega)
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out3) (by omega)
    (by simp), ?_, k⟩
  have wt : word t2.mem B (arr w a + 8 * nu n) = word s.mem B (arr w a + 8 * nu n) :=
    out2.word (by omega) (by omega)
  rw [m3, fin64_wordsVal_write_top _ _ _ _ _ (by omega), wt, wordsVal_succ_top s.mem B (arr w a) (nu n)]
  rw [wordsVal_succ_top s.mem B (arr w a) (nu n)] at veq
  exact shr_arith64 _ (wordsVal_lt _ _ _ _)
    (by rw [Nat.mul_comm (2 ^ (64 * nu n))] at veq ⊢; omega) (wordsVal_lt _ _ _ _)

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
  refine WP.mono (setup_ok h hcnt (by omega) (by omega) (by omega)) fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  have k5 : t1.gpr .a5 = s.gpr .a5 := k1.gpr (by decide)
  refine WP.mono (macLoop_ok h1.ws.scr p0 p1 p2 p3 hK1 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_any w o a K (by omega)) (ahead_any w o b K (by omega)))
    fun t2 ⟨qeq, q0, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))
  rw [m1, k5, p4] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega) (by simp), by simpa using qeq, q0, (k2.gpr (by decide)).trans k5,
    (k2.gpr (by decide)).trans (k1.gpr (by decide)), out2, k⟩

/-! ## `mred` -/

/-- An arithmetic shift by 63, unsigned: all ones for a negative word. -/
theorem sshr63_toNat (x : BitVec 64) :
    (x.sshiftRight 63).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  have hx := x.isLt
  cases hm : x.msb
  · have hu : x.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ite_eq_right (by omega)]
    omega
  · have hu : 2 ^ 63 ≤ x.toNat := by
      have := BitVec.msb_eq_decide x; rw [hm] at this; simp at this; omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_not, ite_eq_left hu]
    omega

/-- The top half of `ν + 1` words, from the top word's sign. -/
theorem half_top {Wlo A : Nat} (x : Nat) (hW : Wlo < A) :
    (A * 2 ^ 63 ≤ Wlo + A * x) ↔ 2 ^ 63 ≤ x := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hx => ?_
    have : A * (x + 1) ≤ A * 2 ^ 63 := Nat.mul_le_mul_left A hx
    rw [Nat.mul_add_one] at this; omega
  · intro h; have := Nat.mul_le_mul_left A h; omega

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
    · rw [ite_eq_left hlt]; rw [BitVec.lt_def, e1] at hlt; simp; omega
    · rw [ite_eq_right hlt]; rw [BitVec.lt_def, e1] at hlt; simp; omega
  simp only [half_top _ hWlo]
  have eT2 : (top.sshiftRight 63 + (if top + c < c then (1 : BitVec 64) else 0)).toNat =
      ((if 2 ^ 63 ≤ top.toNat then 2 ^ 64 - 1 else 0) + (top.toNat + c.toNat) / 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_add, sshr63_toNat, ecy]
  rw [e1, eT2]
  generalize hS : (if 2 ^ 63 ≤ top.toNat then 2 ^ 64 - 1 else 0) = Sv
  have hSv : Sv = 0 ∨ Sv = 2 ^ 64 - 1 := by rw [← hS]; split <;> simp
  have hr : Wlo + A * top.toNat + A * 2 ^ 64 * Sv + k * P = L + A * (top.toNat + c.toNat + 2 ^ 64 * Sv) := by
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]; omega
  have inner : (top.toNat + c.toNat) % 2 ^ 64 + 2 ^ 64 * ((Sv + (top.toNat + c.toNat) / 2 ^ 64) % 2 ^ 64) =
      (top.toNat + c.toNat + 2 ^ 64 * Sv) % (2 ^ 64 * 2 ^ 64) := by
    rcases hSv with h | h <;> subst h <;> omega
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
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `[o] = (t + k m) / 2^64` (`mred`), `ν + 1` words, as
`Proof/Divstep/TcS.lean`'s `mredRaw_nat` reads it: `E` the `ν + 2` words of
`t + k m` with `t`'s sign extended, `k = t₀ iv mod 2^64` for `iv` the window's
word `wIv` and `m` the `ν` words of array 2. -/
theorem mred_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {t o : Nat}
    (ht : t < N) (ho : o < N) (hN : N ≤ 256) (hto : t ≠ o) :
    WP isa (mred t o) s fun u => Ctx u B Z w N n ∧ Keys.Frame B w [t, o] [] s.mem u.mem ∧
      wordsVal u.mem B (arr w o) (nu n + 1) =
        (wordsVal s.mem B (arr w t) (nu n + 1) + 2 ^ (64 * nu n) * 2 ^ 64 *
          (if 2 ^ (64 * nu n) * 2 ^ 63 ≤ wordsVal s.mem B (arr w t) (nu n + 1) then 2 ^ 64 - 1 else 0) +
          (word s.mem B (arr w t)).toNat * (s.mem.readW (off B (arr w aW + wIv)) 64).toNat % 2 ^ 64 *
            wordsVal s.mem B (arr w aMz) (nu n)) % (2 ^ (64 * nu n) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64 ∧
      Keep kRegs s u := by
  have hm : aMz < N := by have := h.room; unfold aMz; omega
  have hW : aW < N := by have := h.room; unfold aW; omega
  have ft := h.ws.arr_fit ht
  have fo := h.ws.arr_fit ho
  have fm := h.ws.arr_fit hm
  have fW := h.ws.arr_fit hW
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have := h.nw
  have hnw := h.ws.nowrap
  have dto := arr_disj (w := w) hto
  have := h.wbig
  have := arr_al w t
  have := arr_al w o
  have := arr_al w aW
  have hs := h.ws.scr
  rw [mred]; simp only [seqs]; rw [WP.seq_iff]
  -- The sign of `t`, and `k`.
  refine WP.mono (WP.keep kRegs (Q := fun u =>
      u.gpr .a7 = (word s.mem B (arr w t + 8 * nu n)).sshiftRight 63 ∧
      u.gpr .a5 = word s.mem B (arr w t) * s.mem.readW (off B (arr w aW + wIv)) 64 ∧ u.mem = s.mem)
    ?_ (by rfl) (by rfl)) fun u1 ⟨⟨a7₁, a5₁, m₁⟩, k₁⟩ => ?_
  · brun [topOf, ldW, cntN, List.append_assoc, runBlock_ptr B w, h.ws.s10, h.ws.s11, h.s8, ofNat_succ,
      ofNat_half (show n + 1 < 2 ^ 64 by omega), ofNat_shl3 (show 8 * nu n < 2 ^ 64 by omega), off_add,
      (show t < 2048 by omega), (show aW < 2048 by decide), wIv,
      hs.ld (show arr w t + 8 * nu n + 8 ≤ Z by omega), hs.ld (show arr w t + 8 ≤ Z by omega),
      hs.ld (show arr w aW + 40 + 8 ≤ Z by omega),
      hs.al8 (show arr w t + 8 * nu n + 8 ≤ Z by omega) (by omega),
      hs.al8 (show arr w t + 8 ≤ Z by omega) (by omega),
      hs.al8 (show arr w aW + 40 + 8 ≤ Z by omega) (by omega)]
  have h1 := h.of_keep k₁
  rw [WP.seq_iff]
  -- `t += k m` over `ν` words.
  refine WP.mono (mac_ok h1 (fun x hx => cntN_ok hx) (K := nu n) (by omega) (by omega) ht ht hm hN)
    fun u2 ⟨h2, _, v₂, p0₂, a5₂, a7₂, o₂, k₂⟩ => ?_
  rw [m₁, a5₁] at v₂
  rw [m₁] at o₂
  have hs2 := h2.ws.scr
  rw [WP.seq_iff]
  -- The carry into word `ν`, the sign and its carry into word `ν + 1`.
  refine WP.mono (WP.keep kRegs (Q := fun u => u.mem =
      (u2.mem.writeW (off B (arr w t + 8 * nu n)) (word u2.mem B (arr w t + 8 * nu n) + u2.gpr .t4)).writeW
        (off B (arr w t + 8 * nu n + 8)) (u2.gpr .a7 +
          (if word u2.mem B (arr w t + 8 * nu n) + u2.gpr .t4 < u2.gpr .t4 then (1 : BitVec 64) else 0)))
    ?_ (by rfl) (by rfl)) fun u3 ⟨m₃, k₃⟩ => ?_
  · brun [p0₂, hs2.ld (show arr w t + 8 * nu n + 8 ≤ Z by omega), hs2.st (show arr w t + 8 * nu n + 8 ≤ Z by omega),
      hs2.st (show arr w t + 8 * nu n + 8 + 8 ≤ Z by omega),
      hs2.al8 (show arr w t + 8 * nu n + 8 ≤ Z by omega) (by omega),
      hs2.al8 (show arr w t + 8 * nu n + 8 + 8 ≤ Z by omega) (by omega)]
  have h3 := h2.of_keep k₃
  -- `[o] :=` words `1 … ν + 1` of `[t]`.
  have hb4 : WP isa (.block (ptr .t0 o ++ ptr .t1 t ++ [.addi .t1 .t1 8] ++ cntN1)) u3 fun x =>
      Ctx x B Z w N n ∧ x.mem = u3.mem ∧ x.gpr .t0 = off B (arr w o) ∧ x.gpr .t1 = off B (arr w t + 8) ∧
      x.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧ Keep kRegs u3 x := by
    rw [List.append_assoc]
    refine ptr2_ok h3.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) fun x q0 q1 kx mx => ?_
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.t1] (Q := fun y => y.gpr .t1 = off B (arr w t + 8) ∧ y.mem = x.mem)
      (by brun [q1, off_add]) (by rfl) (by rfl)) fun y ⟨⟨y1, ym⟩, ky⟩ => ?_
    have hy := h3.of_keep ((kx.trans ky).mono (by decide))
    refine WP.mono (cntN1_ok hy) fun z ⟨⟨z3, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs u3 z := ((kx.trans ky).trans kz).mono (by decide)
    refine ⟨h3.of_keep k0, zm.trans (ym.trans mx), ?_, ?_, z3, k0⟩
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q0
    · rw [kz.gpr (by decide)]; exact y1
  rw [WP.seq_iff]
  refine WP.mono hb4 fun x ⟨hx, mx, r0, r1, r3, kx⟩ => ?_
  refine WP.mono (Loops.copyLoop_ok hx.ws.scr r0 r1 r3 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by unfold Ahead; omega)) fun u4 ⟨v₄, o₄, k₄⟩ => ?_
  have k : Keep kRegs s u4 := Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' k₁ k₂) k₃) kx) (k₄.mono (by decide))
  rw [mx] at v₄ o₄
  have o₃ : Outside B (arr w t + 8 * nu n) 16 u2.mem u3.mem := by
    rw [m₃]
    exact ((writeW_outside _ B _ (d := arr w t + 8 * nu n) (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B _ (d := arr w t + 8 * nu n + 8) (by omega)).mono (by omega) (by omega))
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · exact ((Keys.Frame.of_arr (o := t) (d := 0) (by simpa only [Nat.add_zero] using o₂) (by omega) (by simp)).trans
      (Keys.Frame.of_arr (o := t) (d := 8 * nu n) o₃ (by omega) (by simp))).trans
      (Keys.Frame.of_arr (o := o) (d := 0) (by simpa only [Nat.add_zero] using o₄) (by omega) (by simp))
  · have wtop : word u2.mem B (arr w t + 8 * nu n) = word s.mem B (arr w t + 8 * nu n) :=
      o₂.word (by omega) (by omega)
    have a7₂' : u2.gpr .a7 = (word s.mem B (arr w t + 8 * nu n)).sshiftRight 63 := a7₂.trans a7₁
    rw [wtop, a7₂'] at m₃
    rw [show arr w t + 8 * nu n + 8 = arr w t + 8 * (nu n + 1) by omega] at m₃
    have E3 : wordsVal u3.mem B (arr w t) (nu n + 1 + 1) =
        wordsVal u2.mem B (arr w t) (nu n) + 2 ^ (64 * nu n) * (word s.mem B (arr w t + 8 * nu n) + u2.gpr .t4).toNat +
          2 ^ (64 * nu n) * 2 ^ 64 * ((word s.mem B (arr w t + 8 * nu n)).sshiftRight 63 +
            (if word s.mem B (arr w t + 8 * nu n) + u2.gpr .t4 < u2.gpr .t4 then (1 : BitVec 64) else 0)).toNat := by
      rw [m₃, fin64_wordsVal_write_top _ _ _ _ _ (by omega), fin64_wordsVal_write_top _ _ _ _ _ (by omega),
        show 64 * (nu n + 1) = 64 * nu n + 64 by omega, Nat.pow_add]
    rw [mred_arith64 _ _ (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) v₂] at E3
    have e0 : wordsVal u3.mem B (arr w t) (nu n + 1 + 1) =
        (word u3.mem B (arr w t)).toNat + 2 ^ 64 * wordsVal u3.mem B (arr w t + 8) (nu n + 1) := rfl
    have hw0 := (word u3.mem B (arr w t)).isLt
    rw [BitVec.toNat_mul] at E3
    rw [v₄, wordsVal_succ_top s.mem B (arr w t) (nu n), ← E3, e0]
    omega

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
  have hm : aMz < N := by have := h.room; unfold aMz; omega
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
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by omega) (by omega) (by omega))
    fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (Loops.subLoop_ok h1.ws.scr p0 p1 p2 p3 (by rw [p4]; decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k hsx (by omega)) (ahead_k hsm (by omega)))
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
    refine ptrs_ok h2.ws (by omega) (by omega) (by omega) fun t q0 q1 q2 kt mt => ?_
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
    r0 r1 r2 r3 (by rw [r4]; exact mask_of_borrow _ b4) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (ahead_k hos (by omega)) (ahead_any w o x (nu n + 1) (by omega))) fun t4 ⟨seq, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 :=
    Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))) k3) (k4.mono (by decide))
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · rw [m3] at out4
    exact (Keys.Frame.of_arr (o := sc) (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega)
      (by simp)).trans (Keys.Frame.of_arr (o := o) (d := 0) (by simpa only [Nat.add_zero] using out4)
        (by omega) (by simp))
  · have vx : wordsVal t2.mem B (arr w x) (nu n + 1) = X := by
      rw [out2.wordsVal (by have := arr_disj (w := w) hsx; omega) (by omega)]; exact hX
    rw [seq, m3, vx]
    have hpR := wordsVal_lt s.mem B (arr w aMz) (nu n + 1)
    have hXR := wordsVal_lt s.mem B (arr w x) (nu n + 1)
    have hSR := wordsVal_lt t2.mem B (arr w sc) (nu n + 1)
    rw [hp] at hpR veq
    rw [hX] at hXR veq
    generalize 2 ^ (64 * (nu n + 1)) = R at hpR hXR hSR veq
    by_cases e : (t2.gpr .t4).toNat = 1
    · rw [e] at veq; simp only [e, decide_true, ↓reduceIte]
      have : ¬ p ≤ X := by omega
      simp only [this, ↓reduceIte]
    · have e0 : (t2.gpr .t4).toNat = 0 := by omega
      rw [e0] at veq; simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      have : p ≤ X := by omega
      simp only [this, ↓reduceIte]; omega

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
  brun [signOf, topOf, cntN, List.append_assoc, runBlock_ptr B w, (show j < 2048 by omega), h.ws.s10, h.ws.s11,
    h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega), ofNat_shl3 (show 8 * nu n < 2 ^ 64 by omega),
    off_add, hs.ld (show arr w j + 8 * nu n + 8 ≤ Z by omega),
    hs.al8 (show arr w j + 8 * nu n + 8 ≤ Z by omega) (by omega), sshr63_mask]

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
  refine ptrs_ok h1.ws (by omega) (by omega) (by omega) fun t2 p0 p1 p2 k2 m2 => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (cntN1_ok h2) fun t3 ⟨⟨p3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have q4 : t3.gpr .t4 = t1.gpr .t4 := (k3.gpr (by decide)).trans (k2.gpr (by decide))
  refine WP.mono (Loops.selLoop_ok (b := decide (2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat)) h3.ws.scr
    (by rw [k3.gpr (by decide)]; exact p0) (by rw [k3.gpr (by decide)]; exact p1)
    (by rw [k3.gpr (by decide)]; exact p2) p3 (by rw [q4, r4]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (ahead_any w o a (nu n + 1) (by omega)) (ahead_k hob (by omega)))
    fun t4 ⟨v4, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide)))
    (k3.mono (by decide))) (k4.mono (by decide))
  rw [m3, m2, m1] at v4 out4
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega)
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
  refine ptr_ok h.ws (by decide) (by decide) (by omega) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.ws.s9, ofNat_succ]
  have k1 : Keep kRegs s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep kRegs s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (Loops.zeroLoop_ok (dO := arr w j) (n := w + 1) (h.of_keep k2).ws.scr (by rw [ky.gpr (by decide)]; exact u0)
    (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega) (by omega) (by omega) (by omega)) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  exact ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Keys.Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega) (by simp), out, z, Keep.trans' k2 (kt.mono (by decide))⟩

end VG.Proof.Rsa.RISCV64.InvBatch
