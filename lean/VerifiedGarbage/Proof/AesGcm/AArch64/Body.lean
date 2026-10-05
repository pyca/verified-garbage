import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Env`. -/
section

/-!
# AES-GCM on AArch64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`) and the working space (2560
bytes at `W`) (`Lay`): the state is disjoint from the parts of `W` other than
`[16, 96)` (where `seal` and `open` keep it), and the context from both.
`Perm` says the state may read the context and write the state and `W`;
`Env` adds the registers that hold the three addresses throughout, and the
stack pointer. `arun` runs a block symbolically.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "arun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    mov, ptr, imm, tO, uO, aadO, alenO, dataO, lenO, tlO, vO, rO, scrO, List.cons_append, List.nil_append,
    List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, and_true, true_and, eq_self_iff_true, $ts,*]) <;> try rfl)

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => VG.Proof.AesGcm.AArch64.in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- The regions: the context, the state and the parts of `W`. -/
structure Lay (Ctx St W : Addr) : Prop where
  cw : Ctx.toNat + 256 ≤ 2 ^ 64
  sw : St.toNat + 80 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩
  cw' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  sa : (⟨St, 80⟩ : Region).Disjoint ⟨W, 16⟩
  sb : (⟨St, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩

/-- What a state may access. -/
structure Perm (Ctx St W : Addr) (s : State) : Prop where
  ctx : Covers [⟨Ctx, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨St, 80⟩] s.wr
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the context, the state and `W`, the stack
pointer, and what the state may access. -/
structure Env (Ctx St W SP : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = St
  x21 : s.gpr .x21 = Ctx
  sp : s.sp = SP
  perm : VG.Proof.AesGcm.AArch64.Perm Ctx St W s

theorem Perm.of_eq {Ctx St W : Addr} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Perm Ctx St W s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.AArch64.Perm Ctx St W s' := by
  obtain ⟨a, b, c⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact c⟩

/-- An environment, after code that keeps `x19`–`x21`, the stack pointer and
the permissions. -/
theorem Env.keep {Ctx St W SP : Addr} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {Ctx St W SP : Addr} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {Ctx : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨Ctx + BitVec.ofNat 64 d, n⟩ ⟨Ctx, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {St : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ ⟨St, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {Ctx St W : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (VG.Proof.AesGcm.AArch64.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.AArch64.Lay.aSub hd)
  · exact (L.sb.sub_left (VG.Proof.AesGcm.AArch64.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.AArch64.Lay.bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (VG.Proof.AesGcm.AArch64.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.AArch64.Lay.stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (VG.Proof.AesGcm.AArch64.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.AArch64.Lay.wSub hd)

/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.sw; omega) (by have := L.sw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

end Lay

namespace Perm

variable {Ctx St W : Addr} {s : State} (P : VG.Proof.AesGcm.AArch64.Perm Ctx St W s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.AArch64.in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.AesGcm.AArch64.covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.AArch64.covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.AArch64.covers_off P.w h (by decide)

end Perm

/-! ## Arithmetic on lengths -/

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem lsr_ofNat (n k : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem lsl4_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem lsl3_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.mul_comm]

theorem and15 (x : BitVec 64) : x &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_beq_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = !decide (a = 0) := by
  rw [bne, VG.Proof.AesGcm.AArch64.ofNat_beq_zero ha]

/-- `cbz` on a register holding `a`. -/
theorem eval_zero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (a = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq, VG.Proof.AesGcm.AArch64.ofNat_beq_zero ha]

/-- `cbnz` on a register holding `a`. -/
theorem eval_nonzero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.nonzero .x r) s = some (!decide (a = 0)) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, VG.Proof.AesGcm.AArch64.ofNat_bne_zero ha]

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, VG.Proof.AesGcm.AArch64.ofNat_add_ofNat]

theorem movz_ofNat {k : Nat} (hk : k < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A running block, with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- The registers the pieces keep for the function running them: the rounds
and the function's own values. -/
abbrev keptRegs : List Reg := [.x22, .x26, .x27, .x28]

/-- The kept registers hold the values `k` gives them. -/
def Kept (k : Reg → BitVec 64) (s : State) : Prop := ∀ r ∈ VG.Proof.AesGcm.AArch64.keptRegs, s.gpr r = k r

theorem Kept.of_eq {k : Reg → BitVec 64} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Kept k s) (hg : ∀ r ∈ VG.Proof.AesGcm.AArch64.keptRegs, s'.gpr r = s.gpr r) :
    VG.Proof.AesGcm.AArch64.Kept k s' := fun r hr => (hg r hr).trans (h r hr)

theorem Kept.of_saved {k : Reg → BitVec 64} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Kept k s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) : VG.Proof.AesGcm.AArch64.Kept k s' :=
  h.of_eq fun r hr => hg r (by
    simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

/-- Registers outside `rs` are unchanged. -/
def Others (rs : List Reg) (s s' : State) : Prop := ∀ r, r ∉ rs → s'.gpr r = s.gpr r

theorem Kept.of_others {k : Reg → BitVec 64} {s s' : State} {rs : List Reg} (h : VG.Proof.AesGcm.AArch64.Kept k s) (hg : VG.Proof.AesGcm.AArch64.Others rs s s')
    (hd : ∀ r ∈ VG.Proof.AesGcm.AArch64.keptRegs, r ∉ rs := by decide) : VG.Proof.AesGcm.AArch64.Kept k s' :=
  h.of_eq fun r hr => hg r (hd r hr)

/-- What a block that changes only registers leaves. -/
structure Regs (rs : List Reg) (s s' : State) : Prop where
  others : VG.Proof.AesGcm.AArch64.Others rs s s'
  mem : s'.mem = s.mem
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Env.of_regs {Ctx St W SP : Addr} {s s' : State} {rs : List Reg} (h : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hr : VG.Proof.AesGcm.AArch64.Regs rs s s')
    (hd : ∀ r ∈ [Reg.x19, .x20, .x21], r ∉ rs := by decide) : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' :=
  h.keep (fun r h' => hr.others r (hd r h')) hr.sp hr.rd hr.wr

theorem Regs.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.AesGcm.AArch64.Regs rs s₁ s₂) (h₂ : VG.Proof.AesGcm.AArch64.Regs rs' s₂ s₃)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : VG.Proof.AesGcm.AArch64.Regs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.others r fun h => hr (hs r h)).trans (h₁.others r hr), h₂.mem.trans h₁.mem,
    h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Regs.comp {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.AesGcm.AArch64.Regs rs s₁ s₂) (h₂ : VG.Proof.AesGcm.AArch64.Regs rs' s₂ s₃) :
    VG.Proof.AesGcm.AArch64.Regs (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => (h₂.others r fun h => hr (List.mem_append_right _ h)).trans
    (h₁.others r fun h => hr (List.mem_append_left _ h)), h₂.mem.trans h₁.mem,
    h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Regs.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.AesGcm.AArch64.Regs rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    VG.Proof.AesGcm.AArch64.Regs rs' s s' :=
  ⟨fun r hr => h.others r fun h' => hr (hs r h'), h.mem, h.sp, h.rd, h.wr⟩

theorem Regs.refl (rs : List Reg) (s : State) : VG.Proof.AesGcm.AArch64.Regs rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- Proves `Others rs s s'` for a chain of register writes. -/
macro "others_tac" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_write, hr]))

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Loops`. -/
section

/-!
# AES-GCM on AArch64: the byte loops and `minK`

Untrusted: everything here is checked by Lean. `copy` copies `x13` bytes
from `x12` to `x11`, and `xor` XORs `x13` bytes at `x11` into those at `x12`,
a byte at a time through advancing pointers (`copy_ok`, `xor_ok`); the buffers
do not overlap. `minK` computes `min (16 - x25, x24)` (`minK_ok`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem byte_rt (b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: `n` bytes at `S` (read) and at `D`
(written), apart. -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The registers the loops write. -/
abbrev loopRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-! ## `copy` -/

abbrev copyBody : List Instr :=
  [.ldrb .x14 .x12 0, .strb .x14 .x11 0, .addImm .x .x12 .x12 1, .addImm .x .x11 .x11 1,
    .subImm .x .x13 .x13 1]

theorem copyStep_ok (s : State) {A B : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x11 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 1) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.AArch64.copyBody s = some s' ∧ s'.mem = s.mem.writeW B (s.mem A) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x11 = s.gpr .x11 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.AesGcm.AArch64.copyBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, VG.Proof.AesGcm.AArch64.byte_rt, VG.Proof.AesGcm.AArch64.read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  · simp only [VG.Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h
    simp [gpr_write, h₁, h₂, h₃, h₄]

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x12 = S) (hD : s.gpr .x11 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (hpos : 0 < n) (h : VG.Proof.AesGcm.AArch64.LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .x12 = S + BitVec.ofNat 64 n ∧ s'.gpr .x11 = D + BitVec.ofNat 64 n ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.AArch64.copyBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = S + BitVec.ofNat 64 i ∧
      t.gpr .x11 = D + BitVec.ofNat 64 i ∧ t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hS]; simp, by rw [hD]; simp, by rw [hn, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x11, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x11', x13', g', sp', rd', wr'⟩ := VG.Proof.AesGcm.AArch64.copyStep_ok t
    (A := S + BitVec.ofNat 64 i) (B := D + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [x11, BitVec.add_zero]) (by rw [rd, wr]; exact VG.Proof.AesGcm.AArch64.in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact VG.Proof.AesGcm.AArch64.in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _
  have hx : writeBytes s.mem D (bytesAt s.mem S i) (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact h.disj _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, hx, VG.Proof.AesGcm.AArch64.bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) (s.mem (S + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := VG.Proof.AesGcm.AArch64.eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x12', x12, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat, he],
      by rw [x11', x11, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat, he], gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat], by rw [x11', x11, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat],
      x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-- `copy`: the `n` bytes at `S` to `D`. -/
theorem copy_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x12 = S) (hD : s.gpr .x11 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (h : VG.Proof.AesGcm.AArch64.LoopPre s S D n) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero hn (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    exact WP.mono (VG.Proof.AesGcm.AArch64.copyLoop_ok s hS hD hn (by omega) h) fun s' ⟨m, _, _, g, sp, rd, wr⟩ => ⟨m, g, sp, rd, wr⟩

/-! ## `xor` -/

abbrev xorBody : List Instr :=
  [.ldrb .x14 .x12 0, .ldrb .x15 .x11 0, .logic .eor .w .x14 .x14 .x15, .strb .x14 .x12 0,
    .addImm .x .x12 .x12 1, .addImm .x .x11 .x11 1, .subImm .x .x13 .x13 1]

theorem byte_xor (a b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) ^^^
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))))) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, show i < 64 by omega, show i < 32 by omega,
    hi, decide_true, Bool.true_and]

theorem xorStep_ok (s : State) {A B : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x11 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) B 1) (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.AArch64.xorBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A ^^^ s.mem B) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x11 = s.gpr .x11 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := VG.Proof.AesGcm.AArch64.in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.AesGcm.AArch64.xorBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, VG.Proof.AesGcm.AArch64.byte_xor, VG.Proof.AesGcm.AArch64.read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  · simp only [VG.Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅]

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    VG.Proof.AesGcm.AArch64.xorBytes m D S (i + 1) = VG.Proof.AesGcm.AArch64.xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [VG.Proof.AesGcm.AArch64.xorBytes, VG.Proof.AesGcm.AArch64.bytesAt_succ, List.zipWith_append, VG.Proof.AesGcm.AArch64.length_bytesAt]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (VG.Proof.AesGcm.AArch64.xorBytes m D S n).length = n := by
  simp [VG.Proof.AesGcm.AArch64.xorBytes, VG.Proof.AesGcm.AArch64.length_bytesAt]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

/-- The source byte `i` is not overwritten so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

/-- `xorLoop`: the `n` bytes at `S` (`x11`) XORed into those at `D` (`x12`). -/
theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x11 = S) (hD : s.gpr .x12 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (hpos : 0 < n) (h : VG.Proof.AesGcm.AArch64.LoopPre s S D n) :
    WP isa xorLoop s fun s' => s'.mem = writeBytes s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D S n) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.AArch64.xorBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x11 = S + BitVec.ofNat 64 i ∧ t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D S i) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hD]; simp, by rw [hS]; simp, by rw [hn, Nat.sub_zero],
      by simp [VG.Proof.AesGcm.AArch64.xorBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x11, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x11', x13', g', sp', rd', wr'⟩ := VG.Proof.AesGcm.AArch64.xorStep_ok t
    (A := D + BitVec.ofNat 64 i) (B := S + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [x11, BitVec.add_zero]) (by rw [rd, wr]; exact VG.Proof.AesGcm.AArch64.in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact VG.Proof.AesGcm.AArch64.in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := VG.Proof.AesGcm.AArch64.length_xorBytes s.mem D S i
  have hmem : t'.mem = writeBytes s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D S (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcm.AArch64.src_kept h.disj hi h.lt _ hlen, VG.Proof.AesGcm.AArch64.dst_kept hi h.lt _ hlen, VG.Proof.AesGcm.AArch64.xorBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega), hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := VG.Proof.AesGcm.AArch64.eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat], by rw [x11', x11, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat],
      x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-- `xor`: the `n` bytes at `S` (`x11`) XORed into those at `D` (`x12`). -/
theorem xor_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x11 = S) (hD : s.gpr .x12 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (h : VG.Proof.AesGcm.AArch64.LoopPre s S D n) :
    WP isa xor s fun s' => s'.mem = writeBytes s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D S n) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero hn (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [VG.Proof.AesGcm.AArch64.xorBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcm.AArch64.xorLoop_ok s hS hD hn (by omega) h

/-! ## `minK` -/

/-- The registers `minK` writes. -/
abbrev minRegs : List Reg := [.x9, .x10, .x11]

theorem minK_ok (s : State) {o n : Nat} (h25 : s.gpr .x25 = BitVec.ofNat 64 o)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (ho : o < 16) (hn : n < 2 ^ 64) :
    WP isa minK s fun s' => s'.gpr .x10 = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x9₁, x10₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [imm .x9 16, .sub .x .x9 .x9 .x25, .lsr .x .x10 .x24 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (16 - o) ∧ s₁.gpr .x10 = BitVec.ofNat 64 (n / 16) ∧
      (∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h25, VG.Proof.AesGcm.AArch64.ofNat_sub (show o ≤ 16 by omega) (show 16 < 2 ^ 64 by decide)]
    · simp [gpr_write, h24, VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ hn]
    · simp only [VG.Proof.AesGcm.AArch64.minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (n / 16 = 0)) (VG.Proof.AesGcm.AArch64.eval_nonzero x10₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h16 : 16 ≤ n := by simp at ht; omega
    refine WP.run (Q := fun s' => s' = s₁.write .x .x10 (s₁.gpr .x9 + BitVec.ofNat 64 0)) ⟨_, by arun [], rfl⟩
      fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, x9₁, BitVec.add_zero, BitVec.setWidth_eq]
      rw [Nat.min_eq_left (by omega)]
    · simp only [VG.Proof.AesGcm.AArch64.minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.2.1, ite_false]; exact g₁ r (by simp [VG.Proof.AesGcm.AArch64.minRegs, hr.1, hr.2.1, hr.2.2])
  · have h16 : n < 16 := by simp at hf; omega
    obtain ⟨s₂, run₂, x11₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.sub .x .x11 .x9 .x24, .lsr .x .x11 .x11 63] s₁ = some s₂ ∧
        s₂.gpr .x11 = BitVec.ofNat 64 (if n ≤ 16 - o then 0 else 1) ∧
        (∀ r, r ≠ .x11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by arun [], ?_⟩
      refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, x9₁, g₁ .x24 (by decide), h24, BitVec.setWidth_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by omega),
        VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
      by_cases hc : n ≤ 16 - o
      · simp only [hc, ↓reduceIte]
        rw [VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by decide), Nat.div_eq_of_lt (by omega)]
      · simp only [hc, ↓reduceIte]
        rw [VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by decide)]
        omega
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hg : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs → s₂.gpr r = s.gpr r := fun r hr => by
      rw [g₂ r (by simp only [VG.Proof.AesGcm.AArch64.minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2),
        g₁ r hr]
    by_cases hc : n ≤ 16 - o
    · simp only [hc, ↓reduceIte] at x11₂
      refine WP.ite true (by rw [VG.Proof.AesGcm.AArch64.eval_zero x11₂ (by decide)]; rfl) (fun _ => ?_) (fun h => by cases h)
      refine WP.run (Q := fun s' => s' = s₂.write .x .x10 (s₂.gpr .x24 + BitVec.ofNat 64 0))
        ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
      subst hs'
      refine ⟨?_, fun r hr => ?_, by rw [mem_write, m₂, m₁], by rw [sp_write, sp₂, sp₁],
        by rw [rd_write, rd₂, rd₁], by rw [wr_write, wr₂, wr₁]⟩
      · simp only [gpr_write, ite_true, BitVec.add_zero, BitVec.setWidth_eq, g₂ .x24 (by decide),
          g₁ .x24 (by decide), h24]
        rw [Nat.min_eq_right hc]
      · simp only [VG.Proof.AesGcm.AArch64.minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [gpr_write, hr.2.1, ite_false]; exact hg r (by simp [VG.Proof.AesGcm.AArch64.minRegs, hr.1, hr.2.1, hr.2.2])
    · simp only [hc, ↓reduceIte] at x11₂
      refine WP.ite false (by rw [VG.Proof.AesGcm.AArch64.eval_zero x11₂ (by decide)]; rfl) (fun h => by cases h) (fun _ => ?_)
      refine WP.run (Q := fun s' => s' = s₂.write .x .x10 (s₂.gpr .x9 + BitVec.ofNat 64 0))
        ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
      subst hs'
      refine ⟨?_, fun r hr => ?_, by rw [mem_write, m₂, m₁], by rw [sp_write, sp₂, sp₁],
        by rw [rd_write, rd₂, rd₁], by rw [wr_write, wr₂, wr₁]⟩
      · simp only [gpr_write, ite_true, BitVec.add_zero, BitVec.setWidth_eq, g₂ .x9 (by decide), x9₁]
        rw [Nat.min_eq_left (by omega)]
      · simp only [VG.Proof.AesGcm.AArch64.minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [gpr_write, hr.2.1, ite_false]; exact hg r (by simp [VG.Proof.AesGcm.AArch64.minRegs, hr.1, hr.2.1, hr.2.2])

/-! ## Bytes written -/

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [VG.Proof.AesGcm.AArch64.bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  have := VG.Proof.AesGcm.AArch64.bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, VG.Proof.AesGcm.AArch64.bytesAt_add, VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬xs.length + i < xs.length by omega]

/-- The bytes of `bytesAt m D n` from `j` on. -/
theorem bytesAt_drop (m : Mem) (D : Addr) {j n : Nat} (hj : j ≤ n) :
    (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := by
  rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.AArch64.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _),
    Nat.add_sub_cancel_left]

/-- The first `k` bytes of `bytesAt m D n`. -/
theorem bytesAt_take (m : Mem) (D : Addr) {k n : Nat} (hk : k ≤ n) :
    (bytesAt m D n).take k = bytesAt m D k := by
  rw [show n = k + (n - k) by omega, VG.Proof.AesGcm.AArch64.bytesAt_add, List.take_left' (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)]

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Absorb`. -/
section

/-!
# AES-GCM on AArch64: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`x24` bytes at `x23` into GHASH, with the accumulator at `St + yo` and the
`x25` buffered bytes at `St + 32`: it fills the buffer (`absSeg1_ok`) and
absorbs it if full (`absCall1_ok`, a call of `vg_ghash` on one block or
none), absorbs whole blocks (`absSeg2_ok`, `absCall2_ok`) and buffers the
rest (`absTail_ok`), by the steps of `Proof/Gcm/Stream.lean`; `absorb_ok`
puts them together. The pieces are proven separately, between the calls, so
that the proof of constant time can use them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
state and `W`. -/
structure DataOk (St W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  st : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace DataOk

variable {St W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.AArch64.DataOk St W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.AArch64.DataOk St W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.AArch64.DataOk St W s (D + BitVec.ofNat 64 k) (n - k) where
  rd := VG.Proof.AesGcm.AArch64.covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  st := h.st.sub_left (Offset.sub_base D (by omega))
  w := h.w.sub_left (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.AArch64.DataOk St W s D k where
  rd := VG.Proof.AesGcm.AArch64.covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)

end DataOk

/-- The regions `absorb` writes. -/
abbrev absFrame (St W : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨St + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- The bytes `absorb` takes into the buffer first. -/
abbrev headLen (o n : Nat) : Nat := min (16 - o) n

/-- Whether the buffer is then full: the blocks of the first call. -/
abbrev headBlocks (o n : Nat) : Nat := if o + VG.Proof.AesGcm.AArch64.headLen o n = 16 then 1 else 0

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`x23`, `x24`, `x25` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (x : List Byte) (D : Addr)
    (n o : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  ho : x.length % 16 = o
  data : VG.Proof.AesGcm.AArch64.DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Before the first call: the buffer filled, from `m₀`. -/
structure Abs1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (D : Addr) (n o : Nat)
    (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.headLen o n)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - VG.Proof.AesGcm.AArch64.headLen o n)
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : VG.Proof.AesGcm.AArch64.DataOk St W s D n
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32)
    (W + BitVec.ofNat 64 512) (VG.Proof.AesGcm.AArch64.headBlocks o n)
  buf : bytesAt s.mem (St + BitVec.ofNat 64 32) (o + VG.Proof.AesGcm.AArch64.headLen o n) =
    bytesAt m₀ (St + BitVec.ofNat 64 32) o ++ bytesAt m₀ D (VG.Proof.AesGcm.AArch64.headLen o n)
  frame : Frame [⟨St + BitVec.ofNat 64 (32 + o), VG.Proof.AesGcm.AArch64.headLen o n⟩] m₀ s.mem

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x : List Byte)
    (D : Addr) (n o : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : VG.Proof.AesGcm.AArch64.DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.absFrame St W yo) m₀ s.mem

/-- Before the second call: the whole blocks from byte `j` on. -/
structure Abs3 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x : List Byte)
    (D : Addr) (n o : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16))
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16)))
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : VG.Proof.AesGcm.AArch64.DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.absFrame St W yo) m₀ s.mem
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (D + BitVec.ofNat 64 j)
    (W + BitVec.ofNat 64 512) ((n - j) / 16)

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x₀ x : List Byte)
    (o : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.AArch64.absFrame St W yo) m₀ s.mem

section
variable {Ctx St W : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataOk St W s D n) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.absFrame St W yo, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))

/-- The hash subkey is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ VG.Proof.AesGcm.AArch64.absFrame St W yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

/-- The call of `vg_ghash` on the accumulator, from a state whose registers
are its arguments. -/
theorem ghCall_of {SP : Addr} {s : State} (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) {P : Addr} {nb : Nat}
    (h0 : s.gpr .x0 = Ctx + BitVec.ofNat 64 240) (h1 : s.gpr .x1 = St + BitVec.ofNat 64 yo)
    (h2 : s.gpr .x2 = P) (h3 : s.gpr .x3 = BitVec.ofNat 64 nb) (h4 : s.gpr .x4 = W + BitVec.ofNat 64 512)
    (hn : 16 * nb < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * nb⟩)
    (hpw : (⟨P, 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpr : Covers [⟨P, 16 * nb⟩] (s.rd ++ s.wr)) :
    GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) nb :=
  ⟨h0, h1, h2, h3, h4, hn, L.ctx_st (by decide) (by omega), L.ctx_w (by decide) (by decide),
    hpy, L.st_w (by omega) (.inr ⟨by decide, by decide⟩), hpw,
    VG.Proof.AesGcm.AArch64.covers_cons (he.perm.ctxC (by decide)) (VG.Proof.AesGcm.AArch64.covers_cons hpr (VG.Proof.AesGcm.AArch64.covers_cons
      (VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by omega))) (VG.Proof.AesGcm.AArch64.covers_left (he.perm.wC (by decide))))),
    VG.Proof.AesGcm.AArch64.covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))⟩

omit L hyo in
/-- What a call of `vg_ghash` from an environment leaves. -/
theorem GhPost.env {SP : Addr} {s s' : State} {H' Y D S : Addr} {nb : Nat}
    (h : GhPost s H' Y D S nb s') (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' :=
  he.of_saved h.saved h.sp h.rd h.wr

end

theorem ghArgs_eq (yo : Nat) (rest : List Instr) :
    ghArgs yo ++ rest = ptr .x0 .x21 240 :: ptr .x1 .x20 yo :: ptr .x4 .x19 scrO :: rest := rfl

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer. -/
theorem absSeg1_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.AbsIn Ctx St W SP k H x D n o s) :
    WP isa (absSeg1 yo) s (VG.Proof.AesGcm.AArch64.Abs1 Ctx St W SP k yo H D n o s.mem) := by
  have ho : o < 16 := by rw [← h.ho]; exact Nat.mod_lt _ (by decide)
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.minK_ok s h.x25 h.x24 ho hn') fun s₁ ⟨x10₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  have hk1 : VG.Proof.AesGcm.AArch64.headLen o n ≤ n := Nat.min_le_right _ _
  have hk16 : o + VG.Proof.AesGcm.AArch64.headLen o n ≤ 16 := by have := Nat.min_le_left (16 - o) n; simp only [VG.Proof.AesGcm.AArch64.headLen]; omega
  have r₁ : VG.Proof.AesGcm.AArch64.Regs VG.Proof.AesGcm.AArch64.minRegs s s₁ := ⟨g₁, m₁, sp₁, rd₁, wr₁⟩
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, r₂⟩ : ∃ s₂, runBlock isa
      [.add .x .x11 .x20 .x25, ptr .x11 .x11 32, mov .x12 .x23, mov .x13 .x10] s₁ = some s₂ ∧
      s₂.gpr .x11 = St + BitVec.ofNat 64 (32 + o) ∧ s₂.gpr .x12 = D ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.headLen o n) ∧ VG.Proof.AesGcm.AArch64.Regs [.x11, .x12, .x13] s₁ s₂ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g₁ .x20 (by decide), g₁ .x25 (by decide), he.x20, h.x25, VG.Proof.AesGcm.AArch64.add_ofNat_assoc,
        Nat.add_comm]
    · simp [gpr_write, g₁ .x23 (by decide), h.x23]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hlp : VG.Proof.AesGcm.AArch64.LoopPre s₂ D (St + BitVec.ofNat 64 (32 + o)) (VG.Proof.AesGcm.AArch64.headLen o n) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₂.rd, r₂.wr, r₁.rd, r₁.wr]; exact (h.data.take hk1).rd
    · rw [r₂.wr, r₁.wr]; exact he.perm.stC (by omega)
    · exact (h.data.take hk1).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₂ x12₂ x11₂ x13₂ hlp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  rw [r₂.mem, r₁.mem] at m₃
  have hdk := VG.Proof.AesGcm.AArch64.length_bytesAt s.mem D (VG.Proof.AesGcm.AArch64.headLen o n)
  -- The block after the copy.
  have gg₃ : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs ++ [.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (List.mem_append_right _ h)), (r₁.comp r₂).others r
      (fun h => hr (List.mem_append_left _ h))]
  obtain ⟨s₄, run₄, x23₄, x24₄, x9₄, r₄⟩ : ∃ s₄, runBlock isa
      [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .add .x .x9 .x25 .x10, .subImm .x .x9 .x9 16] s₃ =
        some s₄ ∧
      s₄.gpr .x23 = D + BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.headLen o n) ∧ s₄.gpr .x24 = BitVec.ofNat 64 (n - VG.Proof.AesGcm.AArch64.headLen o n) ∧
      s₄.gpr .x9 = BitVec.ofNat 64 (o + VG.Proof.AesGcm.AArch64.headLen o n) - BitVec.ofNat 64 16 ∧ VG.Proof.AesGcm.AArch64.Regs [.x23, .x24, .x9] s₃ s₄ := by
    have e10 : s₃.gpr .x10 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.headLen o n) := by
      rw [g₃ _ (by decide), r₂.others _ (by decide), x10₁]
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e10, gg₃ .x23 (by decide), h.x23]
    · simp [gpr_write, e10, gg₃ .x24 (by decide), h.x24, VG.Proof.AesGcm.AArch64.ofNat_sub hk1 hn']
    · simp [gpr_write, e10, gg₃ .x25 (by decide), h.x25, VG.Proof.AesGcm.AArch64.ofNat_add_ofNat]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have ev : isa.eval (.zero .x .x9) s₄ = some (decide (o + VG.Proof.AesGcm.AArch64.headLen o n = 16)) := by
    show some (s₄.read .x .x9 == 0) = _
    rw [State.read, x9₄, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .x3 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.headBlocks o n) ∧ VG.Proof.AesGcm.AArch64.Regs [.x3] s₄ s₅)
    (WP.ite (decide (o + VG.Proof.AesGcm.AArch64.headLen o n = 16)) ev (fun ht => ?_) (fun hf => ?_)) fun s₅ ⟨x3₅, r₅⟩ => ?_)
  · have h16 : o + VG.Proof.AesGcm.AArch64.headLen o n = 16 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, VG.Proof.AesGcm.AArch64.headBlocks, h16], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h16 : o + VG.Proof.AesGcm.AArch64.headLen o n ≠ 16 := by simpa using hf
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, VG.Proof.AesGcm.AArch64.headBlocks, h16], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have gg₅ : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs ++ [.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs ++ [.x23, .x24, .x9, .x3] →
      s₅.gpr r = s.gpr r := fun r hr => by
    rw [r₅.others r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; simp [h])),
      r₄.others r (fun h => hr (List.mem_append_right _ (List.mem_append_left _ h))),
      gg₃ r (fun h => hr (List.mem_append_left _ h))]
  obtain ⟨s₆, run₆, x0₆, x1₆, x4₆, x2₆, r₆⟩ : ∃ s₆, runBlock isa (ghArgs yo ++ [ptr .x2 .x20 32]) s₅ = some s₆ ∧
      s₆.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₆.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₆.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₆.gpr .x2 = St + BitVec.ofNat 64 32 ∧
      VG.Proof.AesGcm.AArch64.Regs [.x0, .x1, .x4, .x2] s₅ s₆ := by
    have hyo' : yo < 4096 := by omega
    refine ⟨_, by rw [VG.Proof.AesGcm.AArch64.ghArgs_eq]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, gg₅ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₅ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₅ .x19 (by decide), he.x19]
    · simp [gpr_write, gg₅ .x20 (by decide), he.x20]
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have ggA : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs ++ [.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs ++ [.x23, .x24, .x9, .x3] ++
      [.x0, .x1, .x4, .x2] → s₆.gpr r = s.gpr r := fun r hr => by
    rw [r₆.others r (fun h => hr (List.mem_append_right _ h)), gg₅ r (fun h => hr (List.mem_append_left _ h))]
  have hm₆ : s₆.mem = writeBytes s.mem (St + BitVec.ofNat 64 (32 + o)) (bytesAt s.mem D (VG.Proof.AesGcm.AArch64.headLen o n)) := by
    rw [r₆.mem, r₅.mem, r₄.mem, m₃]
  have hsp₆ : s₆.sp = s.sp := by rw [r₆.sp, r₅.sp, r₄.sp, sp₃, r₂.sp, r₁.sp]
  have hrd₆ : s₆.rd = s.rd := by rw [r₆.rd, r₅.rd, r₄.rd, rd₃, r₂.rd, r₁.rd]
  have hwr₆ : s₆.wr = s.wr := by rw [r₆.wr, r₅.wr, r₄.wr, wr₃, r₂.wr, r₁.wr]
  have he₆ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₆ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp₆ hrd₆ hwr₆
  have hnf : VG.Proof.AesGcm.AArch64.headBlocks o n ≤ 1 := by simp only [VG.Proof.AesGcm.AArch64.headBlocks]; split <;> omega
  refine ⟨he₆, h.kept.of_eq fun r hr => ggA r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [r₆.others _ (by decide), r₅.others _ (by decide), x23₄],
    by rw [r₆.others _ (by decide), r₅.others _ (by decide), x24₄],
    by rw [ggA _ (by decide), h.x25], h.data.of_eq hrd₆ hwr₆, ?_, ?_, ?_⟩
  · refine VG.Proof.AesGcm.AArch64.ghCall_of L hyo he₆ x0₆ x1₆ x2₆ (by rw [r₆.others _ (by decide), x3₅]) x4₆ (by omega)
      (L.st_st (.inl (by omega)) (by omega) (by omega))
      (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (VG.Proof.AesGcm.AArch64.covers_left (he₆.perm.stC (by omega)))
  · rw [hm₆, show St + BitVec.ofNat 64 (32 + o) = St + BitVec.ofNat 64 32 + BitVec.ofNat 64 o from
      (VG.Proof.AesGcm.AArch64.add_ofNat_assoc _ _ _).symm]
    have := VG.Proof.AesGcm.AArch64.bytesAt_writeBytes s.mem (St + BitVec.ofNat 64 32) o (bytesAt s.mem D (VG.Proof.AesGcm.AArch64.headLen o n))
      (by rw [hdk]; omega)
    rwa [hdk] at this
  · rw [hm₆]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ hdk

omit L hyo in
theorem blocksAt_zero (m : Mem) (p : Addr) : blocksAt m p 0 = [] := rfl

omit L hyo in
theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

omit L hyo in
theorem frame_absFrame_buf {m m' : Mem} {o k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (VG.Proof.AesGcm.AArch64.absFrame St W yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem frame_absFrame_gh {m m' : Mem}
    (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩] m m') :
    Frame (VG.Proof.AesGcm.AArch64.absFrame St W yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The ghash frame keeps the hash subkey. -/
theorem hH_gh {s s' : State} {D : Addr} {nb : Nat}
    (g : GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) D (W + BitVec.ofNat 64 512) nb s') :
    blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame g.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.ctx_st (by decide) (by omega)
    · exact L.ctx_w (by decide) (by decide)

/-- The first call: the buffer absorbed if it is full. -/
theorem absCall1_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.AArch64.Abs1 Ctx St W SP k yo H D n o m₀ s) (hx : x.length % 16 = o)
    (hH₀ : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (ghCall v.callees) s (VG.Proof.AesGcm.AArch64.AbsMid Ctx St W SP k yo H x D n o m₀ (VG.Proof.AesGcm.AArch64.headLen o n)) := by
  have ho : o < 16 := by rw [← hx]; exact Nat.mod_lt _ (by decide)
  have hk1 : VG.Proof.AesGcm.AArch64.headLen o n ≤ n := Nat.min_le_right _ _
  have hk16 : o + VG.Proof.AesGcm.AArch64.headLen o n ≤ 16 := by have := Nat.min_le_left (16 - o) n; simp only [VG.Proof.AesGcm.AArch64.headLen]; omega
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hlen := VG.Proof.AesGcm.AArch64.length_bytesAt m₀ D (VG.Proof.AesGcm.AArch64.headLen o n)
  have hHs : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), hH₀]
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
  have gout := g.out
  rw [hHs, hY] at gout
  refine ⟨g.env h.env, h.kept.of_saved g.saved, hk1, by rw [g.saved _ (by decide) (by decide), h.x23],
    by rw [g.saved _ (by decide) (by decide), h.x24], by rw [g.saved _ (by decide) (by decide), h.x25],
    h.data.of_eq g.rd g.wr, by rw [VG.Proof.AesGcm.AArch64.hH_gh L hyo g, hHs], fun ha => ?_, ?_,
    (VG.Proof.AesGcm.AArch64.frame_absFrame_buf h.frame hk16).trans (VG.Proof.AesGcm.AArch64.frame_absFrame_gh g.frame)⟩
  · by_cases h16 : o + VG.Proof.AesGcm.AArch64.headLen o n = 16
    · rw [show VG.Proof.AesGcm.AArch64.headBlocks o n = 1 by simp [VG.Proof.AesGcm.AArch64.headBlocks, h16], VG.Proof.AesGcm.AArch64.blocksAt_one] at gout
      refine Proof.Gcm.absorb_complete ha (by rw [hlen, hx]; exact h16)
        (B := bytesAt s.mem (St + BitVec.ofNat 64 32) 16) ?_ gout
      rw [← h16, h.buf, ← hx, ha.2]
    · rw [show VG.Proof.AesGcm.AArch64.headBlocks o n = 0 by simp [VG.Proof.AesGcm.AArch64.headBlocks, h16], VG.Proof.AesGcm.AArch64.blocksAt_zero] at gout
      refine Proof.Gcm.absorb_fill ha (by rw [hlen, hx]; omega) gout ?_
      rw [hlen, hx, bytesAt_frame g.frame (fun r hr => ?_) (by omega), h.buf]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.st_st (.inr (by omega)) (by omega) (by omega)
      · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · by_cases h16 : o + VG.Proof.AesGcm.AArch64.headLen o n = 16
    · exact .inr (by omega)
    · exact .inl (by simp only [VG.Proof.AesGcm.AArch64.headLen] at h16 ⊢; omega)

/-- Before the second call: the arguments for the whole blocks. -/
theorem absSeg2_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.AbsMid Ctx St W SP k yo H x D n o m₀ j s) :
    WP isa (.block (absSeg2 yo)) s (VG.Proof.AesGcm.AArch64.Abs3 Ctx St W SP k yo H x D n o m₀ j) := by
  have hn' := h.data.lt
  have he := h.env
  have hyo' : yo < 4096 := by omega
  have hdj := (h.data.drop h.le).take (k := 16 * ((n - j) / 16)) (by omega)
  obtain ⟨s₁, run₁, x3₁, x2₁, x0₁, x1₁, x4₁, x23₁, x24₁, r₁⟩ : ∃ s₁, runBlock isa (absSeg2 yo) s = some s₁ ∧
      s₁.gpr .x3 = BitVec.ofNat 64 ((n - j) / 16) ∧ s₁.gpr .x2 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₁.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      s₁.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s₁.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      VG.Proof.AesGcm.AArch64.Regs [.x3, .x2, .x0, .x1, .x4, .x9, .x23, .x24] s s₁ := by
    refine ⟨_, by simp only [absSeg2, ghArgs]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, h.x24, VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega)]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), VG.Proof.AesGcm.AArch64.lsl4_ofNat,
        VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq,
        VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), VG.Proof.AesGcm.AArch64.lsl4_ofNat]
      rw [VG.Proof.AesGcm.AArch64.ofNat_sub (by omega) (by omega)]
      congr 1
      omega
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ := he.of_regs r₁
  refine ⟨he₁, h.kept.of_others r₁.others, h.le, x23₁, x24₁, by rw [r₁.others _ (by decide)]; exact h.x25,
    h.data.of_eq r₁.rd r₁.wr, by rw [r₁.mem]; exact h.hH, fun ha => by rw [r₁.mem]; exact h.abs ha, h.whole,
    by rw [r₁.mem]; exact h.frame, ?_⟩
  exact VG.Proof.AesGcm.AArch64.ghCall_of L hyo he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by have := hdj.lt; omega)
    (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide)))
    (by rw [r₁.rd, r₁.wr]; exact hdj.rd)

/-- The second call: the whole blocks absorbed. -/
theorem absCall2_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.Abs3 Ctx St W SP k yo H x D n o m₀ j s) :
    WP isa (ghCall v.callees) s fun s' =>
      VG.Proof.AesGcm.AArch64.AbsMid Ctx St W SP k yo H x D n o m₀ (j + 16 * ((n - j) / 16)) s' ∧ n - (j + 16 * ((n - j) / 16)) < 16 := by
  have hm := h
  have hn' := hm.data.lt
  have hle := hm.le
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hdata : bytesAt s.mem D n = bytesAt m₀ D n :=
    bytesAt_frame hm.frame (VG.Proof.AesGcm.AArch64.data_absFrame hyo hm.data) (by omega)
  refine ⟨⟨g.env hm.env, hm.kept.of_saved g.saved, by omega, ?_, ?_, ?_, hm.data.of_eq g.rd g.wr,
    by rw [VG.Proof.AesGcm.AArch64.hH_gh L hyo g, hm.hH], fun ha => ?_, ?_, hm.frame.trans (VG.Proof.AesGcm.AArch64.frame_absFrame_gh g.frame)⟩, by omega⟩
  · rw [g.saved _ (by decide) (by decide), hm.x23]
  · rw [g.saved _ (by decide) (by decide), hm.x24]
  · rw [g.saved _ (by decide) (by decide), hm.x25]
  · have hb : ∀ (m m' : Mem) (_ : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩] m m')
        (q : Nat), q ≤ 16 → bytesAt m' (St + BitVec.ofNat 64 32) q = bytesAt m (St + BitVec.ofNat 64 32) q :=
      fun m m' hf q hq => bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.st_st (.inr (by omega)) (by omega) (by omega)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (by omega)
    have gout := g.out
    rw [hm.hH] at gout
    by_cases h0 : (n - j) / 16 = 0
    · rw [h0, VG.Proof.AesGcm.AArch64.blocksAt_zero, Proof.Gcm.ghashFrom_nil] at gout
      rw [h0, Nat.mul_zero, Nat.add_zero]
      exact (hm.abs ha).congr gout (hb _ _ g.frame _ (Nat.le_of_lt (Nat.mod_lt _ (by decide))))
    · have hw : (x.length + j) % 16 = 0 := hm.whole.resolve_left (by omega)
      have ex : x ++ bytesAt m₀ D (j + 16 * ((n - j) / 16)) =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * ((n - j) / 16)) := by
        rw [VG.Proof.AesGcm.AArch64.bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (hm.abs ha) (by simp [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega)
        (by simp [VG.Proof.AesGcm.AArch64.length_bytesAt]) ?_
      rw [gout, Proof.Gcm.blocksAt_eq]
      refine congrArg (fun l => ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 yo)) (Spec.Gcm.blocks l)) ?_
      have e₁ := congrArg (fun l => (l.drop j).take (16 * ((n - j) / 16))) hdata
      simp only [VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ hle, VG.Proof.AesGcm.AArch64.bytesAt_take _ _ (show 16 * ((n - j) / 16) ≤ n - j by omega)] at e₁
      exact e₁
  · by_cases h0 : (n - j) / 16 = 0
    · rw [h0, Nat.mul_zero, Nat.add_zero]; exact hm.whole
    · have hw : (x.length + j) % 16 = 0 := hm.whole.resolve_left (by omega)
      exact .inr (by omega)

/-- The last bytes, buffered. -/
theorem absTail_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.AbsMid Ctx St W SP k yo H x D n o m₀ j s) (hj : n - j < 16) :
    WP isa absTail s (VG.Proof.AesGcm.AArch64.AbsOut Ctx St W SP k yo H x (x ++ bytesAt m₀ D n) o m₀) := by
  have hn' := h.data.lt
  have he := h.env
  have hdj := h.data.drop h.le
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, r₁⟩ : ∃ s₁, runBlock isa [ptr .x11 .x20 32, mov .x12 .x23, mov .x13 .x24] s =
      some s₁ ∧ s₁.gpr .x11 = St + BitVec.ofNat 64 32 ∧ s₁.gpr .x12 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ VG.Proof.AesGcm.AArch64.Regs [.x11, .x12, .x13] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, he.x20]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₁ (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 32) (n - j) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₁.rd, r₁.wr]; exact hdj.rd
    · rw [r₁.wr]; exact he.perm.stC (by omega)
    · exact hdj.st.sub_right (Lay.stSub (by omega))
  refine WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [r₁.mem] at m₂
  have hlen := VG.Proof.AesGcm.AArch64.length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
  have fw : Frame [⟨St + BitVec.ofNat 64 32, n - j⟩] s.mem s₂.mem := by rw [m₂]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ hlen
  have gg : ∀ r, r ∉ [Reg.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r (fun h' => hr (List.mem_append_right _ h')), r₁.others r (fun h' => hr (List.mem_append_left _ h'))]
  refine ⟨he.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₂, r₁.sp]) (by rw [rd₂, r₁.rd]) (by rw [wr₂, r₁.wr]),
    h.kept.of_eq fun r hr => gg r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x25], fun ha => ?_, ?_⟩
  · have ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      have e₁ := congrArg (fun l => l.drop j)
        (bytesAt_frame h.frame (VG.Proof.AesGcm.AArch64.data_absFrame hyo h.data) (by omega) : bytesAt s.mem D n = bytesAt m₀ D n)
      simpa only [VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ h.le] using e₁
    have ex : x ++ bytesAt m₀ D n = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      rw [List.append_assoc, ← VG.Proof.AesGcm.AArch64.bytesAt_add, Nat.add_sub_cancel' h.le]
    rw [ex, ← ed]
    by_cases h0 : n - j = 0
    · rw [m₂, h0]
      simp only [bytesAt, List.range_zero, List.map_nil, writeBytes_nil, List.append_nil]
      exact h.abs ha
    · have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · exact blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
      · rw [m₂]; exact VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
  · exact h.frame.trans ((fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

/-- `absorb yo`. -/
theorem absorb_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {s : State} (h : VG.Proof.AesGcm.AArch64.AbsIn Ctx St W SP k H x D n o s) :
    WP isa (absorb v.callees yo) s (VG.Proof.AesGcm.AArch64.AbsOut Ctx St W SP k yo H x (x ++ bytesAt s.mem D n) o s.mem) :=
  WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.absSeg1_ok L hyo h) fun _ h₁ =>
  WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.absCall1_ok L hyo v h₁ h.ho h.hH) fun _ h₂ =>
  WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.absSeg2_ok L hyo h₂) fun _ h₃ =>
  WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.absCall2_ok L hyo v h₃) fun _ ⟨h₄, hlt⟩ => VG.Proof.AesGcm.AArch64.absTail_ok L hyo h₄ hlt))))

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Flush`. -/
section

/-!
# AES-GCM on AArch64: padding (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `padSeg yo src` copies the
`x25` bytes at `x12` (which `src` sets) into `T`, zeroed first, and sets up
the call of `vg_ghash` on it, or on no block if there are none
(`padSeg_ok`); the call absorbs it (`padCall_ok`). `flush yo` pads the
buffered bytes so (`flush_ok`). `lens yo ra rb` stores the lengths block
`[8 ra]₆₄ ‖ [8 rb]₆₄` in `T` and absorbs it (`lensSeg_ok`, `lensCall_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- Whether there are bytes to pad: the blocks of the call. -/
abbrev padBlocks (o : Nat) : Nat := if o = 0 then 0 else 1

/-- Before the call of a padding: the `o` bytes at `P` (in `m₀`) padded with
zeros in `T`. -/
structure Pad1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (P : Addr) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (W + BitVec.ofNat 64 96)
    (W + BitVec.ofNat 64 512) (VG.Proof.AesGcm.AArch64.padBlocks o)
  tb : bytesAt s.mem (W + BitVec.ofNat 64 96) 16 = bytesAt m₀ P o ++ zeros (16 - o)
  frame : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

/-- After a call of `vg_ghash` on `T` (or on nothing), from `m₀`. -/
structure TOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (Y : Block) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  out : blockAt s.mem (St + BitVec.ofNat 64 yo) = Y
  frame : Frame (VG.Proof.AesGcm.AArch64.tFrame St W yo) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

/-- Padding the `o` bytes at `P`, which `src` points `x12` at. -/
theorem padSeg_ok {k : Reg → BitVec 64} {src : List Instr} {P : Addr} {o : Nat} {s : State}
    (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o) (ho : o < 16)
    (hsrc : ∃ s₁, runBlock isa src s = some s₁ ∧ s₁.gpr .x12 = P ∧ VG.Proof.AesGcm.AArch64.Regs [.x12] s s₁)
    (hP : Covers [⟨P, o⟩] (s.rd ++ s.wr)) (hPW : (⟨P, o⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 16⟩) :
    WP isa (padSeg yo src) s (VG.Proof.AesGcm.AArch64.Pad1 Ctx St W SP k yo o P s.mem) := by
  obtain ⟨s₁, run₁, x12₁, r₁⟩ := hsrc
  have he₁ := he.of_regs r₁
  have w₁ := he₁.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he₁.perm.wW (show 104 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, m₂, x11₂, x13₂, x12₂, r₂⟩ : ∃ s₂, runBlock isa [imm .x9 0, .str .x .x9 .x19 tO,
      .str .x .x9 .x19 (tO + 8), ptr .x11 .x19 tO, mov .x13 .x25] s₁ = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₂.gpr .x11 = W + BitVec.ofNat 64 96 ∧ s₂.gpr .x13 = BitVec.ofNat 64 o ∧ s₂.gpr .x12 = P ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x11, .x13] s₁ s₂ ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [he₁.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, r₁.mem, VG.Proof.AesGcm.AArch64.add_ofNat_assoc]; rfl
    · simp [gpr_write, he₁.x19]
    · simp [gpr_write, r₁.others .x25 (by decide), h25]
    · simp [gpr_write, x12₁]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  obtain ⟨og₂, sp₂, rd₂, wr₂⟩ := r₂
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₂ P (W + BitVec.ofNat 64 96) o := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [rd₂, wr₂, r₁.rd, r₁.wr]; exact hP
    · rw [wr₂, r₁.wr]; exact he.perm.wC (by omega)
    · exact hPW.sub_right (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₂ x12₂ x11₂ x13₂ lp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  have gg₃ : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h' => hr (List.mem_append_right _ h')),
      og₂ r (fun h' => hr (List.mem_append_left _ (List.mem_append_right _ h'))),
      r₁.others r (fun h' => hr (List.mem_append_left _ (List.mem_append_left _ h')))]
  -- The blocks of the call.
  have ev : isa.eval (.zero .x .x25) s₃ = some (decide (o = 0)) :=
    VG.Proof.AesGcm.AArch64.eval_zero (by rw [gg₃ _ (by decide), h25]) (by omega)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .x3 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.padBlocks o) ∧ VG.Proof.AesGcm.AArch64.Regs [.x3] s₃ s₄)
    (WP.ite (decide (o = 0)) ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨x3₄, r₄⟩ => ?_)
  · have h0 : o = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, VG.Proof.AesGcm.AArch64.padBlocks, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : o ≠ 0 := by simpa using hf
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, VG.Proof.AesGcm.AArch64.padBlocks, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have gg₄ : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs ++ [.x3] → s₄.gpr r = s.gpr r := fun r hr => by
    rw [r₄.others r (fun h' => hr (List.mem_append_right _ h')), gg₃ r (fun h' => hr (List.mem_append_left _ h'))]
  obtain ⟨s₅, run₅, x0₅, x1₅, x4₅, x2₅, r₅⟩ : ∃ s₅, runBlock isa (ghArgs yo ++ [ptr .x2 .x19 tO]) s₄ = some s₅ ∧
      s₅.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₅.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₅.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₅.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      VG.Proof.AesGcm.AArch64.Regs [.x0, .x1, .x4, .x2] s₄ s₅ := by
    have hyo' : yo < 4096 := by omega
    refine ⟨_, by rw [VG.Proof.AesGcm.AArch64.ghArgs_eq]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, gg₄ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₄ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₄ .x19 (by decide), he.x19]
    · simp [gpr_write, gg₄ .x19 (by decide), he.x19]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have ggA : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs ++ [.x3] ++ [.x0, .x1, .x4, .x2] →
      s₅.gpr r = s.gpr r := fun r hr => by
    rw [r₅.others r (fun h' => hr (List.mem_append_right _ h')), gg₄ r (fun h' => hr (List.mem_append_left _ h'))]
  have hm₅ : s₅.mem = writeBytes s₂.mem (W + BitVec.ofNat 64 96) (bytesAt s₂.mem P o) := by
    rw [r₅.mem, r₄.mem, m₃]
  have hsp : s₅.sp = s.sp := by rw [r₅.sp, r₄.sp, sp₃, sp₂, r₁.sp]
  have hrd : s₅.rd = s.rd := by rw [r₅.rd, r₄.rd, rd₃, rd₂, r₁.rd]
  have hwr : s₅.wr = s.wr := by rw [r₅.wr, r₄.wr, wr₃, wr₂, r₁.wr]
  have he₅ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₅ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hPo : bytesAt s₂.mem P o = bytesAt s.mem P o :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hPW) (by omega)
  have hlen := VG.Proof.AesGcm.AArch64.length_bytesAt s₂.mem P o
  refine ⟨he₅, hk.of_eq fun r hr => ggA r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [ggA _ (by decide), h25], ?_, ?_, ?_⟩
  · have hnb : VG.Proof.AesGcm.AArch64.padBlocks o ≤ 1 := by simp only [VG.Proof.AesGcm.AArch64.padBlocks]; split <;> omega
    refine VG.Proof.AesGcm.AArch64.ghCall_of L hyo he₅ x0₅ x1₅ x2₅ (by rw [r₅.others _ (by decide), x3₄]) x4₅ (by omega)
      (L.st_w (by omega) (.inr ⟨by decide, by omega⟩)) (L.w_w (.inl (by omega)) (by omega) (by decide))
      (VG.Proof.AesGcm.AArch64.covers_left (he₅.perm.wC (by omega)))
  · rw [hm₅, VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hPo]
    congr 1
    have := VG.Proof.AesGcm.AArch64.zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
    rw [← m₂, show (16 : Nat) = o + (16 - o) by omega, VG.Proof.AesGcm.AArch64.bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · rw [hm₅]
    exact fz.trans ((VG.Proof.AesGcm.AArch64.writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- The call after a padding: `T` absorbed, if there were bytes. -/
theorem padCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o : Nat} {P : Addr} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.AArch64.Pad1 Ctx St W SP k yo o P m₀ s) :
    WP isa (ghCall v.callees) s (VG.Proof.AesGcm.AArch64.TOut Ctx St W SP k yo o
      (ghashFrom (blockAt m₀ (Ctx + BitVec.ofNat 64 240)) (blockAt m₀ (St + BitVec.ofNat 64 yo))
        (if o = 0 then [] else [ofBytes (bytesAt m₀ P o ++ zeros (16 - o))])) m₀) := by
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = blockAt m₀ (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x25], ?_, ?_⟩
  · rw [g.out, hH, hY]
    by_cases h0 : o = 0
    · simp only [VG.Proof.AesGcm.AArch64.padBlocks, h0, ↓reduceIte, VG.Proof.AesGcm.AArch64.blocksAt_zero]
    · simp only [VG.Proof.AesGcm.AArch64.padBlocks, h0, ↓reduceIte, VG.Proof.AesGcm.AArch64.blocksAt_one, blockAt, h.tb]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `flush yo`: the buffer, of `o = len(x) mod 16` bytes, padded and absorbed. -/
theorem flush_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {o : Nat} {s : State}
    (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o) (ho : x.length % 16 = o)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (flush v.callees yo) s fun s' => VG.Proof.AesGcm.AArch64.TOut Ctx St W SP k yo o (blockAt s'.mem (St + BitVec.ofNat 64 yo))
        s.mem s' ∧ blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
        Absorbed s'.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ zeros (padLen x.length))) := by
  have hlt : o < 16 := by rw [← ho]; exact Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 hlt
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    (VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by omega))) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.AesGcm.AArch64.padCall_ok L hyo v h₁) fun s₂ h₂ => ⟨{ h₂ with
                                                                 out := rfl }, ?_, fun ha => ?_⟩
  · rw [blockAt_frame h₂.frame (VG.Proof.AesGcm.AArch64.ctx_tFrame L hyo), hH]
  · have hB : bytesAt s₂.mem (St + BitVec.ofNat 64 32) o = bytesAt s.mem (St + BitVec.ofNat 64 32) o :=
      bytesAt_frame h₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.st_st (.inr (by omega)) (by omega) (by omega)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (by omega)
    by_cases h0 : o = 0
    · rw [Proof.Gcm.padLen_of_mod (by omega), Spec.Gcm.zeros, List.replicate_zero, List.append_nil]
      refine ha.congr ?_ (by rw [ho]; exact hB)
      rw [h₂.out]; simp only [h0, ↓reduceIte, Proof.Gcm.ghashFrom_nil]
    · refine Proof.Gcm.absorb_pad ha (by omega) (B := bytesAt s.mem (St + BitVec.ofNat 64 32) o ++ zeros (16 - o))
        (by rw [ho]) ?_
      rw [h₂.out, hH]; simp only [h0, ↓reduceIte]

omit L hyo in
theorem rev64_eq : AArch64.rev64 = byteRev64 := rfl

omit L hyo in
/-- The 8 bytes of `[8 r]₆₄`. -/
theorem le8_lens (x : BitVec 64) : Proof.Cmac.le8 (AArch64.rev64 (x <<< 3)) = Spec.Gcm.be64 (8 * x.toNat) := by
  rw [VG.Proof.AesGcm.AArch64.rev64_eq, Proof.Gcm.le8_byteRev64, VG.Proof.AesGcm.AArch64.lsl3_eq, BitVec.toNat_ofNat, Proof.Gcm.be64_mod]

/-- Before the call of `lens yo ra rb`: the lengths block in `T`. -/
structure Lens1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (a b : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (W + BitVec.ofNat 64 96)
    (W + BitVec.ofNat 64 512) 1
  tb : bytesAt s.mem (W + BitVec.ofNat 64 96) 16 = lensBlock a b
  frame : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

theorem lensSeg_ok {k : Reg → BitVec 64} {o : Nat} {ra rb : Reg} {s : State} (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s)
    (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o)
    (hrb : rb ≠ .x9) :
    WP isa (.block (lensSeg yo ra rb)) s
      (VG.Proof.AesGcm.AArch64.Lens1 Ctx St W SP k yo o (s.gpr ra).toNat (s.gpr rb).toNat s.mem) := by
  have w₁ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have hyo' : yo < 4096 := by omega
  obtain ⟨s₁, run₁, m₁, x3₁, x0₁, x1₁, x4₁, x2₁, r₁⟩ : ∃ s₁, runBlock isa (lensSeg yo ra rb) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (s.gpr ra <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (s.gpr rb <<< 3)) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₁.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₁.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x3, .x0, .x1, .x4, .x2] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [lensSeg, ghArgs]; arun [he.x19, w₁, w₂, hyo', hrb], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
    · simp [gpr_write]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, he.x19]
  obtain ⟨og, sp₁, rd₁, wr₁⟩ := r₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine ⟨he₁, hk.of_others og, by rw [og _ (by decide), h25], ?_, ?_, ?_⟩
  · exact VG.Proof.AesGcm.AArch64.ghCall_of L hyo he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by decide)
      (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (VG.Proof.AesGcm.AArch64.covers_left (he₁.perm.wC (by decide)))
  · rw [m₁, Proof.Cmac.bytesAt_store2, VG.Proof.AesGcm.AArch64.le8_lens, VG.Proof.AesGcm.AArch64.le8_lens]; rfl
  · rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _

/-- The call of `lens`: the lengths block absorbed. -/
theorem lensCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o a b : Nat} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.AArch64.Lens1 Ctx St W SP k yo o a b m₀ s) :
    WP isa (ghCall v.callees) s (VG.Proof.AesGcm.AArch64.TOut Ctx St W SP k yo o
      (ghashFrom (blockAt m₀ (Ctx + BitVec.ofNat 64 240)) (blockAt m₀ (St + BitVec.ofNat 64 yo))
        [ofBytes (lensBlock a b)]) m₀) := by
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = blockAt m₀ (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x25], ?_, ?_⟩
  · rw [g.out, hH, hY, VG.Proof.AesGcm.AArch64.blocksAt_one,
      show blockAt s.mem (W + BitVec.ofNat 64 96) = ofBytes (lensBlock a b) by rw [blockAt, h.tb]]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Crypt`. -/
section

/-!
# AES-GCM on AArch64: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `x24` bytes at `x23`, where `x25` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block and the
arguments for the whole blocks (`crSeg1_ok`), the whole blocks with
`vg_aes_ctr32` (`ctrCall1_ok`), the arguments for a new keystream block
(`crSeg2_ok`), a new keystream block if there are bytes left (`ctrCall2_ok`),
and the last bytes (`crTail_ok`); `crypt_ok` puts them together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state and `W`. -/
structure DataW (Ctx St W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  ok : VG.Proof.AesGcm.AArch64.DataOk St W s D n
  wr : Covers [⟨D, n⟩] s.wr
  ctx : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩

theorem DataW.of_eq {Ctx St W : Addr} {s s' : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.AArch64.DataW Ctx St W s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.drop {Ctx St W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n)
    {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.AArch64.DataW Ctx St W s (D + BitVec.ofNat 64 k) (n - k) :=
  ⟨h.ok.drop hk, VG.Proof.AesGcm.AArch64.covers_off h.wr (by omega) h.ok.lt, h.ctx.sub_right (Offset.sub_base D (by omega))⟩

theorem DataW.take {Ctx St W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n)
    {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D k :=
  ⟨h.ok.take hk, VG.Proof.AesGcm.AArch64.covers_prefix h.wr hk, h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m Ctx (16 * (R + 1)))

/-- The regions `crypt` writes. -/
abbrev crFrame (St W D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨St + BitVec.ofNat 64 48, 32⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]

/-- The bytes `crypt` XORs with the rest of the current keystream block. -/
abbrev crHead (o n : Nat) : Nat := if o = 0 then 0 else min (16 - o) n

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [VG.Proof.AesGcm.AArch64.bytesAt_add, VG.Proof.AesGcm.AArch64.bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, VG.Proof.AesGcm.AArch64.length_bytesAt]

theorem disjoint_zero_right {r : Region} {a : Addr} : r.Disjoint ⟨a, 0⟩ := fun _ _ h => by
  simp only [Region.Contains] at h; omega

theorem disjoint_zero_left {r : Region} {a : Addr} : (⟨a, 0⟩ : Region).Disjoint r := fun _ h _ => by
  simp only [Region.Contains] at h; omega

theorem zero_xor' (x : Block) : (0 : Block) ^^^ x = x := by simp

theorem mz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide

theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

/-- With a whole number of blocks, the keystream block does not matter. -/
theorem Ctr.of_aligned {m m' : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0) (hc : blockAt m' cb = blockAt m cb) :
    Ctr m' cb ks ciph icb n :=
  ⟨hc.trans h.1, fun h1 => absurd h0 h1⟩

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go, `R`
rounds. -/
structure CrIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R P : Nat) (D : Addr) (n : Nat) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m₀ s.mem

/-- Before the first call: `CrMid` but for `x23` and `x24`, which have moved
past the whole blocks, and the call's arguments. -/
structure Cr1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16))
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16)))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m₀ s.mem
  call : CtrCall s Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R
    ((n - j) / 16)

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + n)
  out : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D n = xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D n)
  frame : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.crFrame St W D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨Ctx, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.AArch64.ciphOf m' Ctx R = VG.Proof.AesGcm.AArch64.ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [VG.Proof.AesGcm.AArch64.ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

/-- The arguments of a call of `vg_aes_ctr32` on the counter block at
`St + 48`, `nb` blocks at `D'` (within the data, or the keystream block). -/
theorem ctrCall_of {R : Nat} {s : State} (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D' : Addr} {nb : Nat}
    (h0 : s.gpr .x0 = Ctx) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = St + BitVec.ofNat 64 48)
    (h3 : s.gpr .x3 = D') (h4 : s.gpr .x4 = BitVec.ofNat 64 nb) (h5 : s.gpr .x5 = W + BitVec.ofNat 64 512)
    (hwrap : D'.toNat + 16 * nb ≤ 2 ^ 64)
    (hkd : (⟨Ctx, 240⟩ : Region).Disjoint ⟨D', 16 * nb⟩)
    (hcd : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨D', 16 * nb⟩)
    (hds : (⟨D', 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩)
    (hdw : Covers [⟨D', 16 * nb⟩] s.wr) :
    CtrCall s Ctx (St + BitVec.ofNat 64 48) D' (W + BitVec.ofNat 64 512) R nb := by
  refine ⟨h0, h1, h2, h3, h4, h5, hR, hwrap, by omega,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)), hkd,
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    hcd, L.st_w (by decide) (.inr ⟨by decide, by decide⟩), hds, ?_, ?_⟩
  · refine VG.Proof.AesGcm.AArch64.covers_cons ?_ (VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by decide))) (VG.Proof.AesGcm.AArch64.covers_cons
      (VG.Proof.AesGcm.AArch64.covers_left hdw) (VG.Proof.AesGcm.AArch64.covers_left (he.perm.wC (by decide)))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
  · exact VG.Proof.AesGcm.AArch64.covers_cons (he.perm.stC (by decide)) (VG.Proof.AesGcm.AArch64.covers_cons hdw (he.perm.wC (by decide)))

omit L in
theorem ctrArgs_eq (rest : List Instr) :
    ctrArgs ++ rest = mov .x0 .x21 :: mov .x1 .x22 :: ptr .x2 .x20 48 :: ptr .x5 .x19 scrO :: rest := rfl

/-- The rest of the keystream block, and the arguments for the whole blocks. -/
theorem crSeg1_ok {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.CrIn Ctx St W SP k R P D n s) :
    WP isa crSeg1 s (VG.Proof.AesGcm.AArch64.Cr1 Ctx St W SP k R icb P D n s.mem (VG.Proof.AesGcm.AArch64.crHead (P % 16) n)) := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  have hkn : VG.Proof.AesGcm.AArch64.crHead (P % 16) n ≤ n := by
    simp only [VG.Proof.AesGcm.AArch64.crHead]; split
    · omega
    · exact Nat.min_le_right _ _
  have hk16 : P % 16 + VG.Proof.AesGcm.AArch64.crHead (P % 16) n ≤ 16 := by
    simp only [VG.Proof.AesGcm.AArch64.crHead]; split
    · omega
    · have := Nat.min_le_left (16 - P % 16) n; omega
  -- `x10 := crHead`.
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x10 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.crHead (P % 16) n) ∧
      VG.Proof.AesGcm.AArch64.Regs VG.Proof.AesGcm.AArch64.minRegs s s₁)
    (WP.ite (decide (P % 16 = 0)) (VG.Proof.AesGcm.AArch64.eval_zero h.x25 (by omega)) (fun ht => ?_) (fun hf => ?_))
    fun s₁ ⟨x10₁, r₁⟩ => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, VG.Proof.AesGcm.AArch64.crHead, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (VG.Proof.AesGcm.AArch64.minK_ok s h.x25 h.x24 hlt hn') fun s' ⟨x10', g', m', sp', rd', wr'⟩ =>
      ⟨by rw [x10']; simp [VG.Proof.AesGcm.AArch64.crHead, h0], ⟨g', m', sp', rd', wr'⟩⟩
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, r₂⟩ : ∃ s₂, runBlock isa
      [.add .x .x11 .x20 .x25, ptr .x11 .x11 64, mov .x12 .x23, mov .x13 .x10] s₁ = some s₂ ∧
      s₂.gpr .x11 = St + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .x12 = D ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.crHead (P % 16) n) ∧ VG.Proof.AesGcm.AArch64.Regs [.x11, .x12, .x13] s₁ s₂ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, r₁.others .x20 (by decide), r₁.others .x25 (by decide), he.x20, h.x25,
        VG.Proof.AesGcm.AArch64.add_ofNat_assoc, Nat.add_comm]
    · simp [gpr_write, r₁.others .x23 (by decide), h.x23]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have r₁₂ := r₁.comp r₂
  have hdk := h.data.take hkn
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₂ (St + BitVec.ofNat 64 (64 + P % 16)) D (VG.Proof.AesGcm.AArch64.crHead (P % 16) n) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₁₂.rd, r₁₂.wr]; exact VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by omega))
    · rw [r₁₂.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.xor_ok s₂ x11₂ x12₂ x13₂ lp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  rw [r₁₂.mem] at m₃
  have gg₃ : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs ++ [.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h' => hr (List.mem_append_right _ h')), r₁₂.others r (fun h' => hr (List.mem_append_left _ h'))]
  have e10 : s₃.gpr .x10 = BitVec.ofNat 64 (VG.Proof.AesGcm.AArch64.crHead (P % 16) n) := by
    rw [g₃ _ (by decide), r₂.others _ (by decide), x10₁]
  generalize hj : VG.Proof.AesGcm.AArch64.crHead (P % 16) n = j at *
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  obtain ⟨s₄, run₄, x3₄, x4₄, x0₄, x1₄, x2₄, x5₄, x23₄, x24₄, r₄⟩ : ∃ s₄, runBlock isa
      ([.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .lsr .x .x4 .x24 4, mov .x3 .x23] ++ ctrArgs ++
        [.lsl .x .x9 .x4 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9]) s₃ = some s₄ ∧
      s₄.gpr .x3 = D + BitVec.ofNat 64 j ∧ s₄.gpr .x4 = BitVec.ofNat 64 nb ∧ s₄.gpr .x0 = Ctx ∧
      s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₄.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * nb) ∧
      s₄.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * nb)) ∧
      VG.Proof.AesGcm.AArch64.Regs [.x23, .x24, .x4, .x3, .x0, .x1, .x2, .x5, .x9] s₃ s₄ := by
    have e23 := gg₃ .x23 (by decide); have e24 := gg₃ .x24 (by decide)
    refine ⟨_, by rw [List.append_assoc, VG.Proof.AesGcm.AArch64.ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e10, e23, h.x23]
    · simp [gpr_write, e10, e24, h.x24, VG.Proof.AesGcm.AArch64.ofNat_sub hkn hn', VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), hnb]
    · simp [gpr_write, gg₃ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₃ .x22 (by decide), h.x22]
    · simp [gpr_write, gg₃ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₃ .x19 (by decide), he.x19]
    · simp [gpr_write, e10, e23, e24, h.x23, h.x24, VG.Proof.AesGcm.AArch64.ofNat_sub hkn hn',
        VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), hnb, VG.Proof.AesGcm.AArch64.lsl4_ofNat, VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, e10, e24, h.x24, BitVec.setWidth_eq,
        VG.Proof.AesGcm.AArch64.ofNat_sub hkn hn', VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), hnb, VG.Proof.AesGcm.AArch64.lsl4_ofNat]
      rw [VG.Proof.AesGcm.AArch64.ofNat_sub (by omega) (by omega)]
      congr 1
      omega
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ggA : ∀ r, r ∉ VG.Proof.AesGcm.AArch64.minRegs ++ [.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs ++ [.x23, .x24, .x4, .x3, .x0, .x1, .x2, .x5, .x9] →
      s₄.gpr r = s.gpr r := fun r hr => by
    rw [r₄.others r (fun h' => hr (List.mem_append_right _ h')), gg₃ r (fun h' => hr (List.mem_append_left _ h'))]
  have hsp : s₄.sp = s.sp := by rw [r₄.sp, sp₃, r₁₂.sp]
  have hrd : s₄.rd = s.rd := by rw [r₄.rd, rd₃, r₁₂.rd]
  have hwr : s₄.wr = s.wr := by rw [r₄.wr, wr₃, r₁₂.wr]
  have he₄ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₄ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  have hd₄ : VG.Proof.AesGcm.AArch64.DataW Ctx St W s₄ D n := h.data.of_eq hrd hwr
  have hm₄ : s₄.mem = writeBytes s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j) := by
    rw [r₄.mem, m₃]
  have hxl := VG.Proof.AesGcm.AArch64.length_xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j
  have fw : Frame [⟨D, j⟩] s.mem s₄.mem := by rw [hm₄]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, j⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have hdj := (hd₄.drop hkn).take (k := 16 * nb) h16
  refine ⟨he₄, h.kept.of_eq fun r hr => ggA r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [ggA _ (by decide), h.x22], h.rounds, hkn, by rw [hnb]; exact x23₄, by rw [hnb]; exact x24₄,
    by rw [ggA _ (by decide), h.x25], hd₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [VG.Proof.AesGcm.AArch64.crHead, h0]
      subst hj0
      exact hc₀.congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
        (blockAt_frame fw fun r hr => (hdisjst r hr).2)
    · exact (hc₀.head h0 hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
        (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [VG.Proof.AesGcm.AArch64.crHead, h0]
      subst hj0
      rfl
    · have e := VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_self s.mem D (VG.Proof.AesGcm.AArch64.xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j)
        (by rw [hxl]; omega)
      rw [hxl] at e
      rw [hm₄, e, VG.Proof.AesGcm.AArch64.xorBytes]
      have := Proof.Gcm.ctr_head hc₀ h0 (d := bytesAt s.mem D j) (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; exact hk16)
      rw [VG.Proof.AesGcm.AArch64.length_bytesAt, VG.Proof.AesGcm.AArch64.add_ofNat_assoc] at this
      exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesGcm.AArch64.split_disj hkn hn').symm) (by omega)
  · by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [VG.Proof.AesGcm.AArch64.crHead, h0]
      exact .inr (by omega)
    · by_cases hkk : j = n
      · exact .inl (by omega)
      · refine .inr ?_
        rw [← hj] at hkk ⊢
        simp only [VG.Proof.AesGcm.AArch64.crHead, h0, ↓reduceIte] at hkk ⊢
        omega
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩
  · rw [hnb]
    exact VG.Proof.AesGcm.AArch64.ctrCall_of L he₄ h.rounds x0₄ x1₄ x2₄ x3₄ x4₄ x5₄ hdj.ok.wrap
      (hdj.ctx.sub_left (Region.sub_prefix (by decide))) (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
      (hdj.ok.w.sub_right (Lay.wSub (by decide))) hdj.wr

/-- The first call: the whole blocks. -/
theorem ctrCall1_ok (v : GcmImpl) {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.Cr1 Ctx St W SP k R icb P D n m₀ j s)
    (hc : VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) :
    WP isa (ctrCall v.callees) s fun s' =>
      VG.Proof.AesGcm.AArch64.CrMid Ctx St W SP k R icb P D n m₀ (j + 16 * ((n - j) / 16)) s' ∧ n - (j + 16 * ((n - j) / 16)) < 16 := by
  have hn' := h.data.ok.lt
  have hle := h.le
  refine WP.mono (ctr_call v.ctr h.call) fun s₃ g => ?_
  generalize hnb : (n - j) / 16 = nb at *
  have h16 : 16 * nb ≤ n - j := by omega
  have hdj := (h.data.drop h.le).take (k := 16 * nb) h16
  have gout : blocksAt s₃.mem (D + BitVec.ofNat 64 j) nb = Spec.Gcm.ctr32 (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R)
      (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem (D + BitVec.ofNat 64 j) nb) := by
    rw [← hc]; exact g.out
  have gctr := g.ctr
  -- The whole blocks, if there are any.
  have hcw : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
      bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
        xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j) (bytesAt s.mem (D + BitVec.ofNat 64 j) (16 * nb)) ∧
      Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j + 16 * nb) := by
    intro hc₀
    by_cases h0 : nb = 0
    · subst h0
      have hks : blockAt s₃.mem (St + BitVec.ofNat 64 64) = blockAt s.mem (St + BitVec.ofNat 64 64) :=
        blockAt_frame g.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact L.st_st (.inr (by decide)) (by decide) (by decide)
          · exact VG.Proof.AesGcm.AArch64.disjoint_zero_right
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      refine ⟨by simp [bytesAt, xorKs], ?_⟩
      simp only [Nat.mul_zero, Nat.add_zero]
      exact (h.ctr hc₀).congr (by rw [gctr]; rfl) hks
    · have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega)
      exact Proof.Gcm.ctr_whole (h.ctr hc₀) hw gout gctr
  refine ⟨⟨h.env.of_saved g.saved g.sp g.rd g.wr, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x22], h.rounds,
    by omega, by rw [g.saved _ (by decide) (by decide), h.x23, hnb],
    by rw [g.saved _ (by decide) (by decide), h.x24, hnb],
    by rw [g.saved _ (by decide) (by decide), h.x25], h.data.of_eq g.rd g.wr,
    fun hc₀ => by rw [← Nat.add_assoc]; exact (hcw hc₀).2, fun hc₀ => ?_, ?_, ?_, ?_⟩, by omega⟩
  · -- The bytes done.
    have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
        xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
      rw [(hcw hc₀).1]
      congr 1
      have e := congrArg (List.take (16 * nb)) h.rest
      rwa [VG.Proof.AesGcm.AArch64.bytesAt_take _ _ h16, VG.Proof.AesGcm.AArch64.bytesAt_take _ _ h16] at e
    have hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
      · exact VG.Proof.AesGcm.AArch64.split_disj (D := D) (j := j) (n := n) h.le hn' |>.sub_right (Region.sub_prefix (by omega))
      · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))) (by omega)
    exact VG.Proof.AesGcm.AArch64.done_append (hjd.trans (h.done hc₀)) hj16
  · -- The bytes left.
    have hdis : ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
        ⟨W + BitVec.ofNat 64 512, 2048⟩],
        (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
      have hrest := (h.data.drop (k := j + 16 * nb) (by omega))
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hrest.ok.st.sub_right (Lay.stSub (by decide))
      · rw [← VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
        have := VG.Proof.AesGcm.AArch64.split_disj (D := D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega)
        rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega] at this
        exact this.symm
      · exact hrest.ok.w.sub_right (Lay.wSub (by decide))
    rw [bytesAt_frame g.frame hdis (by omega)]
    have e := congrArg (List.drop (16 * nb)) h.rest
    rw [VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ h16, VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ h16, VG.Proof.AesGcm.AArch64.add_ofNat_assoc,
      show n - j - 16 * nb = n - (j + 16 * nb) by omega] at e
    exact e
  · by_cases h0 : n - j = 0
    · exact .inl (by omega)
    · exact .inr (by have := h.whole.resolve_left h0; omega)
  · refine h.frame.trans (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., (Offset.sub_base D (by omega))⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

end

/-- Before the second call: a zero keystream block if there are bytes left,
and the call's arguments. -/
structure Cr2 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  lt16 : n - j < 16
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j)
  ks0 : n - j ≠ 0 → blockAt s.mem (St + BitVec.ofNat 64 64) = 0
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m₀ s.mem
  call : CtrCall s Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R
    (if n - j = 0 then 0 else 1)

/-- After the second call: a new keystream block, if there are bytes left. -/
structure Cr3 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  le : j ≤ n
  lt16 : n - j < 16
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n
  ctr0 : n - j = 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j)
  ctr1 : n - j ≠ 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    ∃ mc : Mem, Ctr mc (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j) ∧
      blockAt s.mem (St + BitVec.ofNat 64 64) = VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R (blockAt mc (St + BitVec.ofNat 64 48)) ∧
      blockAt s.mem (St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt mc (St + BitVec.ofNat 64 48))
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- The arguments for a new keystream block. -/
theorem crSeg2_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.CrMid Ctx St W SP k R icb P D n m₀ j s) (hj : n - j < 16) :
    WP isa crSeg2 s (VG.Proof.AesGcm.AArch64.Cr2 Ctx St W SP k R icb P D n m₀ j) := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have he := h.env
  have w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x4 = BitVec.ofNat 64 (if n - j = 0 then 0 else 1) ∧
      VG.Proof.AesGcm.AArch64.Others [.x4, .x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      (n - j = 0 → s₁.mem = s.mem) ∧
      (n - j ≠ 0 → s₁.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (St + BitVec.ofNat 64 72) (0 : BitVec 64)))
    (WP.ite (decide (n - j = 0)) (VG.Proof.AesGcm.AArch64.eval_zero h.x24 (by omega)) (fun ht => ?_) (fun hf => ?_))
    fun s₁ ⟨x4₁, g₁, sp₁, rd₁, wr₁, m0₁, m1₁⟩ => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      exact ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun _ => rfl, fun h' => absurd h0 h'⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.run ⟨_, by arun [he.x20, w₁, w₂], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun h' => absurd h' h0, fun _ => ?_⟩
      simp only [mem_write]
      rfl
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x5₂, x3₂, r₂⟩ : ∃ s₂, runBlock isa (ctrArgs ++ [ptr .x3 .x20 64]) s₁ =
      some s₂ ∧ s₂.gpr .x0 = Ctx ∧ s₂.gpr .x1 = BitVec.ofNat 64 R ∧ s₂.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x3 = St + BitVec.ofNat 64 64 ∧
      VG.Proof.AesGcm.AArch64.Regs [.x0, .x1, .x2, .x5, .x3] s₁ s₂ := by
    refine ⟨_, by rw [VG.Proof.AesGcm.AArch64.ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g₁ .x21 (by decide), he.x21]
    · simp [gpr_write, g₁ .x22 (by decide), h.x22]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
    · simp [gpr_write, g₁ .x19 (by decide), he.x19]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have gg : ∀ r, r ∉ [Reg.x4, .x9] ++ [.x0, .x1, .x2, .x5, .x3] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (fun h' => hr (List.mem_append_right _ h')), g₁ r (fun h' => hr (List.mem_append_left _ h'))]
  have hsp : s₂.sp = s.sp := by rw [r₂.sp, sp₁]
  have hrd : s₂.rd = s.rd := by rw [r₂.rd, rd₁]
  have hwr : s₂.wr = s.wr := by rw [r₂.wr, wr₁]
  have he₂ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₂ := he.keep (fun r hr => gg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  -- The memory: the keystream block zeroed if there are bytes left.
  have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [r₂.mem]
    by_cases h0 : n - j = 0
    · rw [m0₁ h0]; exact Frame.refl _ _
    · rw [m1₁ h0, show St + BitVec.ofNat 64 72 = St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
        rw [BitVec.add_assoc]; rfl]
      exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ r ∈ [(⟨St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.data.ok.st.sub_right (Lay.stSub (by decide))
  have hdD : ∀ (q : Addr) (l : Nat), Region.Sub ⟨q, l⟩ ⟨D, n⟩ → l ≤ n → bytesAt s₂.mem q l = bytesAt s.mem q l :=
    fun q l hs hl => bytesAt_frame fz (fun r hr => (dD r hr).sub_left hs) (by omega)
  refine ⟨he₂, h.kept.of_eq fun r hr => gg r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x22], h.rounds, h.le, hj, by rw [gg _ (by decide), h.x23],
    by rw [gg _ (by decide), h.x24], by rw [gg _ (by decide), h.x25], h.data.of_eq hrd hwr, fun hc₀ => ?_, ?_,
    fun hc₀ => by rw [hdD _ _ (Region.sub_prefix h.le) h.le]; exact h.done hc₀,
    by rw [hdD _ _ (Offset.sub_base D (by omega)) (by omega)]; exact h.rest, h.whole,
    h.frame.trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩), ?_⟩
  · have hcb : blockAt s₂.mem (St + BitVec.ofNat 64 48) = blockAt s.mem (St + BitVec.ofNat 64 48) :=
      blockAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by decide)) (by decide) (by decide)
    by_cases h0 : n - j = 0
    · exact (h.ctr hc₀).congr hcb (by rw [r₂.mem, m0₁ h0])
    · exact Ctr.of_aligned (h.ctr hc₀) (h.whole.resolve_left h0) hcb
  · intro h0
    rw [r₂.mem, m1₁ h0, show St + BitVec.ofNat 64 72 = St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc]; rfl, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · have hnb : (if n - j = 0 then 0 else 1) ≤ 1 := by split <;> omega
    exact VG.Proof.AesGcm.AArch64.ctrCall_of L he₂ h.rounds x0₂ x1₂ x2₂ x3₂ (by rw [r₂.others _ (by decide), x4₁]) x5₂
      (by have := L.sw; rw [BitVec.toNat_add, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by decide)]; omega)
      ((L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by omega)))
      (L.st_st (.inl (by decide)) (by decide) (by omega))
      (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (he₂.perm.stC (by omega))

/-- The second call: a new keystream block, if there are bytes left. -/
theorem ctrCall2_ok (v : GcmImpl) {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.Cr2 Ctx St W SP k R icb P D n m₀ j s)
    (hc : VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) :
    WP isa (ctrCall v.callees) s (VG.Proof.AesGcm.AArch64.Cr3 Ctx St W SP k R icb P D n m₀ j) := by
  have hn' := h.data.ok.lt
  have hle := h.le
  refine WP.mono (ctr_call v.ctr h.call) fun s₃ g => ?_
  have dD : ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨St + BitVec.ofNat 64 64, 16 * (if n - j = 0 then 0 else 1)⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.data.ok.st.sub_right (Lay.stSub (by decide))
    · exact h.data.ok.st.sub_right (Lay.stSub (by split <;> omega))
    · exact h.data.ok.w.sub_right (Lay.wSub (by decide))
  have hdD : ∀ (q : Addr) (l : Nat), Region.Sub ⟨q, l⟩ ⟨D, n⟩ → l ≤ n → bytesAt s₃.mem q l = bytesAt s.mem q l :=
    fun q l hs hl => bytesAt_frame g.frame (fun r hr => (dD r hr).sub_left hs) (by omega)
  refine ⟨h.env.of_saved g.saved g.sp g.rd g.wr, h.kept.of_saved g.saved, h.le, h.lt16,
    by rw [g.saved _ (by decide) (by decide), h.x23], by rw [g.saved _ (by decide) (by decide), h.x24],
    by rw [g.saved _ (by decide) (by decide), h.x25], h.data.of_eq g.rd g.wr, fun h0 hc₀ => ?_,
    fun h0 hc₀ => ?_,
    fun hc₀ => by rw [hdD _ _ (Region.sub_prefix h.le) h.le]; exact h.done hc₀,
    by rw [hdD _ _ (Offset.sub_base D (by omega)) (by omega)]; exact h.rest, h.whole,
    h.frame.trans (g.frame.sub fun r hr => ?_)⟩
  · have gc := g.ctr
    simp only [h0, ↓reduceIte] at gc
    have hks : blockAt s₃.mem (St + BitVec.ofNat 64 64) = blockAt s.mem (St + BitVec.ofNat 64 64) :=
      blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.st_st (.inr (by decide)) (by decide) (by decide)
        · simp only [h0, ↓reduceIte]; exact VG.Proof.AesGcm.AArch64.disjoint_zero_right
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    exact (h.ctr hc₀).congr gc hks
  · refine ⟨s.mem, h.ctr hc₀, ?_, ?_⟩
    · have go := g.out
      simp only [h0, ↓reduceIte, VG.Proof.AesGcm.AArch64.blocksAt_one, VG.Proof.AesGcm.AArch64.ctr32_single, List.cons.injEq, and_true] at go
      rw [go, h.ks0 h0, VG.Proof.AesGcm.AArch64.zero_xor', show Spec.Gcm.aesWith R (bytesAt s.mem Ctx (16 * (R + 1))) =
        VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R from rfl, hc]
    · have gc := g.ctr
      simp only [h0, ↓reduceIte] at gc
      rw [gc]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by split <;> omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

omit L in
/-- The last bytes, with the new keystream block. -/
theorem crTail_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : VG.Proof.AesGcm.AArch64.Cr3 Ctx St W SP k R icb P D n m₀ j s) :
    WP isa crTail s (VG.Proof.AesGcm.AArch64.CrOut Ctx St W SP k R icb P D n m₀) := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have hj := h.lt16
  have he := h.env
  have hdj := h.data.drop h.le
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, r₁⟩ : ∃ s₁, runBlock isa [ptr .x11 .x20 64, mov .x12 .x23, mov .x13 .x24] s =
      some s₁ ∧ s₁.gpr .x11 = St + BitVec.ofNat 64 64 ∧ s₁.gpr .x12 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ VG.Proof.AesGcm.AArch64.Regs [.x11, .x12, .x13] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, he.x20]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₁ (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₁.rd, r₁.wr]; exact VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by omega))
    · rw [r₁.wr]; exact hdj.wr
    · exact (hdj.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (VG.Proof.AesGcm.AArch64.xor_ok s₁ x11₁ x12₁ x13₁ lp) fun s₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [r₁.mem] at m₂
  have hxl := VG.Proof.AesGcm.AArch64.length_xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s.mem s₂.mem := by rw [m₂]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ hxl
  have gg : ∀ r, r ∉ [Reg.x11, .x12, .x13] ++ VG.Proof.AesGcm.AArch64.loopRegs → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r (fun h' => hr (List.mem_append_right _ h')), r₁.others r (fun h' => hr (List.mem_append_left _ h'))]
  have dst : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdj.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have hD : bytesAt s₂.mem D j = bytesAt s.mem D j := bytesAt_frame fw (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.AArch64.split_disj h.le hn') (by omega)
  -- The tail, from a new keystream block.
  have htail : n - j ≠ 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
      bytesAt s₂.mem (D + BitVec.ofNat 64 j) (n - j) =
        xorKs (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) ∧
      Ctr s₂.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + n) := by
    intro h0 hc₀
    obtain ⟨mc, hmc, hks, hcb⟩ := h.ctr1 h0 hc₀
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left h0
    obtain ⟨t₁, t₂⟩ := Proof.Gcm.ctr_tail hmc hw hks hcb (d := bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j))
      (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega) (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega)
    rw [VG.Proof.AesGcm.AArch64.length_bytesAt] at t₁ t₂
    refine ⟨?_, ?_⟩
    · have e := VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_self s.mem (D + BitVec.ofNat 64 j)
        (VG.Proof.AesGcm.AArch64.xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega)
      rw [hxl] at e
      rw [m₂, e, VG.Proof.AesGcm.AArch64.xorBytes, t₁, h.rest]
    · rw [show P + n = P + j + (n - j) by omega]
      exact t₂.congr (blockAt_frame fw fun r hr => (dst r hr).1) (blockAt_frame fw fun r hr => (dst r hr).2)
  refine ⟨he.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₂, r₁.sp]) (by rw [rd₂, r₁.rd]) (by rw [wr₂, r₁.wr]),
    h.kept.of_eq fun r hr => gg r (by
      simp only [VG.Proof.AesGcm.AArch64.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x25], fun hc₀ => ?_, fun hc₀ => ?_, ?_⟩
  · by_cases h0 : n - j = 0
    · have hjn : j = n := by omega
      subst hjn
      exact (h.ctr0 h0 hc₀).congr (blockAt_frame fw fun r hr => (dst r hr).1)
        (blockAt_frame fw fun r hr => (dst r hr).2)
    · exact (htail h0 hc₀).2
  · by_cases h0 : n - j = 0
    · have hjn : j = n := by omega
      subst hjn
      rw [hD]; exact h.done hc₀
    · rw [show n = j + (n - j) by omega]
      exact VG.Proof.AesGcm.AArch64.done_append (hD.trans (h.done hc₀)) (htail h0 hc₀).1
  · exact h.frame.trans (fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base D (by omega)⟩)

/-- `crypt`. -/
theorem crypt_ok (v : GcmImpl) {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.CrIn Ctx St W SP k R P D n s) :
    WP isa (crypt v.callees) s (VG.Proof.AesGcm.AArch64.CrOut Ctx St W SP k R icb P D n s.mem) := by
  have hc : ∀ {m' : Mem}, Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) s.mem m' → VG.Proof.AesGcm.AArch64.ciphOf m' Ctx R = VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R :=
    fun hf => VG.Proof.AesGcm.AArch64.ciph_frame hf (VG.Proof.AesGcm.AArch64.ctx_crFrame L h.data) h.rounds
  exact WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.crSeg1_ok L (icb := icb) h) fun s₁ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.ctrCall1_ok L v h₁ (hc h₁.frame)) fun s₂ ⟨h₂, hlt⟩ =>
    WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.crSeg2_ok L h₂ hlt) fun s₃ h₃ =>
    WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.ctrCall2_ok L v h₃ (hc h₃.frame)) fun s₄ h₄ => VG.Proof.AesGcm.AArch64.crTail_ok h₄))))

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Tag`. -/
section

/-!
# AES-GCM on AArch64: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `x26` and `x27` bytes (`lensSeg_ok`, `lensCall_ok`), copies the
accumulator `S` to `W + o` (`tagSeg_ok`) and XORs `CIPH_K(J₀)` into it with
`vg_aes_ctr32`, from the counter block `J₀` at the state (`tagCall_ok`);
`tag_ok` puts them together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W : Addr) (o : Nat) : List Region :=
  [⟨St, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]

/-- Before the call of `tag o`: the accumulator `Y` copied to `W + o`, `J` at
the state. -/
structure Tag1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (o R : Nat) (Y J : Block) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  call : CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  cp : blockAt s.mem (W + BitVec.ofNat 64 o) = Y
  hJ : blockAt s.mem St = J
  frame : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] m₀ s.mem

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (after the
lengths block) and the counter block `J`. -/
structure TagOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (o R : Nat) (Y J : Block) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 = toBytes (Y ^^^ VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R J)
  frame : Frame (VG.Proof.AesGcm.AArch64.tagFrame St W o) m₀ s.mem

theorem bytesAt_copy2 (m : Mem) {p q : Addr} (hd : (⟨p, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    bytesAt ((m.writeW p (m.readW q 64)).writeW (p + BitVec.ofNat 64 8)
      ((m.writeW p (m.readW q 64)).readW (q + BitVec.ofNat 64 8) 64)) p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep (Region.Disjoint.sep hd.symm (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide), Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- The accumulator copied, and the arguments of the call. -/
theorem tagSeg_ok {k : Reg → BitVec 64} {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s)
    (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.block (tagSeg o)) s (VG.Proof.AesGcm.AArch64.Tag1 Ctx St W SP k o R (blockAt s.mem (St + BitVec.ofNat 64 16))
      (blockAt s.mem St) s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have r₁ := he.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 24 + 8 ≤ 80 by decide)
  have w₁ := he.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have ho8 : (o + 8) % 8 = 0 ∧ o + 8 < 32768 := by omega
  have ho0 : o % 8 = 0 ∧ o < 32768 := by omega
  have ho' : o < 4096 := by omega
  have dsep : (⟨W + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8, 8⟩ := by
    rw [VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
    exact (L.st_w (a := 24) (n := 8) (by decide) (by omega)).symm
  obtain ⟨s₁, run₁, m₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, og, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (tagSeg o) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 o) (s.mem.readW (St + BitVec.ofNat 64 16) 64)).writeW
        (W + BitVec.ofNat 64 (o + 8))
        ((s.mem.writeW (W + BitVec.ofNat 64 o) (s.mem.readW (St + BitVec.ofNat 64 16) 64)).readW
          (St + BitVec.ofNat 64 24) 64) ∧
      s₁.gpr .x0 = Ctx ∧ s₁.gpr .x1 = BitVec.ofNat 64 R ∧ s₁.gpr .x2 = St ∧
      s₁.gpr .x3 = W + BitVec.ofNat 64 o ∧ s₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x5 = W + BitVec.ofNat 64 512 ∧ VG.Proof.AesGcm.AArch64.Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [tagSeg]; arun [he.x19, he.x20, r₁, r₂, w₁, w₂, ho8, ho0, ho'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, Mem.readW, BitVec.setWidth_eq]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, h22]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write]
    · simp [gpr_write, he.x19]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  rw [show W + BitVec.ofNat 64 (o + 8) = W + BitVec.ofNat 64 o + BitVec.ofNat 64 8 from (VG.Proof.AesGcm.AArch64.add_ofNat_assoc ..).symm,
    show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by rw [VG.Proof.AesGcm.AArch64.add_ofNat_assoc]] at m₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dJo : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  refine ⟨he₁, hk.of_others og, ?_, ?_, ?_, f₁⟩
  · refine ⟨x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, hR,
      by have := L.ww; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, by decide,
      by simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      dJo, by simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩),
      L.w_w (by omega) (by omega) (by decide), ?_, ?_⟩
    · refine VG.Proof.AesGcm.AArch64.covers_cons ?_ (VG.Proof.AesGcm.AArch64.covers_cons ?_ (VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_left (he₁.perm.wC (by omega)))
        (VG.Proof.AesGcm.AArch64.covers_left (he₁.perm.wC (by decide)))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₁.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using VG.Proof.AesGcm.AArch64.covers_left (he₁.perm.stC (d := 0) (n := 16) (by decide))
    · exact VG.Proof.AesGcm.AArch64.covers_cons (by simpa using he₁.perm.stC (d := 0) (n := 16) (by decide))
        (VG.Proof.AesGcm.AArch64.covers_cons (he₁.perm.wC (by omega)) (he₁.perm.wC (by decide)))
  · rw [blockAt, m₁, VG.Proof.AesGcm.AArch64.bytesAt_copy2 _ dsep]; rfl
  · exact blockAt_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo

/-- The call of `tag o`: `CIPH_K(J)` XORed into the copy. -/
theorem tagCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o R : Nat} (ho : o = 0 ∨ o = 112) {Y J : Block}
    {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.AArch64.Tag1 Ctx St W SP k o R Y J m₀ s) :
    WP isa (ctrCall v.callees) s (VG.Proof.AesGcm.AArch64.TagOut Ctx St W SP k o R Y J m₀) := by
  refine WP.mono (ctr_call v.ctr h.call) fun s₃ g => ?_
  have gout := g.out
  rw [VG.Proof.AesGcm.AArch64.blocksAt_one, VG.Proof.AesGcm.AArch64.blocksAt_one, VG.Proof.AesGcm.AArch64.ctr32_single, List.cons.injEq] at gout
  have hc : VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R :=
    VG.Proof.AesGcm.AArch64.ciph_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) h.call.rounds
  refine ⟨h.env.of_saved g.saved g.sp g.rd g.wr, h.kept.of_saved g.saved, ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt, gout.1, h.hJ, h.cp,
      show Spec.Gcm.aesWith R (bytesAt s.mem Ctx (16 * (R + 1))) = VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R from rfl, hc]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Region.sub_prefix (base := St) (show 16 ≤ 32 by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok (v : GcmImpl) {k : Reg → BitVec 64} {o o' R : Nat} (ho : o = 0 ∨ o = 112) {s : State}
    (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h25 : s.gpr .x25 = BitVec.ofNat 64 o') :
    WP isa (tag v.callees o) s (VG.Proof.AesGcm.AArch64.TagOut Ctx St W SP k o R
      (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (St + BitVec.ofNat 64 16))
        [ofBytes (lensBlock (s.gpr .x26).toNat (s.gpr .x27).toNat)]) (blockAt s.mem St) s.mem) := by
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.lensSeg_ok L (yo := 16) (.inr rfl) he hk h25 (by decide)) fun s₁ h₁ =>
    WP.mono (VG.Proof.AesGcm.AArch64.lensCall_ok L (.inr rfl) v h₁) fun s₂ h₂ => ?_))
  have dJ : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16, (⟨St, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
  have hJ₂ : blockAt s₂.mem St = blockAt s.mem St := blockAt_frame h₂.frame dJ
  have hc₂ : VG.Proof.AesGcm.AArch64.ciphOf s₂.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R := VG.Proof.AesGcm.AArch64.ciph_frame h₂.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))) hR
  have hk₂ := h₂.kept
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tagSeg_ok L ho h₂.env h₂.kept (by rw [hk₂ .x22 (by decide), ← hk .x22 (by decide), h22]) hR)
    fun s₃ h₃ => WP.mono (VG.Proof.AesGcm.AArch64.tagCall_ok L v ho h₃) fun s₄ h₄ => ?_)
  refine ⟨h₄.env, h₄.kept, ?_, ?_⟩
  · rw [h₄.out, hc₂, hJ₂, h₂.out]
  · refine (h₂.frame.sub fun r hr => ?_).trans (h₄.frame.sub fun r hr => ⟨r, hr, fun _ h => h⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.J0`. -/
section

/-!
# AES-GCM on AArch64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`x24`-byte nonce at `x23` to the state: its bytes and `0x00000001` if it is
12 bytes (`j012_ok`), else GHASH of its whole blocks (`j0Seg_ok`,
`j0Call1_ok`), of its last bytes padded (`padSeg_ok`, `padCall_ok`) and of the
lengths block (`lensSeg_ok`, `lensCall_ok`), `j0hash_ok`; then the first
counter block `inc₃₂(J₀)` and a zero accumulator (`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem ww32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem rev32_eq : AArch64.rev32 = byteRev32 := rfl

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Proof.Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32,
    Proof.Cmac.byteRev32_byteRev32] at h
  rw [h, Proof.Cmac.ofBytes_toBytes]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- `J₀` of a nonce other than 12 bytes, from GHASH of its whole blocks, its
last bytes padded and the lengths block. -/
theorem j0_split (h : Block) (m : Mem) (Np : Addr) {n : Nat} (hn : n ≠ 12) :
    Spec.Gcm.j0 h (bytesAt m Np n) =
      ghashFrom h (ghashFrom h (ghash h (blocks (bytesAt m Np (16 * (n / 16)))))
        (if n % 16 = 0 then [] else
          [ofBytes (bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))]))
        [ofBytes (lensBlock 0 n)] := by
  rw [Proof.Gcm.j0_eq h (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; exact hn), VG.Proof.AesGcm.AArch64.length_bytesAt]
  congr 1
  rw [show bytesAt m Np n = bytesAt m Np (16 * (n / 16)) ++ bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)
      by rw [← VG.Proof.AesGcm.AArch64.bytesAt_add]; congr 1; omega, List.append_assoc,
    Proof.Gcm.blocks_append (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega), ghash, Proof.Gcm.ghashFrom_append]
  by_cases h0 : n % 16 = 0
  · rw [Proof.Gcm.padLen_of_mod h0]
    simp only [h0, ↓reduceIte]
    rw [show bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) 0 ++ zeros 0 = [] from rfl, Proof.Gcm.blocks_nil]
    rfl
  · simp only [h0, ↓reduceIte]
    rw [show padLen n = 16 - n % 16 by simp only [padLen]; omega,
      Proof.Gcm.blocks_single (bs := bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))
        (by rw [List.length_append, VG.Proof.AesGcm.AArch64.length_bytesAt, Proof.Gcm.length_zeros]; omega)]
    rfl

/-- The regions `j0` writes. -/
abbrev j0Frame (St W : Addr) : List Region :=
  [⟨St, 80⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- Before `j0`: the `n`-byte nonce at `Np`, its length also in `x26` and 0 in
`x27`. -/
structure J0In (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  data : VG.Proof.AesGcm.AArch64.DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Before the first call of `j0hash`: a zero accumulator, and the call on the
whole blocks of the nonce. -/
structure J1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : VG.Proof.AesGcm.AArch64.DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y0 : blockAt s.mem (St + BitVec.ofNat 64 0) = 0
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 0) Np (W + BitVec.ofNat 64 512) (n / 16)
  frame : Frame [⟨St, 16⟩] m₀ s.mem

/-- After the first call: the whole blocks absorbed. -/
structure J2 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : VG.Proof.AesGcm.AArch64.DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y : blockAt s.mem (St + BitVec.ofNat 64 0) = ghash H (blocks (bytesAt m₀ Np (16 * (n / 16))))
  iv : bytesAt s.mem Np n = bytesAt m₀ Np n
  frame : Frame (VG.Proof.AesGcm.AArch64.j0Frame St W) m₀ s.mem

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  frame : Frame (VG.Proof.AesGcm.AArch64.j0Frame St W) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (VG.Proof.AesGcm.AArch64.j0Frame St W) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

theorem ctx_j0Frame : ∀ r ∈ VG.Proof.AesGcm.AArch64.j0Frame St W, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (VG.Proof.AesGcm.AArch64.j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (VG.Proof.AesGcm.AArch64.tFrame St W 0) m m') : Frame (VG.Proof.AesGcm.AArch64.j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {s : State} (h : VG.Proof.AesGcm.AArch64.J0In Ctx St W SP k H Np 12 s) :
    WP isa (.block j012) s (VG.Proof.AesGcm.AArch64.J0Mid Ctx St W SP k H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have hd := h.data
  have r₀ := VG.Proof.AesGcm.AArch64.in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := VG.Proof.AesGcm.AArch64.in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := VG.Proof.AesGcm.AArch64.in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  rw [VG.Proof.AesGcm.AArch64.add_ofNat_zero] at r₀ w₀
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem St (s.mem.readW Np 32) (s.mem.readW (Np + BitVec.ofNat 64 4) 32)
        (s.mem.readW (Np + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [j012]; arun [h.x23, he.x20, r₀, r₁, r₂, w₀, w₁, w₂, w₃, VG.Proof.AesGcm.AArch64.add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, VG.Proof.AesGcm.AArch64.ww32, BitVec.setWidth_eq]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm, VG.Proof.AesGcm.AArch64.add_ofNat_zero]; exact Proof.Cmac.frame_store4 (m := s.mem) St _ _ _ _
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og, ?_, ?_, VG.Proof.AesGcm.AArch64.st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, VG.Proof.AesGcm.AArch64.bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, VG.Proof.AesGcm.AArch64.bytesAt_add,
        VG.Proof.AesGcm.AArch64.add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _), blockAt, hm, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, VG.Proof.AesGcm.AArch64.le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {k : Reg → BitVec 64} {H : Block} {iv : List Byte} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.AArch64.J0Mid Ctx St W SP k H iv m₀ s) :
    WP isa (.block initState) s (VG.Proof.AesGcm.AArch64.J0Out Ctx St W SP k H iv m₀) := by
  have he := h.env
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 24 + 8 ≤ 80 by decide)
  rw [VG.Proof.AesGcm.AArch64.add_ofNat_zero] at r₀
  generalize hw : s.mem.readW (St + BitVec.ofNat 64 12) 32 = w
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa initState s = some s' ∧
      s'.mem = ((store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32) (s.mem.readW (St + BitVec.ofNat 64 4) 32)
        (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))).writeW (St + BitVec.ofNat 64 16)
          (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 24) (0 : BitVec 64) ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [initState]; arun [he.x20, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, z₀, z₁, VG.Proof.AesGcm.AArch64.add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, VG.Proof.AesGcm.AArch64.ww32, BitVec.setWidth_eq, ← hw, VG.Proof.AesGcm.AArch64.rev32_eq, VG.Proof.AesGcm.AArch64.add_ofNat_assoc]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f₄ := Proof.Cmac.frame_store4 (m := s.mem) (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))
  have fz := Proof.Cmac.frame_store2 (m := store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1)))
    (St + BitVec.ofNat 64 16) 0 0
  rw [VG.Proof.AesGcm.AArch64.add_ofNat_assoc, ← hm] at fz
  have dz : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16, 16⟩ :=
    L.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨St + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem St = blockAt s.mem St := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide) (by decide))]
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og,
    ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (VG.Proof.AesGcm.AArch64.st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [VG.Proof.AesGcm.AArch64.add_ofNat_assoc], Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← h.j0, blockAt,
      Proof.Cmac.ofBytes_rev4, ← Proof.Cmac.le4_readW s.mem St, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW,
      VG.Proof.AesGcm.AArch64.ofBytes_le4, hw, Proof.Cmac.byteRev32_byteRev32, VG.Proof.AesGcm.AArch64.inc32_words]

/-- The accumulator zeroed and the arguments for the whole blocks of the
nonce. -/
theorem j0Seg_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.J0In Ctx St W SP k H Np n s) :
    WP isa (.block j0Seg) s (VG.Proof.AesGcm.AArch64.J1 Ctx St W SP k H Np n s.mem) := by
  have he := h.env
  have hd := h.data
  have hlt := hd.lt
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  rw [VG.Proof.AesGcm.AArch64.add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, x3₁, x2₁, x0₁, x1₁, x4₁, x23₁, x25₁, og, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa j0Seg s = some s₁ ∧
      s₁.mem = (s.mem.writeW St (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .x2 = Np ∧ s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧
      s₁.gpr .x1 = St + BitVec.ofNat 64 0 ∧ s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      s₁.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16)) ∧ s₁.gpr .x25 = BitVec.ofNat 64 (n % 16) ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x3, .x2, .x0, .x1, .x4, .x23, .x10, .x25] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [j0Seg, ghArgs]; arun [he.x20, z₀, z₁, VG.Proof.AesGcm.AArch64.add_ofNat_zero], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq]; rfl
    · simp [gpr_write, h.x24, VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ hlt]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, VG.Proof.AesGcm.AArch64.lsr_ofNat _ _ hlt, VG.Proof.AesGcm.AArch64.lsl4_ofNat]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, VG.Proof.AesGcm.AArch64.and15,
        VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt hlt]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fz : Frame [⟨St, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hdw := hd.take (k := 16 * (n / 16)) (by omega)
  refine ⟨he₁, h.kept.of_others og, x23₁, x25₁, hd.of_eq rd₁ wr₁, ?_, ?_, ?_, fz⟩
  · rw [blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide), h.hH]
  · rw [VG.Proof.AesGcm.AArch64.add_ofNat_zero, blockAt, hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · exact VG.Proof.AesGcm.AArch64.ghCall_of L (yo := 0) (.inl rfl) he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by have := hdw.lt; omega)
      (by simpa using (hdw.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))).symm)
      (hdw.w.sub_right (Lay.wSub (by decide))) (by rw [rd₁, wr₁]; exact hdw.rd)

/-- The whole blocks of the nonce absorbed. -/
theorem j0Call1_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.AArch64.J1 Ctx St W SP k H Np n m₀ s) :
    WP isa (ghCall v.callees) s (VG.Proof.AesGcm.AArch64.J2 Ctx St W SP k H Np n m₀) := by
  have hd := h.data
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have dD : ∀ r ∈ [(⟨St, 16⟩ : Region)], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simpa using hd.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
  have dD' : ∀ r ∈ [⟨St + BitVec.ofNat 64 0, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.st.sub_right (Lay.stSub (by decide))
    · exact hd.w.sub_right (Lay.wSub (by decide))
  have hiv : bytesAt s.mem Np n = bytesAt m₀ Np n := bytesAt_frame h.frame dD (by have := hd.lt; omega)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x23],
    by rw [g.saved _ (by decide) (by decide), h.x25], hd.of_eq g.rd g.wr, by rw [VG.Proof.AesGcm.AArch64.hH_gh L (.inl rfl) g, h.hH], ?_,
    by rw [bytesAt_frame g.frame dD' (by have := hd.lt; omega), hiv], ?_⟩
  · rw [g.out, h.y0, h.hH, Proof.Gcm.blocksAt_eq]
    have e := congrArg (List.take (16 * (n / 16))) hiv
    rw [VG.Proof.AesGcm.AArch64.bytesAt_take _ _ (by omega), VG.Proof.AesGcm.AArch64.bytesAt_take _ _ (by omega)] at e
    rw [e]; rfl
  · refine (VG.Proof.AesGcm.AArch64.st_j0Frame (W := W) (d := 0) (k := 16) (by simpa using h.frame) (by decide)).trans
      (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.J0In Ctx St W SP k H Np n s) (hn : n ≠ 12) :
    WP isa (j0hash v.callees) s (VG.Proof.AesGcm.AArch64.J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt
  have k26 : k .x26 = BitVec.ofNat 64 n := by rw [← h.kept .x26 (by decide), h.x26]
  have k27 : k .x27 = 0 := by rw [← h.kept .x27 (by decide), h.x27]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.j0Seg_ok L h) fun s₁ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.j0Call1_ok L v h₁) fun s₂ h₂ => ?_))
  have hdr := h₂.data.drop (k := 16 * (n / 16)) (by omega)
  rw [show n - 16 * (n / 16) = n % 16 by omega] at hdr
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
    h₂.env h₂.kept h₂.x25 (Nat.mod_lt _ (by decide))
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, h₂.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))) fun s₃ h₃ =>
    WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.padCall_ok L (.inl rfl) v h₃) fun s₄ h₄ => ?_))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.lensSeg_ok L (yo := 0) (.inl rfl) (ra := .x27) (rb := .x26) h₄.env h₄.kept h₄.x25
    (by decide)) fun s₅ h₅ => WP.mono (VG.Proof.AesGcm.AArch64.lensCall_ok L (.inl rfl) v h₅) fun s₆ h₆ => ?_)
  have a₄ : (s₄.gpr .x27).toNat = 0 := by rw [h₄.kept .x27 (by decide), k27]; rfl
  have b₄ : (s₄.gpr .x26).toNat = n := by rw [h₄.kept .x26 (by decide), k26, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt hlt]
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := h₂.hH
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame h₄.frame (VG.Proof.AesGcm.AArch64.ctx_tFrame L (.inl rfl)), hH₂]
  have hP : bytesAt s₂.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    have e := congrArg (List.drop (16 * (n / 16))) h₂.iv
    rw [VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ (by omega), VG.Proof.AesGcm.AArch64.bytesAt_drop _ _ (by omega), show n - 16 * (n / 16) = n % 16 by omega] at e
    exact e
  refine ⟨h₆.env, h₆.kept, by rw [blockAt_frame h₆.frame (VG.Proof.AesGcm.AArch64.ctx_tFrame L (.inl rfl)), hH₄], ?_, ?_⟩
  · rw [← VG.Proof.AesGcm.AArch64.add_ofNat_zero St, h₆.out, h₄.out, hH₄, hH₂, a₄, b₄, h₂.y, hP, VG.Proof.AesGcm.AArch64.j0_split H s.mem Np hn]
  · exact (h₂.frame.trans (VG.Proof.AesGcm.AArch64.t_j0Frame h₄.frame)).trans (VG.Proof.AesGcm.AArch64.t_j0Frame h₆.frame)

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.AArch64.J0In Ctx St W SP k H Np n s) :
    WP isa (j0 v.callees) s (VG.Proof.AesGcm.AArch64.J0Out Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [.subImm .x .x9 .x24 12] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ VG.Proof.AesGcm.AArch64.Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h.x24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have h₁ : VG.Proof.AesGcm.AArch64.J0In Ctx St W SP k H Np n s₁ :=
    ⟨h.env.of_regs r₁, h.kept.of_others r₁.others, by rw [r₁.others _ (by decide)]; exact h.x23,
      by rw [r₁.others _ (by decide)]; exact h.x24, by rw [r₁.others _ (by decide)]; exact h.x26,
      by rw [r₁.others _ (by decide)]; exact h.x27, h.data.of_eq r₁.rd r₁.wr, by rw [r₁.mem]; exact h.hH⟩
  have ev : isa.eval (.zero .x .x9) s₁ = some (decide (n = 12)) := by
    show some (s₁.read .x .x9 == 0) = _
    rw [State.read, x9₁, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← r₁.mem]
  refine WP.seq (WP.ite (decide (n = 12)) ev (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (VG.Proof.AesGcm.AArch64.j012_ok L h₁) fun _ hm => VG.Proof.AesGcm.AArch64.initState_ok L hm
  · exact WP.mono (VG.Proof.AesGcm.AArch64.j0hash_ok L v h₁ (by simpa using hf)) fun _ hm => VG.Proof.AesGcm.AArch64.initState_ok L hm

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Cmp`. -/
section

/-!
# AES-GCM on AArch64: checking a received tag (`tagLenOk`, `cmpSeg`, `verRet`), moving tags

Untrusted: everything here is checked by Lean. `tagLenOk` leaves 1 in `x9`
iff §5.2.1.2 allows a tag of `x28` bytes, 0 if not (`tagLenOk_ok`);
`cmpSeg` pads the `x28` bytes of the received tag at `W` and of the computed
one at `W + 112` with zeros, and leaves 0 in `x10` if they are equal, 1 if
not (`cmpSeg_ok`); `verRet` returns 1 or 0 (`verRet_ok`). `tagIn` copies the
received tag into `W` (`tagIn_ok`), and `tagOut` the computed one out of it
(`tagOut_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## The length -/

theorem tlTest_ok (s : State) (k : Nat) (hk : k < 4096) {t b : Nat} (h28 : s.gpr .x28 = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (h9 : s.gpr .x9 = BitVec.ofNat 64 b) :
    WP isa (tlTest k) s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (if t = k then 1 else b) ∧ VG.Proof.AesGcm.AArch64.Regs [.x9, .x10] s s' := by
  obtain ⟨s₁, run₁, x10₁, r₁⟩ : ∃ s₁, runBlock isa [.subImm .x .x10 .x28 k] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 t - BitVec.ofNat 64 k ∧ VG.Proof.AesGcm.AArch64.Regs [.x10] s s₁ := by
    refine ⟨_, by arun [hk], ?_⟩
    exact ⟨by simp [gpr_write, h28], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have ev : isa.eval (.zero .x .x10) s₁ = some (decide (t = k)) := by
    show some (s₁.read .x .x10 == 0) = _
    rw [State.read, x10₁, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq ht (by omega)]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, WP.ite (decide (t = k)) ev (fun h => ?_) (fun h => ?_)⟩)
  · have h' : t = k := by simpa using h
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      exact ⟨by simp [gpr_write, h'], (r₁.comp (rs' := [.x9]) ⟨by others_tac, by rfl, by rfl, by rfl, by rfl⟩).mono (rs' := [.x9, .x10])⟩
  · have h' : t ≠ k := by simpa using h
    exact WP.block_nil ⟨by simp [r₁.others .x9 (by decide), h9, h'], r₁.mono⟩

theorem tl_chain {t : Nat} (ht : t < 2 ^ 64) :
    (if t = 16 then 1 else if t = 15 then 1 else if t = 14 then 1 else if t = 13 then 1 else
      if t = 12 then 1 else if t = 8 then 1 else if t = 4 then 1 else 0) =
      if Spec.Gcm.tagLenOk t then 1 else 0 := by
  rcases Nat.lt_or_ge t 17 with h | h
  · have e : ∀ t < 17, (if t = 16 then 1 else if t = 15 then 1 else if t = 14 then 1 else if t = 13 then 1 else
        if t = 12 then 1 else if t = 8 then 1 else if t = 4 then 1 else 0) =
        if Spec.Gcm.tagLenOk t then 1 else 0 := by decide
    exact e t h
  · simp [Spec.Gcm.tagLenOk, show t ≠ 16 by omega, show t ≠ 15 by omega, show t ≠ 14 by omega,
      show t ≠ 13 by omega, show t ≠ 12 by omega, show t ≠ 8 by omega, show t ≠ 4 by omega,
      show ¬ t ≤ 16 by omega]

/-- `tagLenOk`: `x9` is 1 iff the tag length is allowed. -/
theorem tagLenOk_ok (s : State) {t : Nat} (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0) ∧
      VG.Proof.AesGcm.AArch64.Regs [.x9, .x10] s s' := by
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [imm .x9 0] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 0 ∧ VG.Proof.AesGcm.AArch64.Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have e28 : ∀ s' : State, VG.Proof.AesGcm.AArch64.Regs [.x9, .x10] s s' → s'.gpr .x28 = BitVec.ofNat 64 t :=
    fun s' r => by rw [r.others _ (by decide), h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have r₁' : VG.Proof.AesGcm.AArch64.Regs [.x9, .x10] s s₁ := r₁.mono
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₁ 4 (by decide) (e28 _ r₁') ht x9₁) fun s₂ ⟨x9₂, r₂⟩ => ?_)
  have r₂' := r₁'.trans r₂
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₂ 8 (by decide) (e28 _ r₂') ht x9₂) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have r₃' := r₂'.trans r₃
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₃ 12 (by decide) (e28 _ r₃') ht x9₃) fun s₄ ⟨x9₄, r₄⟩ => ?_)
  have r₄' := r₃'.trans r₄
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₄ 13 (by decide) (e28 _ r₄') ht x9₄) fun s₅ ⟨x9₅, r₅⟩ => ?_)
  have r₅' := r₄'.trans r₅
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₅ 14 (by decide) (e28 _ r₅') ht x9₅) fun s₆ ⟨x9₆, r₆⟩ => ?_)
  have r₆' := r₅'.trans r₆
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₆ 15 (by decide) (e28 _ r₆') ht x9₆) fun s₇ ⟨x9₇, r₇⟩ => ?_)
  have r₇' := r₆'.trans r₇
  refine WP.mono (VG.Proof.AesGcm.AArch64.tlTest_ok s₇ 16 (by decide) (e28 _ r₇') ht x9₇) fun s₈ ⟨x9₈, r₈⟩ =>
    ⟨by rw [x9₈, VG.Proof.AesGcm.AArch64.tl_chain ht], r₇'.trans r₈⟩

/-! ## Padded tags -/

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [VG.Proof.AesGcm.AArch64.le8_inj h₁, VG.Proof.AesGcm.AArch64.le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) := by
  rw [VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, VG.Proof.AesGcm.AArch64.bytesAt_add] at hz
  have e := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

/-- The carry of adding all ones: whether a word is not 0. -/
theorem carry_ne (d : BitVec 64) :
    decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + (false : Bool).toNat) = !decide (d = 0) := by
  have : (0 - 1 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
  rw [this]
  by_cases h : d = 0
  · subst h; decide
  · have : d.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [h, decide_false, Bool.not_false, Bool.toNat_false, Nat.add_zero, decide_eq_true_iff]
    omega

theorem carry_val (d : BitVec 64) :
    (0 : BitVec 64) + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + false.toNat)).toNat =
      BitVec.ofNat 64 (if d = 0 then 0 else 1) := by
  rw [VG.Proof.AesGcm.AArch64.carry_ne]
  by_cases h : d = 0
  · subst h; rfl
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- `cmpSeg`: 0 in `x10` iff the first `t` bytes of the tag at `W + 112` are
those at `W`. -/
theorem cmpSeg_ok {k : Reg → BitVec 64} {s : State} (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s) {t : Nat}
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) :
    WP isa cmpSeg s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t then 0 else 1) ∧
      VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' ∧ VG.Proof.AesGcm.AArch64.Kept k s' ∧ s'.gpr .x28 = BitVec.ofNat 64 t ∧
      Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  have w (d : Nat) (h : d + 8 ≤ 2560) := he.perm.wW h
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, og₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [imm .x9 0, .str .x .x9 .x19 vO,
      .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO, .str .x .x9 .x19 (rO + 8), ptr .x11 .x19 rO, mov .x12 .x19,
      mov .x13 .x28] s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 264)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 280)
          (0 : BitVec 64) ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 272 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x11, .x12, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [he.x19, w 256 (by decide), w 264 (by decide), w 272 (by decide), w 280 (by decide)], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, he.x19]
    · simp [gpr_write, he.x19, BitVec.add_zero]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq ?_
  have he₁ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₁ := he.keep (fun r hr => og₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dW : (⟨W, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 272, 16⟩ := by
    simpa using L.w_w (a := 0) (n := t) (d := 272) (k := 16) (.inl (by omega)) (by omega) (by decide)
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₁ W (W + BitVec.ofNat 64 272) t :=
    ⟨by omega, VG.Proof.AesGcm.AArch64.covers_left (by simpa using he₁.perm.wC (d := 0) (n := t) (by omega)),
      he₁.perm.wC (by omega), dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have he₂ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => og₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 t := by
    rw [og₂ _ (by decide), og₁ _ (by decide), h28]
  refine WP.seq ?_
  obtain ⟨s₃, run₃, hm₃, x11₃, x12₃, x13₃, og₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [ptr .x11 .x19 vO,
      ptr .x12 .x19 uO, mov .x13 .x28] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x11 = W + BitVec.ofNat 64 256 ∧ s₃.gpr .x12 = W + BitVec.ofNat 64 112 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.AArch64.Others [.x11, .x12, .x13] s₂ s₃ ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by arun [he₂.x19], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, x28₂]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have dU : (⟨W + BitVec.ofNat 64 112, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp₃ : VG.Proof.AesGcm.AArch64.LoopPre s₃ (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 256) t :=
    ⟨by omega, VG.Proof.AesGcm.AArch64.covers_left (he₃.perm.wC (by omega)), he₃.perm.wC (by omega), dU.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₃ x12₃ x11₃ x13₃ lp₃) fun s₄ ⟨hm₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
  have he₄ : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₄ := he₃.keep (fun r hr => og₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  have r (d : Nat) (h : d + 8 ≤ 2560) := he₄.perm.wR h
  obtain ⟨s₅, run₅, x10₅, og₅, sp₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO,
      .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1,
      .adds .x .x9 .x9 .x12, .adcs .x .x10 .x11 .x11] s₄ = some s₅ ∧
      s₅.gpr .x10 = BitVec.ofNat 64 (if (s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 272) 64) ||| (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0 then 0 else 1) ∧
      VG.Proof.AesGcm.AArch64.Others [.x9, .x10, .x11, .x12] s₄ s₅ ∧ s₅.sp = s₄.sp ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by arun [he₄.x19, r 256 (by decide), r 264 (by decide), r 272 (by decide), r 280 (by decide),
      gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry,
      c_write], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
        show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
      exact VG.Proof.AesGcm.AArch64.carry_val _
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_addWithCarry, hr]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e8 (a : Nat) : W + BitVec.ofNat 64 (a + 8) = W + BitVec.ofNat 64 a + BitVec.ofNat 64 8 :=
    (VG.Proof.AesGcm.AArch64.add_ofNat_assoc W a 8).symm
  have hm₁' : s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [hm₁, ← e8, ← e8]
  have fa := Proof.Cmac.frame_store2 (m := s.mem) (W + BitVec.ofNat 64 256) 0 0
  have fb := Proof.Cmac.frame_store2 (m := (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) (W + BitVec.ofNat 64 272) 0 0
  have sR (d n : Nat) (h₁ : 256 ≤ d) (h₂ : d + n ≤ 288) :
      ∃ r' ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r' :=
    ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  have f₁ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₁.mem := by
    rw [hm₁']
    refine (fa.sub fun r hr => ?_).trans (fb.sub fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr)
    · exact sR 256 16 (by decide) (by decide)
    · exact sR 272 16 (by decide) (by decide)
  have z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 272) 16 = zeros 16 := by
    rw [hm₁', Proof.Cmac.bytesAt_store2]; rfl
  have z₀ : bytesAt s₁.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [hm₁', bytesAt_frame fb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Proof.Cmac.bytesAt_store2]; rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 272, t⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 256, t⟩] s₂.mem s₄.mem := by
    rw [hm₄, hm₃]; exact VG.Proof.AesGcm.AArch64.writeBytes_frame' _ (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)
  have f₁₂ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 272 t (by decide) (by omega))
  have f₁₄ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₄.mem :=
    f₁₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 256 t (by decide) (by omega))
  have hA : bytesAt s₁.mem W t = bytesAt s.mem W t :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := t) (d := 256) (k := 32) (.inl (by omega)) (by omega) (by decide)) (by omega)
  have hB : bytesAt s₂.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem (W + BitVec.ofNat 64 112) t :=
    bytesAt_frame f₁₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by omega)
  have p₁ : bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s.mem W t ++ zeros (16 - t) := by
    rw [hm₂, VG.Proof.AesGcm.AArch64.pad_bytes z₁ _ (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega), VG.Proof.AesGcm.AArch64.length_bytesAt, hA]
  have z₀' : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by omega))
      (by decide), z₀]
  have p₀ : bytesAt s₄.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem (W + BitVec.ofNat 64 112) t ++ zeros (16 - t) := by
    rw [hm₄, hm₃, VG.Proof.AesGcm.AArch64.pad_bytes z₀' _ (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega), VG.Proof.AesGcm.AArch64.length_bytesAt, hB]
  have q₁ : bytesAt s₄.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by decide) (by omega))
      (by decide)
  have key : ((s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 272) 64) |||
      (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0) ↔
      bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t := by
    rw [show (264 : Nat) = 256 + 8 from rfl, show (280 : Nat) = 272 + 8 from rfl, e8 256, e8 272, VG.Proof.AesGcm.AArch64.words_eq, p₀, q₁, p₁]
    exact ⟨List.append_cancel_right, fun h => by rw [h]⟩
  have og : VG.Proof.AesGcm.AArch64.Others [.x9, .x11, .x12, .x13, .x14, .x15, .x10] s s₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h13, h14, h15, h10⟩ := hr
    have hl : r ∉ VG.Proof.AesGcm.AArch64.loopRegs := by simp [VG.Proof.AesGcm.AArch64.loopRegs, h11, h12, h13, h14, h15]
    rw [og₅ r (by simp [h9, h10, h11, h12]), og₄ r hl, og₃ r (by simp [h11, h12, h13]), og₂ r hl,
      og₁ r (by simp [h9, h11, h12, h13])]
  refine ⟨by rw [x10₅]; simp only [key], he₄.keep (fun r hr => og₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₅ rd₅ wr₅, hk.of_others og, by rw [og _ (by decide), h28], ?_⟩
  rw [m₅]; exact f₁₄

end

/-- `verRet`: 1 if the tags are equal (`x10` is 0), 0 if not. -/
theorem verRet_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block verRet) s fun s' => s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧ VG.Proof.AesGcm.AArch64.Regs [.x0] s s' := by
  refine WP.run ⟨_, by simp only [verRet]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `tagIn`: the received tag, the `t` bytes at `Tg`, copied to `W`. -/
theorem tagIn_ok {s : State} {W Tg : Addr} {t : Nat} (h19 : s.gpr .x19 = W) (h12 : s.gpr .x12 = Tg)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) (hr : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨W, 2560⟩] s.wr) (hd : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa tagIn s fun s' => bytesAt s'.mem W t = bytesAt s.mem Tg t ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      VG.Proof.AesGcm.AArch64.Others VG.Proof.AesGcm.AArch64.loopRegs s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, og₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x11 .x19, mov .x13 .x28] s =
      some s₁ ∧ s₁.gpr .x11 = W ∧ s₁.gpr .x12 = Tg ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.AArch64.Others [.x11, .x13] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h19]
    · simp [gpr_write, h12]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : VG.Proof.AesGcm.AArch64.LoopPre s₁ Tg W t :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hr, VG.Proof.AesGcm.AArch64.covers_prefix (by rw [wr₁]; exact hw) (by omega),
      hd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (VG.Proof.AesGcm.AArch64.copy_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ⟨?_, ?_, ?_, by rw [sp₂, sp₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · have := VG.Proof.AesGcm.AArch64.bytesAt_writeBytes_self s₁.mem W (bytesAt s₁.mem Tg t) (by rw [VG.Proof.AesGcm.AArch64.length_bytesAt]; omega)
    rw [VG.Proof.AesGcm.AArch64.length_bytesAt] at this
    rw [hm₂, this, m₁]
  · rw [hm₂, ← m₁]
    exact (VG.Proof.AesGcm.AArch64.writeBytes_frame' _ (VG.Proof.AesGcm.AArch64.length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · intro r hr
    rw [og₂ r hr, og₁ r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl <;> simp)]

/-- `tagOut`: the tag at `W` copied to the 16 bytes at `Tg`. -/
theorem tagOut_ok {s : State} {W Tg : Addr} (h19 : s.gpr .x19 = W) (h28 : s.gpr .x28 = Tg)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hw : Covers [⟨Tg, 16⟩] s.wr)
    (hd : (⟨Tg, 16⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa (.block tagOut) s fun s' => bytesAt s'.mem Tg 16 = bytesAt s.mem W 16 ∧
      Frame [⟨Tg, 16⟩] s.mem s'.mem ∧ VG.Proof.AesGcm.AArch64.Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := VG.Proof.AesGcm.AArch64.in_off hr (show 0 + 8 ≤ 2560 by decide) (by decide)
  have r₂ := VG.Proof.AesGcm.AArch64.in_off hr (show 8 + 8 ≤ 2560 by decide) (by decide)
  have w₁ := VG.Proof.AesGcm.AArch64.in_off hw (show 0 + 8 ≤ 16 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.AArch64.in_off hw (show 8 + 8 ≤ 16 by decide) (by decide)
  have hd' : (⟨Tg, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 8, 8⟩ :=
    hd.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Offset.sub_base _ (by decide))
  obtain ⟨s', run, hm, og, sp', rd', wr'⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = (s.mem.writeW Tg (s.mem.readW W 64)).writeW (Tg + BitVec.ofNat 64 8)
        ((s.mem.writeW Tg (s.mem.readW W 64)).readW (W + BitVec.ofNat 64 8) 64) ∧
      VG.Proof.AesGcm.AArch64.Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [tagOut]; arun [h19, h28, r₁, r₂, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, Mem.writeW, Mem.readW, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceAdd, gpr_write, ite_true, ite_false, reduceCtorEq, h19, h28]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, og, sp', rd', wr'⟩
  · rw [hm, VG.Proof.AesGcm.AArch64.bytesAt_copy2 _ hd']
  · rw [hm]; exact Proof.Cmac.frame_store2 _ _ _

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Save`. -/
section

/-!
# AES-GCM on AArch64: saving and restoring our caller's registers

Untrusted: everything here is checked by Lean. Each function saves `x19`–`x28`
and `x30` at `W + 128` (`save_ok`) and restores them (`restore_ok`,
`exit_ok`); the pieces it runs in between never write there (`SavedAt.frame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64

/-- The memory after saving the registers `g` at `W + 128`. -/
def savedMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (W + BitVec.ofNat 64 d) (g r)) m

/-- The saved registers' slots. -/
abbrev savedR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (W : Addr) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.Proof.AesGcm.AArch64.savedMem s.mem W s.gpr := by
  have w (d : Nat) (h : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 := VG.Proof.AesGcm.AArch64.in_off hw h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, save, saved, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some, hb,
      w 128 (by decide), w 136 (by decide), w 144 (by decide), w 152 (by decide), w 160 (by decide),
      w 168 (by decide), w 176 (by decide), w 184 (by decide), w 192 (by decide), w 200 (by decide),
      w 208 (by decide)]
    rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [VG.Proof.AesGcm.AArch64.savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) : VG.Proof.AesGcm.AArch64.SavedAt (VG.Proof.AesGcm.AArch64.savedMem m W g) W ⟨g, 0, false,
    fun _ => 0, m, [], [], fun _ => 0, fun _ => 0⟩ := by
  intro p h
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [VG.Proof.AesGcm.AArch64.savedMem, saved, List.foldl]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [VG.Proof.AesGcm.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem SavedAt.of_gpr {m : Mem} {W : Addr} {s₀ s₁ : State} (h : VG.Proof.AesGcm.AArch64.SavedAt m W s₀) (hg : s₁.gpr = s₀.gpr) :
    VG.Proof.AesGcm.AArch64.SavedAt m W s₁ := fun p hp => by rw [h p hp, hg]

theorem savedAt_save (m : Mem) (W : Addr) (s₀ : State) : VG.Proof.AesGcm.AArch64.SavedAt (VG.Proof.AesGcm.AArch64.savedMem m W s₀.gpr) W s₀ :=
  (VG.Proof.AesGcm.AArch64.savedMem_slot m W s₀.gpr).of_gpr rfl

theorem slot_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 216) :
    (VG.Proof.AesGcm.AArch64.savedR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [VG.Proof.AesGcm.AArch64.savedR W] m (VG.Proof.AesGcm.AArch64.savedMem m W g) := by
  simp only [VG.Proof.AesGcm.AArch64.savedMem, saved, List.foldl]
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 216) := VG.Proof.AesGcm.AArch64.slot_contains W h₁ h₂
  exact (((((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 144 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 152 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 160 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {W : Addr} {s₀ : State} (h : VG.Proof.AesGcm.AArch64.SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r) : VG.Proof.AesGcm.AArch64.SavedAt m' W s₀ := by
  intro p hp
  have hp' := hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hs : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.AesGcm.AArch64.savedR W) := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Offset.sub _ (by decide) (by decide)
  rw [hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

theorem restore_ok (s : State) {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (W + BitVec.ofNat 64 p.2) 64) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r (d : Nat) (h : d + 8 ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := VG.Proof.AesGcm.AArch64.in_off hr h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, h19,
      r 128 (by decide), r 136 (by decide), r 144 (by decide), r 152 (by decide), r 160 (by decide),
      r 168 (by decide), r 176 (by decide), r 184 (by decide), r 192 (by decide), r 200 (by decide),
      r 208 (by decide)]
    rfl, ?_⟩
  refine ⟨fun p h => ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_write, Mem.readW]
  · simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp [gpr_write, h]

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h19 : s.gpr .x19 = W) (hsp : s.sp = s₀.sp)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hs : VG.Proof.AesGcm.AArch64.SavedAt s.mem W s₀) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, hsv, hother, sp', hm, rd', wr'⟩ := VG.Proof.AesGcm.AArch64.restore_ok s h19 hr
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr' => ?_, by rw [sp', hsp]⟩, hm, hother .x0 (by decide), rd', wr'⟩
  have hin : r ∈ saved.map (·.1) := (by decide : ∀ r ∈ preserved, r ∈ saved.map (·.1)) r hr'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hin
  rw [hsv p hp, hs p hp]

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Contract`. -/
section

/-!
# AES-GCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read their last arguments from the stack, which they
may only read.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- `vg_aes_gcm_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 256⟩
    let scr : Region := ⟨s.gpr .x3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .x2).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .x2) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_init(ctx = x0, nonce = x1, nonce_len = x2, state = x3, scratch = x4)`. -/
def streamInitAArch64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let st : Region := ⟨s.gpr .x3, 80⟩
    let scr : Region := ⟨s.gpr .x4, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .x3) ciph (ctxH s.mem (s.gpr .x0))
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) [] []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_aad(ctx = x0, state = x1, aad_len = x2, data = x3, len = x4, scratch = x5)`. -/
def streamAadAArch64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let st : Region := ⟨s.gpr .x1, 80⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .x1) ciph (ctxH s.mem (s.gpr .x0)) iv a [] →
    s.gpr .x2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .x1) ciph (ctxH s.mem (s.gpr .x0)) iv
      (a ++ VG.Spec.Aes.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = x0, rounds = x1, state = x2, aad_len = x3, text_len = x4, data = x5, len = x6,
scratch = x7)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 ∧
    VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .x2) ciph h iv a (gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) p) →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = p.length →
      let c := gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) (p ++ VG.Spec.Aes.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
      StreamRepr s'.mem (s.gpr .x2) ciph h iv a c ∧ VG.Spec.Aes.bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = c.drop p.length
  pub := VG.Proof.AesGcm.AArch64.streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      let c' := c ++ VG.Spec.Aes.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
      StreamRepr s'.mem (s.gpr .x2) ciph h iv a c' ∧
        VG.Spec.Aes.bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = (gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) c').drop c.length
  pub := VG.Proof.AesGcm.AArch64.streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = x0, rounds = x1, state = x2, aad_len = x3,
text_len = x4, tag = x5, work = x6)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let tag : Region := ⟨s.gpr .x5, 16⟩
  let work : Region := ⟨s.gpr .x6, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    tag.Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x6).toNat + 2560 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      VG.Spec.Aes.bytesAt s'.mem (s.gpr .x5) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = x0, rounds = x1, state = x2, aad_len = x3,
text_len = x4, tag = x5, tag_len = x6, work = x7)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let tag : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let work : Region := ⟨s.gpr .x7, 2560⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ tag.Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 ∧
    VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    let tl := (s.gpr .x6).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      let t := fullTag ciph h iv a c
      if VG.Spec.Gcm.tagLenOk tl ∧ t.take tl = VG.Spec.Aes.bytesAt s.mem (s.gpr .x5) tl then (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_seal` and `vg_aes_gcm_open` need of their common arguments:
`(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6,
len = x7, …)`, with `n` arguments on the stack and `work` the `w`-th. -/
def oneCore (n w : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let work : Region := ⟨stackArg s w, 2560⟩
  ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ VG.Proof.AesGcm.AArch64.args s n ∈ s.rd ∧ data ∈ s.wr ∧ work ∈ s.wr ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.AArch64.args s n) ∧ work.Disjoint (VG.Proof.AesGcm.AArch64.args s n) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s w).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * n ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-- What `vg_aes_gcm_seal` needs: its common arguments, `tag = [sp]` and `work = [sp + 8]`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, VG.Proof.AesGcm.AArch64.args s 2] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.AArch64.args s 2) ∧ tag.Disjoint work ∧ work.Disjoint (VG.Proof.AesGcm.AArch64.args s 2) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 2 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, VG.Spec.Aes.bytesAt s'.mem (stackArg s 0) 16)
  pub := VG.Proof.AesGcm.AArch64.onePub 2

/-- What `vg_aes_gcm_open` needs: its common arguments, `tag = [sp]`, `tag_len = [sp + 8]` and
`work = [sp + 16]`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, tag, VG.Proof.AesGcm.AArch64.args s 3] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.AArch64.args s 3) ∧ tag.Disjoint work ∧ work.Disjoint (VG.Proof.AesGcm.AArch64.args s 3) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-- What `vg_aes_gcm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (VG.Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_gcm_open` may leak: whether it succeeds, for `rounds` of 10, 12 or 14. -/
def openLeakOf (s : State) : List Nat :=
  if ¬VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1) then [] else [if (VG.Proof.AesGcm.AArch64.openRes s).isSome = true then 1 else 0]

/-- `vg_aes_gcm_open`. -/
def openAArch64 : Contract isa where
  pre := VG.Proof.AesGcm.AArch64.openPre
  post s s' :=
    match VG.Proof.AesGcm.AArch64.openRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  pub s₁ s₂ := VG.Proof.AesGcm.AArch64.onePub 3 s₁ s₂ ∧ VG.Proof.AesGcm.AArch64.openLeakOf s₁ = VG.Proof.AesGcm.AArch64.openLeakOf s₂

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Fn`. -/
section

/-!
# AES-GCM on AArch64: what every function uses

Untrusted: everything here is checked by Lean. The postconditions quantify
over what the state represents (the nonce, the additional data, the text so
far), which the code never looks at: each function runs the same for all of
them, so one run satisfies each instance of its proof (`WP.forall_det`). The
pieces never write the saved registers (`saved_absFrame`, …), and `flush` of
no bytes changes no accumulator (`flush0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- The layout, from disjointness of the context, the state and `W`. -/
theorem Lay.of {Ctx St W : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩) :
    VG.Proof.AesGcm.AArch64.Lay Ctx St W :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide))⟩

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ VG.Proof.AesGcm.AArch64.absFrame St W yo, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W yo, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ VG.Proof.AesGcm.AArch64.tagFrame St W o, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_j0Frame : ∀ r ∈ VG.Proof.AesGcm.AArch64.j0Frame St W, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.crFrame St W D n, (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_cmp : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tag16 : ∀ r ∈ [(⟨W, 16⟩ : Region)], (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simpa using L.w_w (a := 128) (n := 88) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)

/-- `flush` of no bytes: the accumulator as it was. -/
theorem flush0_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k : Reg → BitVec 64} {s : State}
    (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 0) :
    WP isa (flush v.callees yo) s (VG.Proof.AesGcm.AArch64.TOut Ctx St W SP k yo 0 (blockAt s.mem (St + BitVec.ofNat 64 yo)) s.mem) := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 (by decide)
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    (VG.Proof.AesGcm.AArch64.covers_left (he.perm.stC (by omega))) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.AesGcm.AArch64.padCall_ok L hyo v h₁) fun s₂ h₂ => { h₂ with
                                                                out := ?_ }
  rw [h₂.out]; rfl

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Text`. -/
section

/-!
# AES-GCM on AArch64: the additional data padded before the first text

Untrusted: everything here is checked by Lean. `fo` leaves the number of
buffered bytes of additional data in `x25` if this is the first text (and
there is text), and 0 otherwise (`fo_ok`); `flush` then pads and absorbs
them, or changes nothing GHASH has absorbed (`flushStep_ok`): GHASH has then
absorbed `xf a c n`, which the text continues (`ghashInput_xf`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- What GHASH has absorbed before `n` more bytes of text: the additional data
padded if this is the first text. -/
def xf (a c : List Byte) (n : Nat) : List Byte :=
  if n ≠ 0 ∧ c = [] then a ++ zeros (padLen a.length) else ghashInput a c

theorem xf_len {a c : List Byte} {n : Nat} (hn : n ≠ 0) : (VG.Proof.AesGcm.AArch64.xf a c n).length % 16 = c.length % 16 := by
  unfold VG.Proof.AesGcm.AArch64.xf
  by_cases hc : c = []
  · subst hc
    simp only [ne_eq, hn, not_false_eq_true, true_and, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros,
      List.length_nil]
    exact Proof.Gcm.length_pad_mod _
  · simp only [hc, and_false, ↓reduceIte, Proof.Gcm.ghashInput_of_ne hc, List.length_append,
      Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

theorem ghashInput_xf (a c e : List Byte) : ghashInput a (c ++ e) = VG.Proof.AesGcm.AArch64.xf a c e.length ++ e := by
  by_cases he : e = []
  · subst he; simp [VG.Proof.AesGcm.AArch64.xf]
  · have hl : e.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_append _ _ _ he, VG.Proof.AesGcm.AArch64.xf]
    by_cases hc : c = [] <;> simp [hc, hl]

/-- `fo`: the bytes to pad, if this is the first text. -/
theorem fo_ok {s : State} {q n P : Nat} (h25 : s.gpr .x25 = BitVec.ofNat 64 q)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 n) (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hn : n < 2 ^ 64)
    (hP : P < 2 ^ 64) :
    WP isa fo s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ P = 0 then q else 0) ∧ VG.Proof.AesGcm.AArch64.Regs [.x25] s s' := by
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero h26 hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.ite (decide (P = 0)) (VG.Proof.AesGcm.AArch64.eval_zero h27 hP) (fun ht' => ?_) (fun hf' => ?_)
    · have h1 : P = 0 := by simpa using ht'
      exact WP.block_nil ⟨by simp [h25, h0, h1], Regs.refl _ _⟩
    · have h1 : P ≠ 0 := by simpa using hf'
      exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'; exact ⟨by simp [gpr_write, h1], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- `flush` after `fo`: GHASH has absorbed `xf a c n`, where it had absorbed
`ghashInput a c`. -/
theorem flushStep_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {s : State} {a c : List Byte} {n : Nat}
    (he : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s) (hk : VG.Proof.AesGcm.AArch64.Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0))
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (flush v.callees 16) s fun s' => VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' ∧ VG.Proof.AesGcm.AArch64.Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (VG.Proof.AesGcm.AArch64.tFrame St W 16) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (VG.Proof.AesGcm.AArch64.xf a c n)) := by
  by_cases hf : n ≠ 0 ∧ c.length = 0
  · have hc : c = [] := List.eq_nil_of_length_eq_zero hf.2
    subst hc
    rw [ite_eq_left hf] at h25
    refine WP.mono (VG.Proof.AesGcm.AArch64.flush_ok L (.inr rfl) v (x := a) he hk h25 rfl hH) fun s' ⟨ho, hH', habs⟩ =>
      ⟨ho.env, ho.kept, hH', ho.frame, fun ha => ?_⟩
    rw [VG.Proof.AesGcm.AArch64.xf, ite_eq_left ⟨hf.1, rfl⟩]
    exact habs ha
  · rw [ite_eq_right hf] at h25
    refine WP.mono (VG.Proof.AesGcm.AArch64.flush0_ok L v (.inr rfl) he hk h25) fun s' ho =>
      ⟨ho.env, ho.kept, by rw [blockAt_frame ho.frame (VG.Proof.AesGcm.AArch64.ctx_tFrame L (.inr rfl)), hH], ho.frame, fun ha => ?_⟩
    have hx : VG.Proof.AesGcm.AArch64.xf a c n = ghashInput a c := by
      rw [VG.Proof.AesGcm.AArch64.xf, ite_eq_right]; intro h; exact hf ⟨h.1, by rw [h.2]; rfl⟩
    rw [hx]
    refine ha.congr ho.out ?_
    refine bytesAt_frame ho.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hl : (ghashInput a c).length % 16 < 16 := Nat.mod_lt _ (by decide)
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega)) (by have := L.sw; omega) (by have := L.sw; omega)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

end

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Absorbed Ctr)

/-- GHASH's accumulator and buffer stay as they are, outside a frame. -/
theorem Absorbed.frame {m m' : Mem} {St : Addr} {H : Block} {x : List Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r)
    (ha : Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x) :
    Absorbed m' (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x := by
  have hl : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  exact ha.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega)))
    (bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by omega))

/-- The counter block and the keystream block stay as they are, outside a frame. -/
theorem Ctr.frame {m m' : Mem} {St : Addr} {ciph : Block → Block} {icb : Block} {n : Nat} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r)
    (hc : Ctr m (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n) :
    Ctr m' (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n :=
  hc.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega)))
    (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega)))

/-- `J₀` stays where it is, outside a frame. -/
theorem j0_frame {m m' : Mem} {St : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St, 16⟩ : Region).Disjoint r) : blockAt m' St = blockAt m St :=
  blockAt_frame hf hd

section
variable {Ctx St W : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

/-- Parts of the state apart from a part of `W`. -/
theorem st_wpart {d k e j : Nat} (hd : d + k ≤ 80) (he : 96 ≤ e ∧ e + j ≤ 2560) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
  L.st_w hd (.inr he)

theorem st_st' {d k e j : Nat} (h : d + k ≤ e ∨ e + j ≤ d) (hd : d + k ≤ 80) (he : e + j ≤ 80) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ :=
  L.st_st h hd he

theorem st0_disj {e j : Nat} (h : 16 ≤ e) (he : e + j ≤ 80) :
    (⟨St, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_st (a := 0) (n := 16) (d := e) (k := j) (.inl h) (by decide) he

theorem st0_w {e j : Nat} (he : 96 ≤ e ∧ e + j ≤ 2560) :
    (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_w (a := 0) (n := 16) (d := e) (k := j) (by decide) (.inr he)

theorem st0_saved : (⟨St, 16⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.savedR W) := VG.Proof.AesGcm.AArch64.st0_w L ⟨by decide, by decide⟩

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Body`. -/
section

/-!
# AES-GCM on AArch64: the bodies of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. With the additional data `a`
and the ciphertext `c` so far, of `P` bytes, and `n` bytes at `D`: the
additional data padded if this is the first text (`fo`, `flush`), then the
data encrypted and the ciphertext absorbed (`encBody_ok`), or the data
absorbed and decrypted (`decBody_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, q⟩ := h; exact ⟨t, s', e, q, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => exact ⟨_, _, .seq ea (.seq eb e₂), q⟩

/-- The regions the bodies write. -/
abbrev bodyFrame (St W D : Addr) (n : Nat) : List Region :=
  VG.Proof.AesGcm.AArch64.tFrame St W 16 ++ VG.Proof.AesGcm.AArch64.crFrame St W D n ++ VG.Proof.AesGcm.AArch64.absFrame St W 16

/-- Before a body. -/
structure BodyIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = BitVec.ofNat 64 P
  x28 : s.gpr .x28 = D
  hc : c.length = P
  hP : P < 2 ^ 64
  data : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- What a body leaves, from `m₀`, where `e` is the data absorbed and `out`
what it leaves at `D`. -/
structure BodyOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (icb : Block) (e out : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.AArch64.Env Ctx St W SP s
  kept : VG.Proof.AesGcm.AArch64.Kept k s
  frame : Frame (VG.Proof.AesGcm.AArch64.bodyFrame St W D n) m₀ s.mem
  post : Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
    Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb P →
    Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a (c ++ e)) ∧
      Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf m₀ Ctx R) icb (P + n) ∧
      bytesAt s.mem D n = out

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.AArch64.Lay Ctx St W)
include L

theorem ctx_tFrame' : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_absFrame' : ∀ r ∈ VG.Proof.AesGcm.AArch64.absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem acc_tFrame_free : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesGcm.AArch64.st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact VG.Proof.AesGcm.AArch64.st_wpart L (by decide) ⟨by decide, by decide⟩
  · exact VG.Proof.AesGcm.AArch64.st_wpart L (by decide) ⟨by decide, by decide⟩

theorem ctr_absFrame : ∀ r ∈ VG.Proof.AesGcm.AArch64.absFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesGcm.AArch64.st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact VG.Proof.AesGcm.AArch64.st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact VG.Proof.AesGcm.AArch64.st_wpart L (by decide) ⟨by decide, by decide⟩

theorem acc_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.crFrame St W D n, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact VG.Proof.AesGcm.AArch64.st_st' L (.inl (by decide)) (by decide) (by decide)
  · exact VG.Proof.AesGcm.AArch64.st_wpart L (by decide) ⟨by decide, by decide⟩

omit L in
theorem data_tFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ok.st.sub_right (Lay.stSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))

theorem hH_tFrame {m m' : Mem} (hf : Frame (VG.Proof.AesGcm.AArch64.tFrame St W 16) m m') :
    blockAt m' (Ctx + BitVec.ofNat 64 240) = blockAt m (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame hf fun r hr => (VG.Proof.AesGcm.AArch64.ctx_tFrame' L r hr).sub_left (Lay.ctxSub (by decide))

theorem hH_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.AArch64.DataW Ctx St W s D n) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcm.AArch64.crFrame St W D n) m m') :
    blockAt m' (Ctx + BitVec.ofNat 64 240) = blockAt m (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame hf fun r hr => (VG.Proof.AesGcm.AArch64.ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))

/-- The additional data padded if this is the first text: `fo` and `flush`. -/
theorem pad_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : VG.Proof.AesGcm.AArch64.BodyIn Ctx St W SP k R n P D a c H s) :
    WP isa (.seq fo (flush v.callees 16)) s fun s' => VG.Proof.AesGcm.AArch64.Env Ctx St W SP s' ∧ VG.Proof.AesGcm.AArch64.Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (VG.Proof.AesGcm.AArch64.tFrame St W 16) s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (VG.Proof.AesGcm.AArch64.xf a c n)) := by
  have hn := h.data.ok.lt
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.fo_ok h.x25 h.x26 h.x27 hn h.hP) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := h.env.of_regs r₁
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0) := by
    rw [x25₁, h.hc]
  refine WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.flushStep_ok L v he₁ (h.kept.of_others r₁.others) h25
    (by rw [r₁.mem]; exact h.hH))) fun s₂ ⟨⟨he₂, hk₂, hH₂, f₂, abs₂⟩, rd₂, wr₂⟩ =>
    ⟨he₂, hk₂, hH₂, by rw [← r₁.mem]; exact f₂, by rw [rd₂, r₁.rd], by rw [wr₂, r₁.wr],
      fun ha => abs₂ (by rw [r₁.mem]; exact ha)⟩

omit L in
/-- `textArgs`: the offset into the text, and the text as the piece. -/
theorem textArgs_ok {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {s : State} (hk : VG.Proof.AesGcm.AArch64.Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k27 : k .x27 = BitVec.ofNat 64 P) (k28 : k .x28 = D) (hP : P < 2 ^ 64) :
    WP isa (.block textArgs) s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ VG.Proof.AesGcm.AArch64.Regs [.x9, .x25, .x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h27 := (hk .x27 (by decide)).trans k27
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by simp only [textArgs]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq]
  rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, VG.Proof.AesGcm.AArch64.and15,
    VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt hP]

omit L in
/-- `mov x23, x28; mov x24, x26`. -/
theorem textPiece_ok {k : Reg → BitVec 64} {n : Nat} {D : Addr} {s : State} (hk : VG.Proof.AesGcm.AArch64.Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k28 : k .x28 = D) :
    WP isa (.block [mov .x23 .x28, mov .x24 .x26]) s fun s' => s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ VG.Proof.AesGcm.AArch64.Regs [.x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem mem_bt {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16) : r ∈ VG.Proof.AesGcm.AArch64.bodyFrame St W D n :=
  List.mem_append_left _ (List.mem_append_left _ h)

omit L in
theorem mem_bc {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ VG.Proof.AesGcm.AArch64.crFrame St W D n) : r ∈ VG.Proof.AesGcm.AArch64.bodyFrame St W D n :=
  List.mem_append_left _ (List.mem_append_right _ h)

omit L in
theorem mem_ba {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ VG.Proof.AesGcm.AArch64.absFrame St W 16) : r ∈ VG.Proof.AesGcm.AArch64.bodyFrame St W D n :=
  List.mem_append_right _ h

/-- `encBody`: the data encrypted, and the ciphertext absorbed. -/
theorem encBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : VG.Proof.AesGcm.AArch64.BodyIn Ctx St W SP k R n P D a c H s) (icb : Block) :
    WP isa (encBody v.callees) s (VG.Proof.AesGcm.AArch64.BodyOut Ctx St W SP k R n P D a c H icb
      (xorKs (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n))
      (xorKs (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)) s.mem) := by
  have k22 : k .x22 = BitVec.ofNat 64 R := (h.kept .x22 (by decide)).symm.trans h.x22
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have hd₃ : VG.Proof.AesGcm.AArch64.DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have hCr : VG.Proof.AesGcm.AArch64.CrIn Ctx St W SP k R P D n s₃ :=
    ⟨he₃, hk₃, (hk₃ .x22 (by decide)).trans k22, h.rounds, x23₃, x24₃, x25₃, hd₃⟩
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.crypt_ok L v (icb := icb) hCr)) fun s₄ ⟨h₄, rd₄, wr₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.textPiece_ok h₄.kept k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := h₄.env.of_regs r₅
  have hk₅ := h₄.kept.of_others r₅.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hc₃ : VG.Proof.AesGcm.AArch64.ciphOf s₃.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R := by
    rw [m₃]; exact VG.Proof.AesGcm.AArch64.ciph_frame f₂ (VG.Proof.AesGcm.AArch64.ctx_tFrame' L) h.rounds
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (VG.Proof.AesGcm.AArch64.data_tFrame h.data) (by omega)
  have F₅ : Frame (VG.Proof.AesGcm.AArch64.bodyFrame St W D n) s.mem s₅.mem := by
    rw [r₅.mem]
    exact (f₂.sub fun r hr => ⟨r, VG.Proof.AesGcm.AArch64.mem_bt hr, fun _ h => h⟩).trans
      (by rw [← m₃]; exact h₄.frame.sub fun r hr => ⟨r, VG.Proof.AesGcm.AArch64.mem_bc hr, fun _ h => h⟩)
  have hC₃ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P,
      Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s₃.mem Ctx R) icb P := fun hctr => by
    rw [hc₃, m₃]; exact Ctr.frame f₂ (VG.Proof.AesGcm.AArch64.acc_tFrame_free L) hctr
  have hA₅ : ∀ ha : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c),
      Absorbed s₅.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (VG.Proof.AesGcm.AArch64.xf a c n) := fun ha => by
    rw [r₅.mem]; exact Absorbed.frame h₄.frame (VG.Proof.AesGcm.AArch64.acc_crFrame L hd₃) (by rw [m₃]; exact abs₂ ha)
  have hO₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P,
      bytesAt s₅.mem D n = xorKs (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n) := fun hctr => by
    rw [r₅.mem, h₄.out (hC₃ hctr), hc₃, hD₃]
  have hK₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P,
      Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb (P + n) :=
    fun hctr => by rw [r₅.mem, ← hc₃]; exact h₄.ctr (hC₃ hctr)
  have hlen : (xorKs (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)).length = n := by
    rw [Proof.Gcm.length_xorKs, VG.Proof.AesGcm.AArch64.length_bytesAt]
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero ((hk₅ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₅, hk₅, F₅, fun ha hctr => ⟨?_, hK₅ hctr, hO₅ hctr⟩⟩
    rw [VG.Proof.AesGcm.AArch64.ghashInput_xf, hlen, hn0, show bytesAt s.mem D 0 = [] from rfl, Proof.Gcm.xorKs_nil, List.append_nil]
    have := hA₅ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : VG.Proof.AesGcm.AArch64.AbsIn Ctx St W SP k H (VG.Proof.AesGcm.AArch64.xf a c n) D n (P % 16) s₅ :=
      ⟨he₅, hk₅, x23₅, x24₅, by rw [r₅.others _ (by decide), h₄.x25], by rw [VG.Proof.AesGcm.AArch64.xf_len hn0, h.hc],
        h.data.ok.of_eq (by rw [r₅.rd, rd₄, r₃.rd, rd₂]) (by rw [r₅.wr, wr₄, r₃.wr, wr₂]),
        by rw [r₅.mem, VG.Proof.AesGcm.AArch64.hH_crFrame L hd₃ h₄.frame, m₃, hH₂]⟩
    refine WP.mono (VG.Proof.AesGcm.AArch64.absorb_ok L (.inr rfl) v hA) fun s₆ h₆ => ⟨h₆.env, h₆.kept,
      F₅.trans (h₆.frame.sub fun r hr => ⟨r, VG.Proof.AesGcm.AArch64.mem_ba hr, fun _ h => h⟩), fun ha hctr => ⟨?_, ?_, ?_⟩⟩
    · rw [VG.Proof.AesGcm.AArch64.ghashInput_xf, hlen, ← hO₅ hctr]; exact h₆.abs (hA₅ ha)
    · exact Ctr.frame h₆.frame (VG.Proof.AesGcm.AArch64.ctr_absFrame L) (hK₅ hctr)
    · rw [bytesAt_frame h₆.frame (VG.Proof.AesGcm.AArch64.data_absFrame (.inr rfl) hA.data) (by omega), hO₅ hctr]

/-- `decBody`: the data absorbed, and decrypted. -/
theorem decBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : VG.Proof.AesGcm.AArch64.BodyIn Ctx St W SP k R n P D a c H s) (icb : Block) :
    WP isa (decBody v.callees) s (VG.Proof.AesGcm.AArch64.BodyOut Ctx St W SP k R n P D a c H icb (bytesAt s.mem D n)
      (xorKs (VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)) s.mem) := by
  have k22 : k .x22 = BitVec.ofNat 64 R := (h.kept .x22 (by decide)).symm.trans h.x22
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq (WP.seq_assoc (WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (VG.Proof.AesGcm.AArch64.data_tFrame h.data) (by omega)
  have hd₃ : VG.Proof.AesGcm.AArch64.DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  -- After the text is absorbed.
  have mid : WP isa (textAbs v.callees) s₃ fun s₄ => VG.Proof.AesGcm.AArch64.Env Ctx St W SP s₄ ∧ VG.Proof.AesGcm.AArch64.Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (VG.Proof.AesGcm.AArch64.tFrame St W 16 ++ VG.Proof.AesGcm.AArch64.absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
    have F₃ : Frame (VG.Proof.AesGcm.AArch64.tFrame St W 16 ++ VG.Proof.AesGcm.AArch64.absFrame St W 16) s.mem s₃.mem := by
      rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
    · have hn0 : n = 0 := by simpa using ht
      refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
      rw [VG.Proof.AesGcm.AArch64.ghashInput_xf, VG.Proof.AesGcm.AArch64.length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
      have := abs₂ ha
      rw [hn0] at this
      exact this
    · have hn0 : n ≠ 0 := by simpa using hf
      have hA : VG.Proof.AesGcm.AArch64.AbsIn Ctx St W SP k H (VG.Proof.AesGcm.AArch64.xf a c n) D n (P % 16) s₃ :=
        ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [VG.Proof.AesGcm.AArch64.xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
      refine WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
        ⟨h₄.env, h₄.kept, h₄.x25,
          F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
          by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
      rw [VG.Proof.AesGcm.AArch64.ghashInput_xf, VG.Proof.AesGcm.AArch64.length_bytesAt, ← hD₃]
      exact h₄.abs (by rw [m₃]; exact abs₂ ha)
  refine WP.mono mid fun s₄ ⟨he₄, hk₄, x25₄, F₄, rd₄, wr₄, abs₄⟩ => ?_
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.textPiece_ok hk₄ k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := he₄.of_regs r₅
  have hk₅ := hk₄.of_others r₅.others
  have hd₅ : VG.Proof.AesGcm.AArch64.DataW Ctx St W s₅ D n := h.data.of_eq (by rw [r₅.rd, rd₄]) (by rw [r₅.wr, wr₄])
  have hCr : VG.Proof.AesGcm.AArch64.CrIn Ctx St W SP k R P D n s₅ :=
    ⟨he₅, hk₅, (hk₅ .x22 (by decide)).trans k22, h.rounds, x23₅, x24₅,
      by rw [r₅.others _ (by decide), x25₄], hd₅⟩
  have ctxF : ∀ r ∈ VG.Proof.AesGcm.AArch64.tFrame St W 16 ++ VG.Proof.AesGcm.AArch64.absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.AArch64.ctx_tFrame' L r hr
    · exact VG.Proof.AesGcm.AArch64.ctx_absFrame' L r hr
  have hc₅ : VG.Proof.AesGcm.AArch64.ciphOf s₅.mem Ctx R = VG.Proof.AesGcm.AArch64.ciphOf s.mem Ctx R := by
    rw [r₅.mem]; exact VG.Proof.AesGcm.AArch64.ciph_frame F₄ ctxF h.rounds
  have hD₅ : bytesAt s₅.mem D n = bytesAt s.mem D n := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.AArch64.data_tFrame h.data r hr
    · exact VG.Proof.AesGcm.AArch64.data_absFrame (.inr rfl) h.data.ok r hr
  refine WP.mono (VG.Proof.AesGcm.AArch64.crypt_ok L v (icb := icb) hCr) fun s₆ h₆ => ⟨h₆.env, h₆.kept, ?_, fun ha hctr => ⟨?_, ?_, ?_⟩⟩
  · rw [r₅.mem] at h₆
    exact (F₄.sub fun r hr => ⟨r, by
      rcases List.mem_append.mp hr with hr | hr
      · exact VG.Proof.AesGcm.AArch64.mem_bt hr
      · exact VG.Proof.AesGcm.AArch64.mem_ba hr, fun _ h => h⟩).trans (h₆.frame.sub fun r hr => ⟨r, VG.Proof.AesGcm.AArch64.mem_bc hr, fun _ h => h⟩)
  · rw [r₅.mem] at h₆
    exact Absorbed.frame h₆.frame (VG.Proof.AesGcm.AArch64.acc_crFrame L hd₅) (abs₄ ha)
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s₅.mem Ctx R) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact VG.Proof.AesGcm.AArch64.acc_tFrame_free L r hr
      · exact VG.Proof.AesGcm.AArch64.ctr_absFrame L r hr
    have := h₆.ctr hC
    rw [hc₅] at this
    exact this
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.AArch64.ciphOf s₅.mem Ctx R) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact VG.Proof.AesGcm.AArch64.acc_tFrame_free L r hr
      · exact VG.Proof.AesGcm.AArch64.ctr_absFrame L r hr
    rw [h₆.out hC, hc₅, hD₅]

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Init`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_aes_expand_key_scratch`, then the hash subkey `CIPH_K(0¹²⁸)` at byte 240 from
`vg_aes_ctr32` over a zero block with a zero counter block (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr ctxH)

theorem rounds_of_len {L : Nat} (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    BitVec.ofNat 64 L >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- `vg_aes_gcm_init`. -/
theorem init_wp (v : GcmImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init v.callees) s fun s' => GprAbi s s' ∧ initAArch64.post s s' := by
  simp only [VG.Proof.AesGcm.AArch64.initAArch64] at hp ⊢
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, ws, hL⟩ := hp
  generalize hK : s.gpr .x0 = K at *
  generalize hLn : (s.gpr .x1).toNat = L at *
  generalize hCtx : s.gpr .x2 = Ctx at *
  generalize hW : s.gpr .x3 = W at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.AArch64.covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.AArch64.covers_of_mem (by simp)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := VG.Proof.AesGcm.AArch64.save_ok s .x3 hW pW
  have hsi : s.gpr .x1 = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x21₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x3, mov .x21 .x2, .lsr .x .x22 .x1 2, .addImm .x .x22 .x22 6, ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, hsi, BitVec.setWidth_eq]
      exact VG.Proof.AesGcm.AArch64.rounds_of_len hL
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hsi]
    · simp [gpr_write, g₁, hCtx]
  generalize hRd : Spec.Aes.rounds (L / 4) = R at x22₂
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := VG.Proof.AesGcm.AArch64.covers_off pW (by decide) (by decide)
  have kc : KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L := by
    refine ⟨x0₂, x1₂, x2₂, x3₂, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂', wr₂', hrd]
      exact VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (VG.Proof.AesGcm.AArch64.covers_left (VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_prefix pC (by decide)) pS))
    · rw [wr₂']; exact VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_prefix pC (by decide)) pS
  refine WP.seq (WP.mono (key_call v.key kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g21 : s₃.gpr .x21 = Ctx := by rw [g.saved .x21 (by decide) (by decide), x21₂]
  have g22 : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [g.saved .x22 (by decide) (by decide), x22₂]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂'
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂'
  have w₁ := VG.Proof.AesGcm.AArch64.in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.AArch64.in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.AArch64.in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := VG.Proof.AesGcm.AArch64.in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 248) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 104) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .x3 = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ VG.Proof.AesGcm.AArch64.Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s₃ s₄ ∧
      s₄.sp = s₃.sp ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [g19, g21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, g21]
    · simp [gpr_write, g22]
    · simp [gpr_write, g19]
    · simp [gpr_write, g21]
    · simp [gpr_write]
    · simp [gpr_write, g19]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have rd₄' : s₄.rd = s.rd := rd₄.trans rd₃
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have e248 : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
    (VG.Proof.AesGcm.AArch64.add_ofNat_assoc _ 240 8).symm
  have e104 : W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 :=
    (VG.Proof.AesGcm.AArch64.add_ofNat_assoc _ 96 8).symm
  rw [e248, e104] at hm₄
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Proof.Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, VG.Proof.AesGcm.AArch64.zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      VG.Proof.AesGcm.AArch64.zeroT_bytes]
    decide
  have fsv : Frame [VG.Proof.AesGcm.AArch64.savedR W] s.mem s₁.mem := by rw [m₁]; exact VG.Proof.AesGcm.AArch64.savedMem_frame _ _ _
  have hk₄ : bytesAt s₄.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      ← hRd, g.out, m₂, bytesAt_frame fsv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Lay.wSub (by decide)))
        (by rcases hL with rfl | rfl | rfl <;> decide)]
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄']; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄']; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 := by
    refine ⟨x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, hR', ?_, by decide, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
    · simpa using dCW 0 240 (by decide) 96 16 (by decide)
    · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
    · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact dCW 240 16 (by decide) 512 2048 (by decide)
    · exact VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_left (VG.Proof.AesGcm.AArch64.covers_prefix pC' (by decide))) (VG.Proof.AesGcm.AArch64.covers_cons
        (VG.Proof.AesGcm.AArch64.covers_left (VG.Proof.AesGcm.AArch64.covers_off pW' (by decide) (by decide))) (VG.Proof.AesGcm.AArch64.covers_cons
        (VG.Proof.AesGcm.AArch64.covers_left (VG.Proof.AesGcm.AArch64.covers_off pC' (by decide) (by decide))) (VG.Proof.AesGcm.AArch64.covers_left (VG.Proof.AesGcm.AArch64.covers_off pW' (by decide) (by decide)))))
    · exact VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_off pW' (by decide) (by decide)) (VG.Proof.AesGcm.AArch64.covers_cons (VG.Proof.AesGcm.AArch64.covers_off pC' (by decide) (by decide))
        (VG.Proof.AesGcm.AArch64.covers_off pW' (by decide) (by decide)))
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have gout := c.out
  rw [VG.Proof.AesGcm.AArch64.blocksAt_one, VG.Proof.AesGcm.AArch64.blocksAt_one, VG.Proof.AesGcm.AArch64.ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c19 : s₅.gpr .x19 = W := by rw [c.saved .x19 (by decide) (by decide), og₄ _ (by decide), g19]
  have dSv : ∀ r ∈ [(⟨Ctx, 240⟩ : Region), ⟨W + BitVec.ofNat 64 512, 512⟩], (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)) |>.symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩],
      (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (VG.Proof.AesGcm.AArch64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have hsv₁ : VG.Proof.AesGcm.AArch64.SavedAt s₁.mem W s := by rw [m₁]; exact VG.Proof.AesGcm.AArch64.savedAt_save _ _ _
  have hsv₅ : VG.Proof.AesGcm.AArch64.SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← m₂]; exact g.frame) dSv).frame f₄ dSv₄).frame c.frame dSv₅)
  refine WP.mono (VG.Proof.AesGcm.AArch64.exit_ok c19 (by rw [c.sp, sp₄, g.sp, sp₂, sp₁])
    (by rw [c.rd, c.wr, wr₄']; exact VG.Proof.AesGcm.AArch64.covers_left pW) hsv₅) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  rw [hm]
  refine ⟨?_, ?_⟩
  · rw [VG.Proof.AesGcm.AArch64.length_bytesAt, hRd, bytesAt_frame c.frame (fun r hr => ?_) (by omega), hk₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact dK0.sub_left (Region.sub_prefix hRb)
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
  · show blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = _
    rw [gout.1, Spec.Gcm.aes, VG.Proof.AesGcm.AArch64.length_bytesAt, hRd]
    simp

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Rel`. -/
section

/-!
# AES-GCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs relate
two runs from given states (`Eq2 σ₁ σ₂`) piece by piece: the code between
calls by the taint analysis, from the registers the correctness proofs pin to
the same public values in both runs (`rel_taint`); each call by its callee's
proof (`rel_gh`, `rel_ctr`, `rel_key`); a branch on a value both runs agree
on (`rel_ite`); and the next piece from the states the correctness proofs
describe (`rel_seq`). A block may be split where the taint analysis needs a
register pinned anew (`RelCT.block_split`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) {s' : State} {t : List Leak}
    (h : execBlock isa (l₁ ++ l₂) s = some (s', t)) :
    ∃ s₁ t₁ t₂, execBlock isa l₁ s = some (s₁, t₁) ∧ execBlock isa l₂ s₁ = some (s', t₂) ∧ t = t₁ ++ t₂ := by
  induction l₁ generalizing s t with
  | nil => exact ⟨s, [], t, rfl, h, rfl⟩
  | cons i is ih =>
    simp only [List.cons_append, execBlock] at h ⊢
    cases hx : exec i s with
    | none => rw [hx] at h; cases h
    | some s₁ =>
      rw [hx] at h
      simp only at h ⊢
      obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨s₃, t₃, t₄, h₃, h₄, rfl⟩ := ih s₁ h₂
      exact ⟨s₃, List.map Leak.addr (addrs i s) ++ t₃, t₄, by simp [h₃], h₄, by simp⟩

/-- A block run as two. -/
theorem RelCT.block_split {l₁ l₂ : List Instr} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      obtain ⟨a₁, u₁, v₁, x₁, y₁, rfl⟩ := VG.Proof.AesGcm.AArch64.execBlock_append l₁ l₂ _ h₁
      obtain ⟨a₂, u₂, v₂, x₂, y₂, rfl⟩ := VG.Proof.AesGcm.AArch64.execBlock_append l₁ l₂ _ h₂
      exact h _ _ _ _ _ _ hp (.seq (.block x₁) (.block y₁)) (.seq (.block x₂) (.block y₂))

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) c₁ VG.Proof.AesGcm.AArch64.TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 τ₁ τ₂) c₂ VG.Proof.AesGcm.AArch64.TT) :
    RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) (.seq c₁ c₂) VG.Proof.AesGcm.AArch64.TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) c VG.Proof.AesGcm.AArch64.TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h => hr r (VG.AArch64.Taint.mem_ofRegs.mp h)⟩) hc

theorem rel_gh (g : GhashImpl) {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) (.call g.fn.name g.fn.code) VG.Proof.AesGcm.AArch64.TT :=
  gh_rel g fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr (v : Ctr32Impl) {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) (.call v.callee.name v.callee.code) VG.Proof.AesGcm.AArch64.TT :=
  ctr_rel v fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key (k : KeyImpl) {σ₁ σ₂ : State} {K C S : Addr} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) (.call k.fn.name k.fn.code) VG.Proof.AesGcm.AArch64.TT :=
  key_rel k fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, S, L, h₁, h₂, hsp⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) t VG.Proof.AesGcm.AArch64.TT)
    (hf : b = false → RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) e VG.Proof.AesGcm.AArch64.TT) : RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) (.ite c t e) VG.Proof.AesGcm.AArch64.TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (VG.Proof.AesGcm.AArch64.Eq2 σ₁ σ₂) c VG.Proof.AesGcm.AArch64.TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

/-- Proves `∀ r ∈ [r₁, …], σ₁.gpr r = σ₂.gpr r` by rewriting each side with `ts`. -/
macro "agree_tac" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, and_self, $ts,*])

end VG.Proof.AesGcm.AArch64

end
