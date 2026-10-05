import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Spec.Gcm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Env`. -/
section

/-!
# AES-GCM on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`), the working space (2560 bytes
at `W`) and the stack below `SP` used by the calls (`Lay`): the state is
disjoint from the parts of `W` other than `[16, 96)` (where `seal` and
`open` keep it), and the context from both. `Perm` says the state may read
the context and write the state and `W`; `Env` adds the registers that hold
the three addresses throughout.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

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
  VG.Proof.AesGcm.X86_64.covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => VG.Proof.AesGcm.X86_64.in_left (h a n hi)

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

/-- The regions: the context, the state and the parts of `W`, and the stack
below `SP` (8 bytes, for the return addresses of the calls). -/
structure Lay (Ctx St W SP : Addr) : Prop where
  cw : Ctx.toNat + 256 ≤ 2 ^ 64
  sw : St.toNat + 80 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩
  cw' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  sa : (⟨St, 80⟩ : Region).Disjoint ⟨W, 16⟩
  sb : (⟨St, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩
  kc : (below SP 8).Disjoint ⟨Ctx, 256⟩
  ks : (below SP 8).Disjoint ⟨St, 80⟩
  kw : (below SP 8).Disjoint ⟨W, 2560⟩

/-- What a state may access. -/
structure Perm (Ctx St W : Addr) (s : State) : Prop where
  ctx : Covers [⟨Ctx, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨St, 80⟩] s.wr
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the context, the state, `W` and the stack pointer,
and what the state may access. -/
structure Env (Ctx St W SP : Addr) (s : State) : Prop where
  r13 : s.gpr .r13 = Ctx
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : VG.Proof.AesGcm.X86_64.Perm Ctx St W s

theorem Perm.of_eq {Ctx St W : Addr} {s s' : State} (h : VG.Proof.AesGcm.X86_64.Perm Ctx St W s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.Perm Ctx St W s' := by
  obtain ⟨a, b, c⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact c⟩

/-- An environment, after code that keeps `r13`–`r15`, `rsp` and the permissions. -/
theorem Env.keep {Ctx St W SP : Addr} {s s' : State} (h : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' :=
  ⟨by rw [hg _ (by simp), h.r13], by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.r15],
    by rw [hg _ (by simp), h.rsp], h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {Ctx St W SP : Addr} {s s' : State} (h : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

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

variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (VG.Proof.AesGcm.X86_64.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.X86_64.Lay.aSub hd)
  · exact (L.sb.sub_left (VG.Proof.AesGcm.X86_64.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.X86_64.Lay.bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (VG.Proof.AesGcm.X86_64.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.X86_64.Lay.stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (VG.Proof.AesGcm.X86_64.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.X86_64.Lay.wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP 8).Disjoint ⟨Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (VG.Proof.AesGcm.X86_64.Lay.ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP 8).Disjoint ⟨St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (VG.Proof.AesGcm.X86_64.Lay.stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (VG.Proof.AesGcm.X86_64.Lay.wSub ha)

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

variable {Ctx St W : Addr} {s : State} (P : VG.Proof.AesGcm.X86_64.Perm Ctx St W s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86_64.in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86_64.in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86_64.in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86_64.in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86_64.in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.AesGcm.X86_64.covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.X86_64.covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.X86_64.covers_off P.w h (by decide)

end Perm

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Arith`. -/
section

/-!
# AES-GCM on x86-64: arithmetic on lengths

Untrusted: everything here is checked by Lean. The 64-bit operations on
lengths and offsets the code does, as operations on natural numbers.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

theorem imm_eq {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setWidth_imm {n : Nat} : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem shr4 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem shr2 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem and15 (x : BitVec 64) : x &&& (BitVec.ofNat 32 15).signExtend 64 = BitVec.ofNat 64 (x.toNat % 16) := by
  rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `ZF` after `x - y` (or a test of `x` with itself), as natural numbers. -/
theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) :=
  Offset.ofNat_sub_ofNat_beq ha hb

theorem and_self_beq {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a &&& BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [BitVec.and_self]
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

/-- `16 n`, by four doublings. -/
theorem times16_val (n : Nat) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n) +
        (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n)) +
      (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n) +
        (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n))) =
      BitVec.ofNat 64 (16 * n) := by
  simp only [VG.Proof.AesGcm.X86_64.ofNat_add_ofNat]; congr 1; omega

/-- `8 n`, by three doublings. -/
theorem times8_val (x : BitVec 64) :
    x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Run`. -/
section

/-!
# AES-GCM on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `xrun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`), and
the memory facts shared by the pieces: what `DataOk` says of a buffer of
data, and the bytes written by a copy (`bytesAt_writeBytes`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "xrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, stO, tO, uO, roundsO, alenO, tlenO, dataO,
    lenO, auxO, tlO, aadO, tagPO, vO, rO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, and_self, and_true, true_and, $ts,*]) <;> try rfl)

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
context, the state, `W` and the stack below `SP`. -/
structure DataOk (St W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  st : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace DataOk

variable {St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.DataOk St W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.DataOk St W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.X86_64.DataOk St W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := VG.Proof.AesGcm.X86_64.covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  st := h.st.sub_left (Offset.sub_base D (by omega))
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.X86_64.DataOk St W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end DataOk

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
  rw [VG.Proof.AesGcm.X86_64.bytesAt_add]
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
  have := VG.Proof.AesGcm.X86_64.bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks`. -/
section

/-!
# AES-GCM on x86-64: small blocks shared by the pieces

Untrusted: everything here is checked by Lean.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- `test r, r` sets ZF iff `r` holds 0. -/
theorem test_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · rw [zf_arithFlags, h, VG.Proof.AesGcm.X86_64.and_self_beq hn]
  all_goals rfl

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

/-- Running a block with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-- `rcx := min (16 - rbx, rbp)`. -/
theorem minLen_ok (s : State) {o n : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 o)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .sub .rcx (.reg .rbx),
      .alu .cmp .rbp (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - o) ∧ s₁.cf = some (decide (n < 16 - o)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hbx, VG.Proof.AesGcm.X86_64.ofNat_sub ho (by decide)]
    · simp only [cf_arithFlags, hbp, hbx, VG.Proof.AesGcm.X86_64.setWidth_imm, VG.Proof.AesGcm.X86_64.ofNat_sub ho (by decide),
        VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt (show 16 - o < 2 ^ 64 by omega),
        show (16 : Nat) % 2 ^ 32 = 16 from rfl]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  obtain ⟨hcx, hcf, hg, hm, hrd, hwr⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - o)) (VG.Proof.AesGcm.X86_64.eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .rcx (s₁.gpr .rbp)) ⟨_, by xrun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r hr => ?_, hm, hrd, hwr⟩
    · simp only [gpr_setReg, ite_true, hg _ (by decide : Reg.rbp ≠ .rcx), hbp]
      simp at ht; rw [Nat.min_eq_right (by omega)]
    · simp only [gpr_setReg, hr, ite_false]; exact hg r hr
  · refine WP.block_nil ⟨?_, hg, hm, hrd, hwr⟩
    simp at hf; rw [hcx, Nat.min_eq_left (by omega)]

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.CTBase`. -/
section

/-!
# AES-GCM on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`): the code between the calls is
checked by the taint analysis, from registers that agree in the two runs
(`rel_taint`), and leaves registers and flags that agree for the next piece,
a branch or a loop (`rel_regs`); what correctness says about each run is
added with `rel_wp`, and the environment's registers, which no instruction
writes, keep their values (`rel_env`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

/-- Code the taint analysis checks from registers `rs` that agree, leaving
the registers `rs'` and, if `f`, the flags agreeing. -/
theorem rel_regs {P : State → State → Prop} {c : Prog isa} (rs rs' : List Reg) (f : Bool)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs rs) c hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!f || τ'.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => (∀ r ∈ rs', s₁.gpr r = s₂.gpr r) ∧
      (f = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of) := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (Taint.agree_ofRegs (hag _ _ hP)) e₁ e₂
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
  refine ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs.1 (RegSet.mem_ofList.mpr hr)), fun hf => ?_⟩
  exact ha.rf.2 (hs.2.resolve_left (by simp [hf]))

/-- Code the taint analysis checks from registers `rs` that agree. -/
theorem rel_taint {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- What each run satisfies by correctness. -/
theorem rel_wp {P Q : State → State → Prop} {c : Prog isa} {F₁ F₂ G₁ G₂ : State → Prop}
    (h : RelCT isa P c Q) (hP : ∀ s₁ s₂, P s₁ s₂ → F₁ s₁ ∧ F₂ s₂)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa P c fun s₁ s₂ => Q s₁ s₂ ∧ G₁ s₁ ∧ G₂ s₂ :=
  h.wp fun _ _ hp => ⟨hw₁ _ (hP _ _ hp).1, hw₂ _ (hP _ _ hp).2⟩

/-- The environment, after code that writes none of its registers. -/
theorem rel_env {Ctx St W SP : Addr} {P Q : State → State → Prop} {c : Prog isa}
    (hc : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], ∀ i ∈ instrs c, Taint.clobbers i r = false)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂) (h : RelCT isa P c Q) :
    RelCT isa P c fun s₁ s₂ => Q s₁ s₂ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨r₁, w₁⟩ := Exec.rdwr e₁
  obtain ⟨r₂, w₂⟩ := Exec.rdwr e₂
  exact ⟨ht, hq, (hP _ _ hp).1.keep (fun r hr => Exec.gpr (hc r hr) e₁) r₁ w₁,
    (hP _ _ hp).2.keep (fun r hr => Exec.gpr (hc r hr) e₂) r₂ w₂⟩

/-- Two runs with the same environment, agreeing on the registers `rs`. -/
def EnvAgree (Ctx St W SP : Addr) (rs : List Reg) (s₁ s₂ : State) : Prop :=
  VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem EnvAgree.regs {Ctx St W SP : Addr} {rs : List Reg} {s₁ s₂ : State} (h : VG.Proof.AesGcm.X86_64.EnvAgree Ctx St W SP rs s₁ s₂) :
    ∀ r ∈ rs ++ ([.r13, .r14, .r15, .rsp] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h.2.2 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.r13, h.2.1.r13]
    · rw [h.1.r14, h.2.1.r14]
    · rw [h.1.r15, h.2.1.r15]
    · rw [h.1.rsp, h.2.1.rsp]

/-- A branch on ZF, which agrees in the two runs. -/
theorem rel_ite_e {P Q : State → State → Prop} {t e : Prog isa} (hc : ∀ s₁ s₂, P s₁ s₂ → s₁.zf = s₂.zf)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ s₁.zf = some true) t Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ s₁.zf = some false) e Q) :
    RelCT isa P (.ite .e t e) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h) ht he

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem rel_reassoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) : RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁) (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `e; (a; (b; c))`, related as `e; ((a; b); c)`. -/
theorem rel_reassoc_inner {P Q : State → State → Prop} {e a b c : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq a b) c)) Q) : RelCT isa P (.seq e (.seq a (.seq b c))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ c₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ c₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq a₁ b₁) c₁)) (.seq x₂ (.seq (.seq a₂ b₂) c₂))
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `e; (a; (b; (c; d)))`, related as `e; ((a; (b; c)); d)`. -/
theorem rel_reassoc_inner3 {P Q : State → State → Prop} {e a b c d : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq a (.seq b c)) d)) Q) : RelCT isa P (.seq e (.seq a (.seq b (.seq c d)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq a₁ (.seq b₁ c₁)) d₁)) (.seq x₂ (.seq (.seq a₂ (.seq b₂ c₂)) d₂))
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- A block, related as two. -/
theorem rel_block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff, execBlock_append] at e₁ e₂
  obtain ⟨⟨m₁, u₁⟩, a₁, b₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨m₂, u₂⟩, a₂, b₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨n₁, w₁⟩, c₁, d₁⟩ := Option.map_eq_some_iff.mp b₁
  obtain ⟨⟨n₂, w₂⟩, c₂, d₂⟩ := Option.map_eq_some_iff.mp b₂
  simp only [Prod.mk.injEq] at d₁ d₂
  obtain ⟨rfl, rfl⟩ := d₁
  obtain ⟨rfl, rfl⟩ := d₂
  exact h _ _ _ _ _ _ hp (.seq (.block a₁) (.block c₁)) (.seq (.block a₂) (.block c₂))

/-- `a; (b; c)`, related as `(a; b); c`. -/
theorem rel_reassoc2 {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := RelCT.assoc h

/-- The taint check of `ghash1 yo b o`'s arguments. -/
def Gh1Check (yo : Nat) (b : Reg) (o : Nat) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (Impl.AesGcm.X86_64.ptr .rdi .r13 240 ++
    Impl.AesGcm.X86_64.ptr .rsi .r14 yo ++ Impl.AesGcm.X86_64.ptr .rdx b o ++
    [.mov32 .rcx (Impl.AesGcm.X86_64.imm 1)] ++ Impl.AesGcm.X86_64.ptr .r8 .r15 Impl.AesGcm.X86_64.scrO)) hc).isSome = true

theorem gh1Check_r14_32 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : VG.Proof.AesGcm.X86_64.Gh1Check yo .r14 32 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem gh1Check_r15_96 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : VG.Proof.AesGcm.X86_64.Gh1Check yo .r15 96 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1`. -/
section

/-!
# AES-GCM on x86-64: GHASH over one block of the state or of `T`

Untrusted: everything here is checked by Lean. `ghash1 yo b o` continues
the accumulator at `St + yo` over the block at `P = b + o` (`ghash1_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (Ctx Y W SP : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {Ctx St W SP Y : Addr} {ds : List Block} (h : VG.Proof.AesGcm.X86_64.GhOut s Ctx Y W SP ds s')
    (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' := he.of_saved h.saved h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- A call's arguments, from a state whose registers are its arguments. -/
theorem ghCall_of {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) {P : Addr} {n : Nat}
    (hdi : s.gpr .rdi = Ctx + BitVec.ofNat 64 240) (hsi : s.gpr .rsi = St + BitVec.ofNat 64 yo)
    (hdx : s.gpr .rdx = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 n) (hr8 : s.gpr .r8 = W + BitVec.ofNat 64 512)
    (hn : 16 * n < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16 * n⟩) (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) n := by
  have hk := he.rsp
  refine ⟨hdi, hsi, hdx, hcx, hr8, hn, L.ctx_st (by decide) (by omega), L.ctx_w (by decide) (by decide),
    hpy, L.st_w (by omega) (.inr ⟨by decide, by decide⟩), hpw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.stk_ctx (by decide)
  · rw [hk]; exact L.stk_st (by omega)
  · rw [hk]; exact hpk
  · rw [hk]; exact L.stk_w (by decide)
  · exact VG.Proof.AesGcm.X86_64.covers_cons (he.perm.ctxC (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons hpr (VG.Proof.AesGcm.X86_64.covers_cons
      (VG.Proof.AesGcm.X86_64.covers_left (he.perm.stC (by omega))) (VG.Proof.AesGcm.X86_64.covers_left (he.perm.wC (by decide)))))
  · exact VG.Proof.AesGcm.X86_64.covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments. -/
theorem ghCall_ok (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) {P : Addr} {n : Nat}
    (hdi : s.gpr .rdi = Ctx + BitVec.ofNat 64 240) (hsi : s.gpr .rsi = St + BitVec.ofNat 64 yo)
    (hdx : s.gpr .rdx = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 n) (hr8 : s.gpr .r8 = W + BitVec.ofNat 64 512)
    (hn : 16 * n < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16 * n⟩) (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) s
      (VG.Proof.AesGcm.X86_64.GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP (blocksAt s.mem P n)) := by
  refine WP.mono (gh_call v.gh (VG.Proof.AesGcm.X86_64.ghCall_of L hyo he hdi hsi hdx hcx hr8 hn hpy hpw hpk hpr)) fun s' h =>
    ⟨h.rd, h.wr, h.saved, ?_, h.out⟩
  rw [← he.rsp]; exact h.frame

/-- What the arguments of `ghash1 yo b o` leave, for the block at `P = b + o`. -/
structure Gh1Args (s₀ : State) (Ctx St W SP : Addr) (yo : Nat) (P : Addr) (s₁ : State) : Prop where
  rdi : s₁.gpr .rdi = Ctx + BitVec.ofNat 64 240
  rsi : s₁.gpr .rsi = St + BitVec.ofNat 64 yo
  rdx : s₁.gpr .rdx = P
  rcx : s₁.gpr .rcx = BitVec.ofNat 64 1
  r8 : s₁.gpr .r8 = W + BitVec.ofNat 64 512
  keep : ∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r
  mem : s₁.mem = s₀.mem
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr

theorem gh1Args_ok {Ctx St W SP : Addr} {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P)
    (ho : o < 2 ^ 31) :
    WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++
        ptr .r8 .r15 scrO)) s (VG.Proof.AesGcm.X86_64.Gh1Args s Ctx St W SP yo P) := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  rcases hb with rfl | rfl <;> rcases hyo with rfl | rfl
  all_goals
    refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, ← hP]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr}
    (hP : s.gpr b + BitVec.ofNat 64 o = P) (ho : o < 2 ^ 31)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩) (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 v.callees yo b o) s
      (VG.Proof.AesGcm.X86_64.GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP [blockAt s.mem P]) := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.gh1Args_ok hyo he b o hb hP ho) fun s₁ a => ?_)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.of_saved a.keep a.rd a.wr
  refine WP.mono (VG.Proof.AesGcm.X86_64.ghCall_ok v L hyo he₁ (P := P) (n := 1) a.rdi a.rsi a.rdx a.rcx a.r8 (by decide)
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [a.rd, a.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans a.rd, h.wr.trans a.wr, fun r hr => (h.saved r hr).trans (a.keep r hr), a.mem ▸ h.frame,
    by rw [h.out, VG.Proof.AesGcm.X86_64.blocksAt_one, a.mem]⟩

/-- `ghash1 yo b o` in two runs, for the same block address `P`. -/
theorem ghash1_rel (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) (ho : o < 2 ^ 31) {P : Addr}
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (ptr .rdi .r13 240 ++
      ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++ ptr .r8 .r15 scrO)) hc).isSome = true)
    {F₁ F₂ : State → Prop}
    (hF : ∀ s, (F₁ s ∨ F₂ s) → VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ s.gpr b + BitVec.ofNat 64 o = P ∧
      Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (ghash1 v.callees yo b o) fun _ _ => True := by
  have hA : ∀ s, (F₁ s ∨ F₂ s) → WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++
      [.mov32 .rcx (imm 1)] ++ ptr .r8 .r15 scrO)) s (fun s₁ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧
        GhCall s₁ (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) 1) :=
    fun s hs => WP.mono (VG.Proof.AesGcm.X86_64.gh1Args_ok hyo (hF s hs).1 b o hb (hF s hs).2.1 ho) fun s₁ a =>
      have he₁ := (hF s hs).1.of_saved a.keep a.rd a.wr
      ⟨he₁, VG.Proof.AesGcm.X86_64.ghCall_of L hyo he₁ a.rdi a.rsi a.rdx a.rcx a.r8 (by decide) (by simpa using hpy)
        (by simpa using hpw) (by simpa using hpk) (by rw [a.rd, a.wr]; simpa using (hF s hs).2.2)⟩
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.r13, .r14, .r15, .rsp] (fun s₁ s₂ h r hr => by
      have e₁ := (hF s₁ (.inl h.1)).1; have e₂ := (hF s₂ (.inr h.2)).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15]
      · rw [e₁.rsp, e₂.rsp]) hc)
    (fun _ _ h => h) (fun s h => hA s (.inl h)) (fun s h => hA s (.inr h))
  refine RelCT.seq a (gh_rel v.gh fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Absorb`. -/
section

/-!
# AES-GCM on x86-64: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`rbp` bytes at `r12` into GHASH, with the accumulator at `St + yo` and the
`rbx` buffered bytes at `St + 32` (`absorb_ok`): it fills the buffer
(`head_ok`), absorbs whole blocks (`whole_ok`) and buffers the rest
(`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (St W SP : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨St + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r12`, `rbp`, `rbx` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)
  data : VG.Proof.AesGcm.X86_64.DataOk St W SP s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  le : j ≤ n
  r12 : s.gpr .r12 = D + BitVec.ofNat 64 j
  rbp : s.gpr .rbp = BitVec.ofNat 64 (n - j)
  data : VG.Proof.AesGcm.X86_64.DataOk St W SP s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.X86_64.DataOk St W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame St W SP yo, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame St W SP yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP 8] m m') : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, VG.Proof.AesGcm.X86_64.ofNat_add_ofNat]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer. -/
theorem head_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead v.callees yo) s
      (VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n s.mem (min (16 - x.length % 16) n)) := by
  have hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.minLen_ok s h.rbx h.rbp (by omega) hn') fun s₁ ⟨hcx, hg, hm, hrd, hwr⟩ => ?_)
  generalize hk : min (16 - x.length % 16) n = k at hcx ⊢
  have hk1 : 1 ≤ k := by omega
  have hk16 : x.length % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rdi (.reg .r14),
      .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm 32), .mov .rsi (.reg .r12)] s₁ = some s₂ ∧
      s₂.gpr .rdi = St + BitVec.ofNat 64 (32 + x.length % 16) ∧ s₂.gpr .rsi = D ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg _ (by decide : Reg.r14 ≠ .rcx), hg _ (by decide : Reg.rbx ≠ .rcx), he.r14, h.rbx,
        VG.Proof.AesGcm.X86_64.add_ofNat_assoc, Nat.add_comm]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg _ (by decide : Reg.r12 ≠ .rcx), h.r12]
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have lp : LoopPre s₂ D (St + BitVec.ofNat 64 (32 + x.length % 16)) k := by
    refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], hk1, by omega, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂, hrd, hwr]; exact (h.data.take hkn).rd
    · rw [hwr₂, hwr]; exact he.perm.stC (by omega)
    · exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
  have hreg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₃.gpr r = s.gpr r :=
    fun r a b c d e => by rw [hg₃ r a b, hg₂ r c d, hg r e]
  have h3rcx : s₃.gpr .rcx = BitVec.ofNat 64 k := by
    rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide), hcx]
  rw [hm₂, hm] at hm₃
  rw [hrd₂, hrd] at hrd₃
  rw [hwr₂, hwr] at hwr₃
  -- The bytes copied, and the buffer.
  have hdk := VG.Proof.AesGcm.X86_64.length_bytesAt s.mem D k
  have hB : bytesAt s₃.mem (St + BitVec.ofNat 64 32) (x.length % 16 + k) =
      bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ bytesAt s.mem D k := by
    rw [hm₃, show St + BitVec.ofNat 64 (32 + x.length % 16) =
        St + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (VG.Proof.AesGcm.X86_64.add_ofNat_assoc _ _ _).symm]
    have := VG.Proof.AesGcm.X86_64.bytesAt_writeBytes s.mem (St + BitVec.ofNat 64 32) (x.length % 16) (bytesAt s.mem D k)
      (by rw [hdk]; omega)
    rwa [hdk] at this
  have fw : Frame [⟨St + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₃.mem := by
    rw [hm₃]; exact VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hdk
  have hY : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
    blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
  have hH3 : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), h.hH]
  -- The block after the copy.
  obtain ⟨s₄, run₄, h12, hbp, hbx, hzf, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx), .alu .add .rbx (.reg .rcx),
        .alu .cmp .rbx (imm 16)] s₃ = some s₄ ∧
      s₄.gpr .r12 = D + BitVec.ofNat 64 k ∧ s₄.gpr .rbp = BitVec.ofNat 64 (n - k) ∧
      s₄.gpr .rbx = BitVec.ofNat 64 (x.length % 16 + k) ∧
      s₄.zf = some (decide (x.length % 16 + k = 16)) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have e12 := hreg .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebp := hreg .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebx := hreg .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e12, h3rcx, h.r12]
    · simp [gpr_setReg, ebp, h3rcx, h.rbp, VG.Proof.AesGcm.X86_64.ofNat_sub hkn hn']
    · simp [gpr_setReg, ebx, h3rcx, h.rbx, VG.Proof.AesGcm.X86_64.ofNat_add_ofNat]
    · simp only [zf_arithFlags, ebx, h3rcx, h.rbx, VG.Proof.AesGcm.X86_64.ofNat_add_ofNat]
      rw [VG.Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide) (by decide),
        hreg _ (by decide) (by decide) (by decide) (by decide) (by decide)]) (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  have hd₄ : VG.Proof.AesGcm.X86_64.DataOk St W SP s₄ D n := h.data.of_eq (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  refine WP.ite (decide (x.length % 16 + k = 16)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    have h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (VG.Proof.AesGcm.X86_64.ghash1_ok v L hyo he₄ .r14 32 (.inl rfl) (P := St + BitVec.ofNat 64 32) (by rw [he₄.r14])
      (by decide) (L.st_st (.inl (by omega)) (by omega) (by decide)) (L.st_w (by decide) (.inr ⟨by decide, by decide⟩))
      (L.stk_st (by decide)) (VG.Proof.AesGcm.X86_64.covers_left (he₄.perm.stC (by decide)))) fun s₅ g => ?_
    refine ⟨g.env he₄, hkn, by rw [g.saved _ (by decide)]; exact h12, by rw [g.saved _ (by decide)]; exact hbp,
      hd₄.of_eq g.rd g.wr, ?_, ?_, .inr (by omega), ?_⟩
    · rw [blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm, hm₄, hH3]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16) (B := bytesAt s₃.mem (St + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, hB, ha.2]
      · rw [g.out, hm₄, hY, hH3]; rfl
    · have f₁ : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) s.mem s₃.mem := VG.Proof.AesGcm.X86_64.buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16
      have f₂ : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP yo) s₄.mem s₅.mem := VG.Proof.AesGcm.X86_64.gh_absFrame g.frame
      rw [← hm₄] at f₁; exact f₁.trans f₂
  · -- Not full: the data is used up.
    have h16 : x.length % 16 + k < 16 := by simp at hf; omega
    have hkn' : k = n := by omega
    refine WP.block_nil ⟨he₄, hkn, h12, hbp, hd₄, by rw [hm₄]; exact hH3, fun ha => ?_, .inl (by omega),
      by rw [hm₄]; exact VG.Proof.AesGcm.X86_64.buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16⟩
    rw [hm₄]
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) hY (by rw [hdk]; exact hB)

omit L hyo in
/-- The whole blocks split off: `p` and `k` hold them, `r12` and `rbp` the rest. -/
theorem wholeSplit_ok (p k : Reg) (hpk : (p = .rdx ∧ k = .rcx) ∨ (p = .rcx ∧ k = .r8)) {D : Addr} {n j : Nat}
    {s : State} (hn' : n < 2 ^ 64) (hj : j ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (h13 : s.gpr .rbp = BitVec.ofNat 64 (n - j)) :
    ∃ s₁, runBlock isa (splitWhole p k ++ ([.alu .test k (.reg k)] : List Instr)) s = some s₁ ∧
      s₁.gpr p = D + BitVec.ofNat 64 j ∧ s₁.gpr k = BitVec.ofNat 64 ((n - j) / 16) ∧
      s₁.gpr .r12 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      s₁.zf = some (decide ((n - j) / 16 = 0)) ∧
      (∀ r, r ≠ p → r ≠ k → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  have hand := VG.Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 (n - j))
  rw [VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt (by omega), VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) = BitVec.ofNat 64 (16 * nb) := by
    rw [VG.Proof.AesGcm.X86_64.ofNat_sub (Nat.mod_le _ _) (by omega)]; congr 1; omega
  rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨_, by simp only [splitWhole]; xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_setFlags, h12]
    · simp [gpr_setReg, gpr_setFlags, h13, VG.Proof.AesGcm.X86_64.shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12, h13,
        hand, hsub, BitVec.add_assoc, VG.Proof.AesGcm.X86_64.ofNat_add_ofNat]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h13, hand]
      congr 1
      omega
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq,
        h13, VG.Proof.AesGcm.X86_64.shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
      rw [VG.Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄, h₅]
    all_goals rfl

/-- The whole blocks. -/
theorem whole_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n m₀ j s) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa (absorbWhole v.callees yo) s
      (VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n m₀ (j + 16 * ((n - j) / 16))) := by
  have hn' := h.data.lt
  have he := h.env
  obtain ⟨s₁, run₁, hdx, hcx, h12, hbp, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) hn' h.le h.r12 h.rbp
  generalize hnb : (n - j) / 16 = nb at *
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hrd₁ hwr₁
  have hd₁ : VG.Proof.AesGcm.X86_64.DataOk St W SP s₁ D n := h.data.of_eq hrd₁ hwr₁
  refine WP.ite (decide (nb = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    simp only [Nat.mul_zero, Nat.add_zero]
    refine WP.block_nil ⟨he₁, h.le, by rw [h12]; rfl, by rw [hbp]; rfl, hd₁, by rw [hm₁]; exact h.hH,
      fun ha => by rw [hm₁]; exact h.abs ha, h.whole, by rw [hm₁]; exact h.frame⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := (h.data.drop h.le).take (k := 16 * nb) h16
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hdi, hsi, h8, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO) s₁ = some s₂ ∧
        s₂.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 yo ∧
        s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h15]
      · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    refine WP.mono (VG.Proof.AesGcm.X86_64.ghCall_ok v L hyo he₂ (P := D + BitVec.ofNat 64 j) (n := nb) hdi hsi
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hdx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hcx]) h8 (by have := hdj.lt; omega)
      (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
      (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hdj.rd)) fun s₃ g => ?_
    have hg₃ : ∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 →
        r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r a b c d e f g' i hr => by
      rw [g.saved r hr, hg₂ r f g' i, hg₁ r a b c d e]
    refine ⟨g.env he₂, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hrd₂) (g.wr.trans hwr₂), ?_, ?_,
      .inr (by omega), ?_⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h12]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), hbp]
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hm₂, hm₁]; exact h.hH
    · intro ha
      have ex : x ++ bytesAt m₀ D (j + 16 * nb) = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [VG.Proof.AesGcm.X86_64.bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [VG.Proof.AesGcm.X86_64.length_bytesAt]; omega) (by simp [VG.Proof.AesGcm.X86_64.length_bytesAt]) ?_
      rw [g.out, hm₂, hm₁, h.hH, Proof.Gcm.blocksAt_eq]
      congr 2
      -- The data is as in `m₀`.
      have e₁ := congrArg (fun l => l.drop j) hm₀
      have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      have e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      have e₄ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add,
          List.take_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hm₂, hm₁] at this; exact h.frame.trans (VG.Proof.AesGcm.X86_64.gh_absFrame this)

/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n m₀ j s) (hj : n - j < 16) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa absorbTail s (VG.Proof.AesGcm.X86_64.AbsOut Ctx St W SP yo H x (x ++ bytesAt m₀ D n) m₀) := by
  have hn' := h.data.lt
  have he := h.env
  obtain ⟨s₁, run₁, hcx, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rcx (.reg .rbp), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n - j) ∧ s₁.zf = some (decide (n - j = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.rbp]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, h.rbp]; rw [VG.Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r h₁; simp [gpr_setReg, h₁]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, fun ha => by rw [hm₁]; exact h.abs ha, by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.drop h.le
    have h14 := he₁.r14
    obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (ptr .rdi .r14 32 ++ [.mov .rsi (.reg .r12)]) s₁ = some s₂ ∧
        s₂.gpr .rdi = St + BitVec.ofNat 64 32 ∧ s₂.gpr .rsi = D + BitVec.ofNat 64 j ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁ _ (by decide : Reg.r12 ≠ .rcx), h.r12]
      · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have lp : LoopPre s₂ (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 32) (n - j) := by
      refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], by omega, by omega, ?_, ?_, ?_⟩
      · rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hdj.rd
      · rw [hwr₂, hwr₁]; exact he.perm.stC (by omega)
      · exact hdj.st.sub_right (Lay.stSub (by omega))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
    rw [hm₂, hm₁] at hm₃
    have hlen := VG.Proof.AesGcm.X86_64.length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨St + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hlen
    refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide)]) (hrd₃.trans hrd₂) (hwr₃.trans hwr₂),
      ?_, ?_⟩
    · intro ha
      have ex : x ++ bytesAt m₀ D n = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← VG.Proof.AesGcm.X86_64.bytesAt_add, Nat.add_sub_cancel' h.le]
      have ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        have e₁ := congrArg (fun l => l.drop j) hm₀
        have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := fun m => by
          rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [VG.Proof.AesGcm.X86_64.length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)]
      · rw [hm₃]; exact VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

omit L hyo in
theorem AbsIn.keep {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s s' : State}
    (h : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s' where
  env := h.env.keep (fun r _ => by rw [hg]) hrd hwr
  r12 := by rw [hg]; exact h.r12
  rbp := by rw [hg]; exact h.rbp
  rbx := by rw [hg]; exact h.rbx
  data := h.data.of_eq hrd hwr
  hH := by rw [hm]; exact h.hH

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n m₀ j s) : bytesAt s.mem D n = bytesAt m₀ D n :=
  VG.Proof.AesGcm.X86_64.bytesAt_frame h.frame (VG.Proof.AesGcm.X86_64.data_absFrame hyo h.data) (by have := h.data.lt; omega)

/-- `absorb yo`. -/
theorem absorb_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s) :
    WP isa (absorb v.callees yo) s (VG.Proof.AesGcm.X86_64.AbsOut Ctx St W SP yo H x (x ++ bytesAt s.mem D n) s.mem) := by
  have hn' := h.data.lt
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s .rbp h.rbp hn'
  have h₁ := h.keep hg₁ hm₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    obtain ⟨s₂, run₂, hzf₂, hg₂, hm₂, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.test_ok s₁ .rbx h₁.rbx
      (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
    have h₂ := h₁.keep hg₂ hm₂ hrd₂ hwr₂
    have hm₀ : s₂.mem = s.mem := hm₂.trans hm₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (Q := fun s' => ∃ j, VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n s.mem j s')
      (WP.ite (decide (x.length % 16 = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf₂) (fun ht => ?_) (fun hf => ?_)) fun s' hj => ?_)
    · have ho : x.length % 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨0, h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
        fun ha => by rw [hm₀]; simpa [bytesAt] using ha, .inr (by omega), by rw [← hm₀]; exact Frame.refl _ _⟩
    · have := VG.Proof.AesGcm.X86_64.head_ok v L hyo h₂ h0 (by simpa using hf)
      rw [hm₀] at this; exact WP.mono this fun _ h => ⟨_, h⟩
    · obtain ⟨j, hj⟩ := hj
      refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.whole_ok v L hyo hj (hj.data_eq hyo)) fun s'' hj' => ?_)
      exact VG.Proof.AesGcm.X86_64.tail_ok L hyo hj' (by have := hj.le; omega) (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT`. -/
section

/-!
# AES-GCM on x86-64: `absorb` in two runs

Untrusted: everything here is checked by Lean. Two runs of `absorb yo` that
absorb data at the same address, of the same length, after the same number
of bytes modulo 16, leak the same: the code between the calls of `vg_ghash`
is checked by the taint analysis, from the registers `AbsIn` and `AbsMid`
fix, and each call has the same arguments in both runs.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)

/-- The registers `absorb` and `crypt` start from. -/
def absRegs : List Reg := [.r12, .rbp, .rbx, .r13, .r14, .r15, .rsp]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The buffer filled. -/
theorem head_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat}
    (hx : x₁.length % 16 = x₂.length % 16) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂)
      (absorbHead v.callees yo) fun _ _ => True := by
  refine VG.Proof.AesGcm.X86_64.rel_reassoc4 (RelCT.seq (VG.Proof.AesGcm.X86_64.rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => ⟨h.1.env, h.2.env⟩) (VG.Proof.AesGcm.X86_64.rel_regs VG.Proof.AesGcm.X86_64.absRegs [] true (fun s₁ s₂ h r hr => ?_) ⟨_, by taint_decide⟩)) ?_)
  · simp only [VG.Proof.AesGcm.X86_64.absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hx]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  refine VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ (RelCT.block_nil fun _ _ _ => trivial)
  refine (VG.Proof.AesGcm.X86_64.ghash1_rel v L hyo .r14 32 (.inl rfl) (by decide) (P := St + BitVec.ofNat 64 32)
    (L.st_st (.inl (by omega)) (by omega) (by decide)) (L.st_w (by decide) (.inr ⟨by decide, by decide⟩))
    (L.stk_st (by decide)) (VG.Proof.AesGcm.X86_64.gh1Check_r14_32 hyo) (F₁ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP) (F₂ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) fun _ _ h => h
  have he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r14], VG.Proof.AesGcm.X86_64.covers_left (he.perm.stC (by decide))⟩

omit L hyo in
/-- `AbsMid`'s registers agree in two runs with the same `j`. -/
theorem AbsMid.agree {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁) (h₂ : VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂) :
    ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r12, h₂.r12]
  · rw [h₁.rbp, h₂.rbp]
  · rw [h₁.env.r13, h₂.env.r13]
  · rw [h₁.env.r14, h₂.env.r14]
  · rw [h₁.env.r15, h₂.env.r15]
  · rw [h₁.env.rsp, h₂.env.rsp]

/-- The whole blocks. -/
theorem whole_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂)
      (absorbWhole v.callees yo) fun _ _ => True := by
  -- What the split leaves in each run.
  let Sp : State → Prop := fun s₁ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.DataOk St W SP s₁ D n ∧ j ≤ n ∧
    s₁.gpr .rdx = D + BitVec.ofNat 64 j ∧ s₁.gpr .rcx = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {H : Block} {x : List Byte} {m : Mem} (s : State), VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H x D n m j s →
      WP isa (.block (splitWhole .rdx .rcx ++ [.alu .test .rcx (.reg .rcx)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hdx, hcx, -, -, -, hg₁, -, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) h.data.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le, hdx, hcx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧
      VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => AbsMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The call's arguments.
  let Ar : State → Prop := fun s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
    GhCall s₂ (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (D + BitVec.ofNat 64 j)
      (W + BitVec.ofNat 64 512) ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO)) s Ar :=
    fun s ⟨he, hd, hj, hdx, hcx⟩ => by
      have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
      have hdj := (hd.drop hj).take (k := 16 * ((n - j) / 16)) (by omega)
      obtain ⟨s₂, run₂, hdi, hsi, h8, hg₂, -, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
          (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO) s = some s₂ ∧
          s₂.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 yo ∧
          s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
          (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
          s₂.wr = s.wr := by
        rcases hyo with rfl | rfl
        all_goals
          refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [gpr_setReg, h13]
          · simp [gpr_setReg, h14]
          · simp [gpr_setReg, h15]
          · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
          all_goals rfl
      have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
      refine WP.of_runBlock ⟨s₂, run₂, he₂, VG.Proof.AesGcm.X86_64.ghCall_of L hyo he₂ hdi hsi
        (by rw [hg₂ _ (by decide) (by decide) (by decide), hdx])
        (by rw [hg₂ _ (by decide) (by decide) (by decide), hcx]) h8 (by have := hdj.lt; omega)
        (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
        (by rw [hrd₂, hwr₂]; exact hdj.rd)⟩
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp])
      (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO)) hc).isSome = true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have b := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
      have e₁ := h.1.2.1.1; have e₂ := h.1.2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15]
      · rw [e₁.rsp, e₂.rsp]) hc)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (gh_rel v.gh fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

omit L hyo in
/-- The last bytes, buffered. -/
theorem tail_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂)
      absorbTail fun _ _ => True :=
  VG.Proof.AesGcm.X86_64.rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h => AbsMid.agree h.1 h.2) ⟨_, by taint_decide⟩

/-- `absorb yo`, for data at the same address, of the same length, after
the same number of bytes modulo 16. -/
theorem absorb_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat}
    (hx : x₁.length % 16 = x₂.length % 16) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂)
      (absorb v.callees yo) fun _ _ => True := by
  have hag : ∀ s₁ s₂, VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂ →
      ∀ r ∈ VG.Proof.AesGcm.X86_64.absRegs, s₁.gpr r = s₂.gpr r := fun s₁ s₂ h r hr => by
    simp only [VG.Proof.AesGcm.X86_64.absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hx]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  -- `test r, r` keeps everything but the flags.
  have hT : ∀ {r : Reg} {H : Block} {x : List Byte} {k : Nat} (s : State), VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H x D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, h.keep hg₁ hm₁ hrd₁ hwr₁, hz⟩
  have t₁ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧
      VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂) VG.Proof.AesGcm.X86_64.absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.lt)
  refine RelCT.seq t₁ (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt x₁.length (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt x₂.length (show 16 > 0 by decide)
  have t₂ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      VG.Proof.AesGcm.X86_64.absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega))
  -- What each run reaches after filling the buffer: the same `j`.
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ s₁.zf = some (decide (x₁.length % 16 = 0))) ∧
        VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP yo H₂ x₂ D n s₂ ∧ s₂.zf = some (decide (x₂.length % 16 = 0)))
      (.ite .e (.block []) (absorbHead v.callees yo)) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂ := by
    refine VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : x₁.length % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, ?_, ?_⟩
      · have h₂ := h.1.2.1.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
          fun ha => by simpa [bytesAt] using ha, .inr (by omega), Frame.refl _ _⟩
      · have h₂ := h.1.2.2.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
          fun ha => by simpa [bytesAt] using ha, .inr (by omega), Frame.refl _ _⟩
    · by_cases ho : x₁.length % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.head_rel v L hyo (H₁ := H₁) (H₂ := H₂) (D := D) (n := n) hx).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₁ x₁ D n m (min (16 - x₁.length % 16) n) s)
        (G₂ := fun s => ∃ m, VG.Proof.AesGcm.X86_64.AbsMid Ctx St W SP yo H₂ x₂ D n m (min (16 - x₂.length % 16) n) s)
        (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.head_ok v L hyo h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.head_ok v L hyo h hn0 (by omega)) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hx]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  -- The whole blocks and the rest, from the same `j`.
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.whole_rel v L hyo (H₁ := H₁) (H₂ := H₂) (x₁ := x₁) (x₂ := x₂) (D := D) (n := n) (m₁ := m₁)
      (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => VG.Proof.AesGcm.X86_64.whole_ok v L hyo h (h.data_eq hyo)) (fun s h => VG.Proof.AesGcm.X86_64.whole_ok v L hyo h (h.data_eq hyo))
  exact RelCT.seq hw (tail_rel.mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Flush`. -/
section

/-!
# AES-GCM on x86-64: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `rbx`
buffered bytes with zeros in `T` and absorbs them (`flush_ok`); `lens yo`
stores the lengths block of `rbx` and `rbp` bytes in `T` and absorbs it
(`lens_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W SP : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8]

theorem gh_tFrame {St W SP : Addr} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] m m') :
    Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

/-- Zeroing `T`: two stores. -/
theorem zeroT_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] s =
        some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := VG.Proof.AesGcm.X86_64.in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; rfl
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Cmac.bytesAt_store2, Cmac.le8_zero]; rfl

theorem zeroT_frame (m : Mem) (p : Addr) :
    Frame [⟨p, 16⟩] m ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) :=
  Cmac.frame_store2 _ _ _

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add, VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬xs.length + i < xs.length by omega]

/-- Before `flush yo` (or `lens yo`): GHASH has absorbed `x`. -/
structure FlIn (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOut (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP yo) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : VG.Proof.AesGcm.X86_64.FlIn Ctx St W SP yo H x s)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flush v.callees yo) s (VG.Proof.AesGcm.X86_64.FlOut Ctx St W SP yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s .rbx hbx (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] ++
          ptr .rdi .r15 tO ++ ptr .rsi .r14 32 ++ [.mov .rcx (.reg .rbx)]) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
          (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = W + BitVec.ofNat 64 96 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (x.length % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr := by
      have w₁ := VG.Proof.AesGcm.X86_64.in_off he₁.perm.w (show 96 + 8 ≤ 2560 by decide) (by decide)
      have w₂ := VG.Proof.AesGcm.X86_64.in_off he₁.perm.w (show 104 + 8 ≤ 2560 by decide) (by decide)
      refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, VG.Proof.AesGcm.X86_64.add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h15]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁, hbx]
      · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have lp : LoopPre s₂ (St + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 96) (x.length % 16) :=
      ⟨hsi, hdi, hcx, by omega, by omega, VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by omega)), he₂.perm.wC (by omega),
        L.st_w (by omega) (.inr ⟨by decide, by omega⟩)⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- The memory so far.
    have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact VG.Proof.AesGcm.X86_64.zeroT_frame _ _
    have hB₂ : bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16) =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) :=
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
        (by omega)
    have hlen := VG.Proof.AesGcm.X86_64.length_bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16)
    have fc : Frame [⟨W + BitVec.ofNat 64 96, x.length % 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]; exact VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hlen
    have f₃ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
      fz.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    have hT : bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16 =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ zeros (16 - x.length % 16) := by
      rw [hm₃, VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hB₂]
      refine congrArg (_ ++ ·) ?_
      have := VG.Proof.AesGcm.X86_64.zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
      rw [← hm₂, show (16 : Nat) = x.length % 16 + (16 - x.length % 16) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add] at this
      have e := congrArg (List.drop (x.length % 16)) this
      rw [List.drop_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _)] at e
      rw [e, show x.length % 16 + (16 - x.length % 16) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
      rfl
    have hY₃ : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
      blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
    refine WP.mono (VG.Proof.AesGcm.X86_64.ghash1_ok v L hyo he₃ .r15 96 (.inr rfl) (P := W + BitVec.ofNat 64 96) (by rw [he₃.r15])
      (by decide) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (L.stk_w (by decide)) (VG.Proof.AesGcm.X86_64.covers_left (he₃.perm.wC (by decide)))) fun s₄ g => ?_
    refine ⟨g.env he₃, ?_, ?_, ?_⟩
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hH₃]
    · intro ha
      refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16) hT ?_
      rw [g.out, hY₃, hH₃]; rfl
    · refine (f₃.sub fun r hr => ?_).trans (VG.Proof.AesGcm.X86_64.gh_tFrame g.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

omit L hyo in
theorem bswap64_eq : X86_64.bswap64 = byteRev64 := rfl

omit L hyo in
/-- `[8 r]₆₄` into `W + o`. -/
theorem be64Store_ok (s : State) (r : Reg) (_hr : r ≠ .rax) (o : Nat) (ho : o + 8 ≤ 2560) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (be64Store r o) s = some s' ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 o) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr r).toNat))) ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := VG.Proof.AesGcm.X86_64.in_off hw ho (by decide)
  refine ⟨_, by simp only [be64Store]; xrun [h15, w₁], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, VG.Proof.AesGcm.X86_64.times8_val, VG.Proof.AesGcm.X86_64.bswap64_eq]
  · intro r' hr'; simp [gpr_setReg, hr']
  all_goals rfl

/-- The lengths block of `rbx` and `rbp` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (lens v.callees yo) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (St + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat)] ∧
      Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP yo) s.mem s'.mem := by
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.be64Store_ok s .rbx (by decide) tO (by decide) he.r15 he.perm.w
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.be64Store_ok s₁ .rbp (by decide) (tO + 8) (by decide) he₁.r15
    he₁.perm.w
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  have hm : s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr .rbx).toNat)))).writeW
      (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr .rbp).toNat))) := by
    rw [hm₂, hm₁, hg₁ _ (by decide), VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; rfl
  have fT : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm]; exact Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 96) 16 = lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat := by
    rw [hm, Cmac.bytesAt_store2, Proof.Gcm.le8_byteRev64, Proof.Gcm.le8_byteRev64, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl
  have hY₂ : blockAt s₂.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  refine WP.mono (VG.Proof.AesGcm.X86_64.ghash1_ok v L hyo he₂ .r15 96 (.inr rfl) (P := W + BitVec.ofNat 64 96) (by rw [he₂.r15])
    (by decide) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by decide)))) fun s₃ g => ?_
  refine ⟨g.env he₂, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), hH₂]
  · have hb : blockAt s₂.mem (W + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat) := by rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, hb]
  · refine (fT.sub fun r hr => ?_).trans (VG.Proof.AesGcm.X86_64.gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Crypt`. -/
section

/-!
# AES-GCM on x86-64: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `rbp` bytes at `r12`, where `rbx` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block (`cryptHead`),
whole blocks with `vg_aes_ctr32` (`cryptWhole`), then a new keystream block
for the last bytes (`cryptTail`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `SP`. -/
structure DataW (Ctx St W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  ok : VG.Proof.AesGcm.X86_64.DataOk St W SP s D n
  wr : Covers [⟨D, n⟩] s.wr
  ctx : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩

theorem DataW.of_eq {Ctx St W SP : Addr} {s s' : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.drop {Ctx St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n)
    {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s (D + BitVec.ofNat 64 k) (n - k) :=
  ⟨h.ok.drop hk, VG.Proof.AesGcm.X86_64.covers_off h.wr (by omega) h.ok.lt, h.ctx.sub_right (Offset.sub_base D (by omega))⟩

theorem DataW.take {Ctx St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n)
    {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D k :=
  ⟨h.ok.take hk, fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
   h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m Ctx (16 * (R + 1)))

/-- The number of rounds is kept at `W + 176`. -/
def RoundsAt (m : Mem) (W : Addr) (R : Nat) : Prop :=
  m.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14)

/-- The regions `crypt` writes. -/
abbrev crFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨St + BitVec.ofNat 64 48, 32⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 (P % 16)
  data : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  le : j ≤ n
  r12 : s.gpr .r12 = D + BitVec.ofNat 64 j
  rbp : s.gpr .rbp = BitVec.ofNat 64 (n - j)
  data : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86_64.crFrame St W SP D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb (P + n)
  out : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D n = xorKs (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb P (bytesAt m₀ D n)
  frame : Frame (VG.Proof.AesGcm.X86_64.crFrame St W SP D n) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.crFrame St W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem rounds_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.crFrame St W SP D n, (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨Ctx, 256⟩ : Region).Disjoint r)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : VG.Proof.AesGcm.X86_64.ciphOf m' Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [VG.Proof.AesGcm.X86_64.ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

omit L in
theorem rounds_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r) {R : Nat} (h : VG.Proof.AesGcm.X86_64.RoundsAt m W R) :
    VG.Proof.AesGcm.X86_64.RoundsAt m' W R :=
  ⟨by rw [hf.readW (r := ⟨W + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _) hd (by decide)]; exact h.1, h.2⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Tag`. -/
section

/-!
# AES-GCM on x86-64: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `rbx` and `rbp` bytes, copies the accumulator `S` to `W + o` and
XORs `CIPH_K(J₀)` into it with `vg_aes_ctr32`, from the counter block `J₀`
at the state (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W SP : Addr) (o : Nat) : List Region :=
  [⟨St, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩,
    below SP 8]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (Ctx St W SP : Addr) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R J)
  frame : Frame (VG.Proof.AesGcm.X86_64.tagFrame St W SP o) m₀ s.mem
  /-- The call of `vg_aes_ctr32` left the next counter block, the first one of
  the data, at `St`. -/
  j : blockAt s.mem St = Spec.Gcm.inc32 J

/-- `tag o` before the call of `vg_aes_ctr32`, from `m₀`: its arguments, and
the accumulator with the lengths block at `W + o`. -/
structure TagMid (Ctx St W SP : Addr) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  call : CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R
  ciph : VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R
  j : blockAt s.mem St = J
  y : blockAt s.mem (W + BitVec.ofNat 64 o) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  frame : Frame (VG.Proof.AesGcm.X86_64.tagFrame St W SP o) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

omit L in
theorem bytesAt_copy2 (m : Mem) {p q : Addr} (hd : (⟨p, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    bytesAt ((m.writeW p (m.readW q 64)).writeW (p + BitVec.ofNat 64 8)
      ((m.writeW p (m.readW q 64)).readW (q + BitVec.ofNat 64 8) 64)) p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_store2, Mem.readW_writeW_sep (Region.Disjoint.sep hd.symm (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide), Cmac.le8_readW, Cmac.le8_readW, ← Cmac.bytesAt_split]

/-- `tag o` up to the call of `vg_aes_ctr32`. -/
theorem tagMid_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) (hJ : blockAt s.mem St = J) :
    WP isa (.seq (lens v.callees 16) (.block (([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] : List Instr) ++ ptr .rcx .r15 o ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO))) s (VG.Proof.AesGcm.X86_64.TagMid Ctx St W SP o R H (blockAt s.mem (St + BitVec.ofNat 64 16)) J
      (s.gpr .rbx).toNat (s.gpr .rbp).toNat s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.lens_ok v L (yo := 16) (.inr rfl) he hH) fun s₁ ⟨he₁, hH₁, hY₁, f₁⟩ => ?_)
  have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
  have dJ : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP 16, (⟨St, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₁ : blockAt s₁.mem St = J := by rw [blockAt_frame f₁ dJ, hJ]
  have hR₁ : VG.Proof.AesGcm.X86_64.RoundsAt s₁.mem W R := VG.Proof.AesGcm.X86_64.rounds_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm) hR
  have hc₁ : VG.Proof.AesGcm.X86_64.ciphOf s₁.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R := VG.Proof.AesGcm.X86_64.ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm) hR.2
  have r₁ := he₁.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₂ := he₁.perm.stR (show 24 + 8 ≤ 80 by decide)
  have r₃ := he₁.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have w₁ := he₁.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₂ := he₁.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have dsep : (⟨W + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8, 8⟩ := by
    rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
    exact (L.st_w (a := 24) (n := 8) (by decide) (by omega)).symm
  obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)),
        .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
        .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₁ = some s₂ ∧
      s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).writeW
        (W + BitVec.ofNat 64 o + BitVec.ofNat 64 8)
        ((s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).readW
          (St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 64) ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 o ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (W + BitVec.ofNat 64 o) x).writeW
        (W + BitVec.ofNat 64 (o + 8)) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
      intro m x y
      rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.w_w (a := 176) (n := 8) (d := o + 8) (k := 8) (by omega)
          (by decide) (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
        Mem.readW_writeW_sep (Region.Disjoint.sep (L.w_w (a := 176) (n := 8) (d := o) (k := 8) (by omega)
          (by decide) (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    have e24 : St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = St + BitVec.ofNat 64 24 := VG.Proof.AesGcm.X86_64.add_ofNat_assoc ..
    have eo : W + BitVec.ofNat 64 o + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (o + 8) := VG.Proof.AesGcm.X86_64.add_ofNat_assoc ..
    rw [e24, eo]
    refine ⟨_, by xrun [h13, h14, h15, r₁, r₂, r₃, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hsep, hR₁.1]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  have f₂ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s₁.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 o) 16 = bytesAt s₁.mem (St + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, VG.Proof.AesGcm.X86_64.bytesAt_copy2 _ dsep]
  have dJo : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem St = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, hJ₁]
  have hc₂ : VG.Proof.AesGcm.X86_64.ciphOf s₂.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R := by
    rw [VG.Proof.AesGcm.X86_64.ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) hR.2, hc₁]
  have hR₂ : VG.Proof.AesGcm.X86_64.RoundsAt s₂.mem W R := VG.Proof.AesGcm.X86_64.rounds_frame f₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by decide) (by omega)) hR₁
  have hS : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  have hcall : CtrCall s₂ Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1 := by
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hR.2, by have := L.ww; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
      by simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      dJo, hS, L.w_w (by omega) (by omega) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
    · rw [hk]; simpa using L.stk_st (a := 0) (n := 16) (by decide)
    · rw [hk]; exact L.stk_w (by omega)
    · rw [hk]; exact L.stk_w (by decide)
    · refine VG.Proof.AesGcm.X86_64.covers_cons ?_ (VG.Proof.AesGcm.X86_64.covers_cons ?_ (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by omega)))
        (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by decide)))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (d := 0) (n := 16) (by decide))
    · exact VG.Proof.AesGcm.X86_64.covers_cons (by simpa using he₂.perm.stC (d := 0) (n := 16) (by decide))
        (VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.wC (by omega)) (he₂.perm.wC (by decide)))
  refine ⟨he₂, hcall, hR₂, hc₂, hJ₂, ?_, ?_⟩
  · rw [blockAt, hT, ← blockAt, hY₁]
  · have fA : Frame (VG.Proof.AesGcm.X86_64.tagFrame St W SP o) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    exact fA.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) (hJ : blockAt s.mem St = J) :
    WP isa (tag v.callees o) s (VG.Proof.AesGcm.X86_64.TagOut Ctx St W SP o R H (blockAt s.mem (St + BitVec.ofNat 64 16)) J
      (s.gpr .rbx).toNat (s.gpr .rbp).toNat s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.tagMid_ok v L ho he hH hR hJ) fun s₂ M => ?_))
  have hk := M.env.rsp
  refine WP.mono (ctr_call v.ctr M.call) fun s₃ g => ?_
  have gout := g.out
  rw [VG.Proof.AesGcm.X86_64.blocksAt_one, VG.Proof.AesGcm.X86_64.blocksAt_one, VG.Proof.AesGcm.X86_64.ctr32_single, List.cons.injEq] at gout
  refine ⟨M.env.of_saved g.saved g.rd g.wr, ?_, ?_, ?_, by rw [g.ctr, M.j]; rfl⟩
  · refine VG.Proof.AesGcm.X86_64.rounds_frame g.frame (fun r hr => ?_) M.rounds
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 16) (d := 176) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (by omega) (by decide) (by omega)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [hk]; exact (L.stk_w (by decide)).symm
  · rw [Cmac.bytesAt_blockAt, gout.1, M.j,
      show Spec.Gcm.aesWith R (bytesAt s₂.mem Ctx (16 * (R + 1))) = VG.Proof.AesGcm.X86_64.ciphOf s₂.mem Ctx R from rfl, M.ciph, M.y]
  · refine M.frame.trans (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Region.sub_prefix (base := St) (show 16 ≤ 32 by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.J0`. -/
section

/-!
# AES-GCM on x86-64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`rbp`-byte nonce at `r12` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_ok`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_ok`). `initState` then
zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
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

theorem bswap32_eq : X86_64.bswap32 = byteRev32 := rfl

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (St W SP : Addr) : List Region :=
  [⟨St, 80⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP 8]

/-- Before `j0`: the `n`-byte nonce at `Np`. -/
structure J0In (Ctx St W SP : Addr) (H : Block) (Np : Addr) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  r12 : s.gpr .r12 = Np
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  data : VG.Proof.AesGcm.X86_64.DataOk St W SP s Np n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  frame : Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

theorem ctx_j0Frame : ∀ r ∈ VG.Proof.AesGcm.X86_64.j0Frame St W SP, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : Addr} {s : State} (h : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np 12 s) :
    WP isa (.block j012) s (VG.Proof.AesGcm.X86_64.J0Mid Ctx St W SP H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have h14 := he.r14
  have hd := h.data
  have r₀ := VG.Proof.AesGcm.X86_64.in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := VG.Proof.AesGcm.X86_64.in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := VG.Proof.AesGcm.X86_64.in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  have h12 := h.r12
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem St (s.mem.readW Np 32) (s.mem.readW (Np + BitVec.ofNat 64 4) 32)
        (s.mem.readW (Np + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [j012]; xrun [h12, h14, r₀, r₁, r₂, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcm.X86_64.ww32, store4, h12, h14,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm]; simpa using Cmac.frame_store4 (m := s.mem) St _ _ _ _
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide)) hrd hwr,
    ?_, ?_, VG.Proof.AesGcm.X86_64.st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, VG.Proof.AesGcm.X86_64.bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, VG.Proof.AesGcm.X86_64.bytesAt_add,
        VG.Proof.AesGcm.X86_64.add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _), blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, VG.Proof.AesGcm.X86_64.le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.X86_64.J0Mid Ctx St W SP H iv m₀ s) :
    WP isa (.block initState) s (VG.Proof.AesGcm.X86_64.J0Out Ctx St W SP H iv m₀) := by
  have he := h.env
  have h14 := he.r14
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
  generalize hw : s.mem.readW (St + BitVec.ofNat 64 12) 32 = w
  have split : initState =
      [.mov32 .rax (.mem (at_ .r14 0)), .mov32 .rcx (.mem (at_ .r14 4)), .mov32 .rdx (.mem (at_ .r14 8)),
        .mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi] ++
      [.store32 (at_ .r14 48) .rax, .store32 (at_ .r14 52) .rcx, .store32 (at_ .r14 56) .rdx,
        .store32 (at_ .r14 60) .rsi, .mov32 .rax (imm 0), .store (at_ .r14 16) .rax, .store (at_ .r14 24) .rax] := rfl
  obtain ⟨s₁, run₁, ax, cx, dx, si, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov32 .rax (.mem (at_ .r14 0)), .mov32 .rcx (.mem (at_ .r14 4)), .mov32 .rdx (.mem (at_ .r14 8)),
        .mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi] s = some s₁ ∧
      s₁.gpr .rax = (s.mem.readW St 32).setWidth 64 ∧
      s₁.gpr .rcx = (s.mem.readW (St + BitVec.ofNat 64 4) 32).setWidth 64 ∧
      s₁.gpr .rdx = (s.mem.readW (St + BitVec.ofNat 64 8) 32).setWidth 64 ∧
      s₁.gpr .rsi = (byteRev32 (byteRev32 w + 1)).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, r₀, r₁, r₂, r₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, BitVec.add_zero]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, VG.Proof.AesGcm.X86_64.ww32, VG.Proof.AesGcm.X86_64.bswap32_eq, hw]; rfl
    · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
    all_goals rfl
  have h14' : s₁.gpr .r14 = St := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide), h14]
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa
      [.store32 (at_ .r14 48) .rax, .store32 (at_ .r14 52) .rcx, .store32 (at_ .r14 56) .rdx,
        .store32 (at_ .r14 60) .rsi, .mov32 .rax (imm 0), .store (at_ .r14 16) .rax, .store (at_ .r14 24) .rax] s₁ =
        some s' ∧
      s'.mem = ((store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32) (s.mem.readW (St + BitVec.ofNat 64 4) 32)
        (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))).writeW (St + BitVec.ofNat 64 16)
          (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [← hwr₁] at w₀ w₁ w₂ w₃ z₀ z₁
    refine ⟨_, by xrun [h14', w₀, w₁, w₂, w₃, z₀, z₁], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcm.X86_64.ww32, store4, ax, cx, dx, si, hm₁,
        VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
      rfl
    · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
    · simp [rd_setReg, hrd₁]
    · simp [wr_setReg, hwr₁]
  rw [split]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s', run, ?_⟩⟩)
  have f₄ := Cmac.frame_store4 (m := s.mem) (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))
  have fz := VG.Proof.AesGcm.X86_64.zeroT_frame (store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1)))
    (St + BitVec.ofNat 64 16)
  rw [← hm] at fz
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
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide)) hrd hwr,
    ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (VG.Proof.AesGcm.X86_64.st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, VG.Proof.AesGcm.X86_64.zeroT_bytes]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← h.j0, blockAt,
      Cmac.ofBytes_rev4, ← Cmac.le4_readW s.mem St, ← Cmac.le4_readW, ← Cmac.le4_readW, VG.Proof.AesGcm.X86_64.ofBytes_le4, hw,
      Cmac.byteRev32_byteRev32, VG.Proof.AesGcm.X86_64.inc32_words]

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.absFrame St W SP 0) m m') : Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP 0) m m') : Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `aux` is apart from what `absorb 0`, `flush 0` and `lens 0` write. -/
theorem aux_absFrame : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame St W SP 0, (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem aux_tFrame : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP 0, (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s) (hn : n ≠ 12) :
    WP isa (j0hash v.callees) s (VG.Proof.AesGcm.X86_64.J0Mid Ctx St W SP H (bytesAt s.mem Np n) s.mem) := by
  have he := h.env
  have hd := h.data
  have hlt := hd.lt
  have h14 := he.r14; have h15 := he.r15
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have wa := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax,
      .store (at_ .r14 8) .rax, .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
        (St + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 216)
        (BitVec.ofNat 64 n) ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, h15, z₀, z₁, wa], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h.rbp, VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; rfl
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have fz := VG.Proof.AesGcm.X86_64.zeroT_frame s.mem (St + BitVec.ofNat 64 0)
  have fa : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] ((s.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
      (St + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64)) s₁.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₁ : Frame [⟨St + BitVec.ofNat 64 0, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] s.mem s₁.mem :=
    (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans
      (fa.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  have dD : ∀ r ∈ [(⟨St + BitVec.ofNat 64 0, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩],
      (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.st.sub_right (Lay.stSub (by decide))
    · exact hd.w.sub_right (Lay.wSub (by decide))
  have dH : ∀ r ∈ [(⟨St + BitVec.ofNat 64 0, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩],
      (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.ctx_st (by decide) (by decide)
    · exact L.ctx_w (by decide) (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n := bytesAt_frame f₁ dD (by omega)
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [blockAt_frame f₁ dH, h.hH]
  have hY₁ : blockAt s₁.mem (St + BitVec.ofNat 64 0) = 0 := by
    rw [blockAt, bytesAt_frame fa (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (a := 0) (n := 16) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)) (by decide),
      VG.Proof.AesGcm.X86_64.zeroT_bytes]
    decide
  have hai : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 0 H [] Np n s₁ :=
    ⟨he₁, by rw [hg₁ _ (by decide) (by decide), h.r12], by rw [hg₁ _ (by decide) (by decide), h.rbp],
      by rw [hbx₁]; rfl, hd.of_eq hrd₁ hwr₁, hH₁⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.absorb_ok v L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  have hn₂ : s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [ho.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.aux_absFrame L) (by decide),
      hm₁, Mem.readW_writeW_self64]
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (VG.Proof.AesGcm.X86_64.ctx_absFrame L (.inl rfl)), hH₁]
  have ra := he₂.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 auxO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 (n % 16) ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
    rw [VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hlt, VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
    refine ⟨_, by xrun [he₂.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hn₂, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hfi : VG.Proof.AesGcm.X86_64.FlIn Ctx St W SP 0 H (bytesAt s.mem Np n) s₃ :=
    ⟨he₃, by rw [hm₃, hH₂]⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 0) (.inl rfl) hfi (by rw [hbx₃, VG.Proof.AesGcm.X86_64.length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  have hn₄ : s₄.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.aux_tFrame L) (by decide),
      hm₃, hn₂]
  have ra₄ := he₄.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov32 .rbx (imm 0),
      .mov .rbp (.mem (at_ .r15 auxO))] s₄ = some s₅ ∧
      s₅.gpr .rbx = BitVec.ofNat 64 0 ∧ s₅.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, ra₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hn₄]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  refine WP.mono (VG.Proof.AesGcm.X86_64.lens_ok v L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hm₅]; exact hf.hH)) fun s₆ ⟨he₆, hH₆, hY₆, f₆⟩ => ?_
  refine ⟨he₆, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hm₃]; exact hab₂)).whole_eq (by
      simp only [List.length_append, VG.Proof.AesGcm.X86_64.length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [Proof.Gcm.j0_eq H (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; exact hn), VG.Proof.AesGcm.X86_64.length_bytesAt, ← hw, ← hm₅,
      hbx₅, hbp₅, VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt (by decide), VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hlt] at *
    simpa using hY₆
  · have g₁ : Frame (VG.Proof.AesGcm.X86_64.j0Frame St W SP) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have g₄ := VG.Proof.AesGcm.X86_64.t_j0Frame hf.frame
    have g₆ := VG.Proof.AesGcm.X86_64.t_j0Frame f₆
    rw [hm₃] at g₄
    rw [hm₅] at g₆
    exact ((g₁.trans (VG.Proof.AesGcm.X86_64.abs_j0Frame ho.frame)).trans g₄).trans g₆

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s) :
    WP isa (j0 v.callees) s (VG.Proof.AesGcm.X86_64.J0Out Ctx St W SP H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rbp (imm 12)] s = some s₁ ∧
      s₁.zf = some (decide (n = 12)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags, h.rbp]
      exact congrArg some (VG.Proof.AesGcm.X86_64.sub_beq hlt (by decide))
    all_goals rfl
  have h₁ : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hm₁]; exact h.hH, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← hm₁]
  refine WP.seq (WP.ite (decide (n = 12)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (VG.Proof.AesGcm.X86_64.j012_ok L h₁) fun _ hm => VG.Proof.AesGcm.X86_64.initState_ok L hm
  · exact WP.mono (VG.Proof.AesGcm.X86_64.j0hash_ok v L h₁ (by simpa using hf)) fun _ hm => VG.Proof.AesGcm.X86_64.initState_ok L hm

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Cmp`. -/
section

/-!
# AES-GCM on x86-64: checking a received tag (`tagLenOk`, `recv`, `cmp o`)

Untrusted: everything here is checked by Lean. `tagLenOk` clears ZF iff
§5.2.1.2 allows a tag of `rbx` bytes (`tagLenOk_ok`); `recv` pads the `rbx`
bytes of the received tag at `rsi` with zeros at `W + 256` (`recv_ok`); `cmp o`
pads the first `rbx` bytes of the tag at `W + o` at `W + 240` and leaves 1 in
`rax` if they are the received ones, 0 if not (`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## The length -/

/-- `cmp r, k`. -/
theorem cmpImm_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hk : k < 2 ^ 31) :
    ∃ s', runBlock isa [.alu .cmp r (imm k)] s = some s' ∧ s'.zf = some (decide (n = k)) ∧
      s'.cf = some (decide (n < k)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zf_arithFlags, h, VG.Proof.AesGcm.X86_64.imm_eq hk]; exact congrArg some (VG.Proof.AesGcm.X86_64.sub_beq hn (by omega))
  · rw [cf_arithFlags, h, VG.Proof.AesGcm.X86_64.imm_eq hk, VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt (by omega)]
  all_goals rfl

theorem setRcx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov32 .rcx (imm k)] s = some s' ∧ s'.gpr .rcx = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- What `tagLenOk` keeps. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.AesGcm.X86_64.Keeps s₁ s₂) (h₂ : VG.Proof.AesGcm.X86_64.Keeps s₂ s₃) : VG.Proof.AesGcm.X86_64.Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- `rcx := 1` if the condition holds. -/
theorem setIf_ok {s : State} {c : Cond} {b : Bool} (hc : isa.eval c s = some b) {k : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 k) (_hk : k ≤ 1) :
    WP isa (.ite c (.block [.mov32 .rcx (imm 1)]) (.block [])) s fun s' => VG.Proof.AesGcm.X86_64.Keeps s s' ∧
      s'.gpr .rcx = BitVec.ofNat 64 (if b then 1 else k) := by
  refine WP.ite b hc (fun ht => ?_) (fun hf => ?_)
  · obtain ⟨s', run, h1, hg, _, _, hm, hrd, hwr⟩ := VG.Proof.AesGcm.X86_64.setRcx_ok s 1 (by decide)
    exact WP.of_runBlock ⟨s', run, ⟨hg, hm, hrd, hwr⟩, by rw [h1, ht]; rfl⟩
  · exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, by rw [hrcx, hf]; rfl⟩

/-- `tagLenOk`: ZF is clear iff the tag length is allowed. -/
theorem tagLenOk_ok (s : State) {t : Nat} (h : s.gpr .rbx = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.zf = some (!Spec.Gcm.tagLenOk t) ∧ VG.Proof.AesGcm.X86_64.Keeps s s' := by
  obtain ⟨s₁, run₁, hcx₁, hg₁, -, -, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.setRcx_ok s 0 (by decide)
  have hbx₁ : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hg₁ _ (by decide), h]
  obtain ⟨s₂, run₂, hz₂, -, hg₂, hm₂, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.cmpImm_ok s₁ .rbx hbx₁ ht (show 4 < 2 ^ 31 by decide)
  have k₂ : VG.Proof.AesGcm.X86_64.Keeps s s₂ := ⟨fun r hr => by rw [hg₂, hg₁ r hr], hm₂.trans hm₁, hrd₂.trans hrd₁, hwr₂.trans hwr₁⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.setIf_ok (VG.Proof.AesGcm.X86_64.eval_e hz₂) (by rw [hg₂, hcx₁]) (k := 0) (by decide)) fun s₃ ⟨k₃, hcx₃⟩ => ?_)
  have hbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 t := by rw [k₃.gpr _ (by decide), hg₂, hbx₁]
  obtain ⟨s₄, run₄, hz₄, -, hg₄, hm₄, hrd₄, hwr₄⟩ := VG.Proof.AesGcm.X86_64.cmpImm_ok s₃ .rbx hbx₃ ht (show 8 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.setIf_ok (VG.Proof.AesGcm.X86_64.eval_e hz₄) (k := if decide (t = 4) then 1 else 0) (by rw [hg₄, hcx₃])
    (by split <;> decide)) fun s₅ ⟨k₅, hcx₅⟩ => ?_)
  have hbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 t := by rw [k₅.gpr _ (by decide), hg₄, hbx₃]
  obtain ⟨s₆, run₆, -, hc₆, hg₆, hm₆, hrd₆, hwr₆⟩ := VG.Proof.AesGcm.X86_64.cmpImm_ok s₅ .rbx hbx₅ ht (show 12 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have k₆ : VG.Proof.AesGcm.X86_64.Keeps s s₆ := ((k₂.trans k₃).trans ⟨fun r _ => by rw [hg₄], hm₄, hrd₄, hwr₄⟩).trans k₅ |>.trans
    ⟨fun r _ => by rw [hg₆], hm₆, hrd₆, hwr₆⟩
  generalize hk : (if decide (t = 8) then 1 else if decide (t = 4) then 1 else 0) = k at hcx₅
  have hk1 : k ≤ 1 := by rw [← hk]; split <;> (try split) <;> decide
  have hcx₆ : s₆.gpr .rcx = BitVec.ofNat 64 k := by rw [hg₆, hcx₅]
  have hite : WP isa (.ite .b (.block [])
      (.seq (.block [.alu .cmp .rbx (imm 17)]) (.ite .b (.block [.mov32 .rcx (imm 1)]) (.block [])))) s₆
      (fun s₇ => VG.Proof.AesGcm.X86_64.Keeps s s₇ ∧ s₇.gpr .rcx = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0)) := by
    refine WP.ite (decide (t < 12)) (VG.Proof.AesGcm.X86_64.eval_b hc₆) (fun hlt => ?_) (fun hge => ?_)
    · refine WP.block_nil ⟨k₆, ?_⟩
      rw [hcx₆, ← hk]
      have : t < 12 := by simpa using hlt
      simp only [Spec.Gcm.tagLenOk]
      rcases (show t = 4 ∨ t = 8 ∨ (t ≠ 4 ∧ t ≠ 8) by omega) with rfl | rfl | ⟨h4, h8⟩
      · rfl
      · rfl
      · simp [h4, h8, show ¬ 12 ≤ t by omega]
    · have hbx₆ : s₆.gpr .rbx = BitVec.ofNat 64 t := by rw [hg₆, hbx₅]
      obtain ⟨s₇, run₇, -, hc₇, hg₇, hm₇, hrd₇, hwr₇⟩ := VG.Proof.AesGcm.X86_64.cmpImm_ok s₆ .rbx hbx₆ ht (show 17 < 2 ^ 31 by decide)
      refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
      refine WP.mono (VG.Proof.AesGcm.X86_64.setIf_ok (VG.Proof.AesGcm.X86_64.eval_b hc₇) (by rw [hg₇, hcx₆]) hk1) fun s₈ ⟨k₈, hcx₈⟩ =>
        ⟨k₆.trans ⟨fun r _ => by rw [hg₇], hm₇, hrd₇, hwr₇⟩ |>.trans k₈, ?_⟩
      rw [hcx₈, ← hk]
      have : 12 ≤ t := by simpa using hge
      simp only [Spec.Gcm.tagLenOk]
      by_cases h17 : t < 17
      · simp [h17, show t ≠ 4 by omega, show t ≠ 8 by omega, this, show t ≤ 16 by omega]
      · simp [h17, show t ≠ 4 by omega, show t ≠ 8 by omega, show ¬ t ≤ 16 by omega]
  refine WP.seq (WP.mono hite fun s₇ ⟨k₇, hcx₇⟩ => ?_)
  obtain ⟨s₈, run₈, hz₈, hg₈, hm₈, hrd₈, hwr₈⟩ := VG.Proof.AesGcm.X86_64.test_ok s₇ .rcx hcx₇ (by split <;> decide)
  refine WP.of_runBlock ⟨s₈, run₈, ?_, k₇.trans ⟨fun r _ => by rw [hg₈], hm₈, hrd₈, hwr₈⟩⟩
  rw [hz₈]; cases Spec.Gcm.tagLenOk t <;> rfl

/-! ## Padded tags -/

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes (m : Mem) (P : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P xs) P 16 =
      xs ++ zeros (16 - xs.length) := by
  rw [VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  have := VG.Proof.AesGcm.X86_64.zeroT_bytes m P
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add] at this
  have e := congrArg (List.drop xs.length) this
  rw [List.drop_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_split m p, Cmac.bytesAt_split m q, ← Cmac.le8_readW, ← Cmac.le8_readW, ← Cmac.le8_readW,
    ← Cmac.le8_readW]
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
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Cmac.length_le8, Cmac.length_le8])
    rw [VG.Proof.AesGcm.X86_64.le8_inj h₁, VG.Proof.AesGcm.X86_64.le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
/-- `recv`: the `t` bytes of the received tag at `T` (in `rsi`), padded at `W + 256`. -/
theorem recv_ok {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) {t : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 t)
    (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : Addr} (hsi : s.gpr .rsi = T) (hT : Covers [⟨T, t⟩] (s.rd ++ s.wr))
    (dW : (⟨T, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) :
    WP isa recv s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem T t ++ zeros (16 - t) ∧
      Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧ s'.gpr .rbx = s.gpr .rbx := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi₁, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
        ptr .rdi .r15 rO ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 256 ∧ s₁.gpr .rsi = T ∧ s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hsi]
    · simp [gpr_setReg, hbx]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lp : LoopPre s₁ T (W + BitVec.ofNat 64 256) t :=
    ⟨hsi₁, hdi, hcx, h1, by omega, by rw [hrd₁, hwr₁]; exact hT, he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have fz : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.AesGcm.X86_64.zeroT_frame _ _
  have hR : bytesAt s₁.mem T t = bytesAt s.mem T t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := VG.Proof.AesGcm.X86_64.length_bytesAt s₁.mem T t
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_, ?_⟩
  · rw [hm₂, hm₁, VG.Proof.AesGcm.X86_64.pad_bytes _ _ _ (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; exact h16), VG.Proof.AesGcm.X86_64.length_bytesAt, ← hm₁, hR]
  · refine fz.trans ?_
    rw [hm₂]
    exact (VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide)]

/-- `cmp o`: 1 in `rax` iff the first `t` bytes of the tag at `W + o` are
the received tag `R`, padded at `W + 256`. -/
theorem cmp_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) {t : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {R : List Byte} (hRl : R.length = t)
    (hR : bytesAt s.mem (W + BitVec.ofNat 64 256) 16 = R ++ zeros (16 - t)) :
    WP isa (cmp o) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 o) t = R then 1 else 0) ∧
      Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 240 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 248 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
        ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 240 ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hoi : o < 2 ^ 31 := by omega
    refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15, VG.Proof.AesGcm.X86_64.imm_eq hoi]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W + BitVec.ofNat 64 o, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 240, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 240) t :=
    ⟨hsi, hdi, hcx, h1, by omega, VG.Proof.AesGcm.X86_64.covers_left (he₁.perm.wC (by omega)), he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.AesGcm.X86_64.zeroT_frame _ _
  have hT : bytesAt s₁.mem (W + BitVec.ofNat 64 o) t = bytesAt s.mem (W + BitVec.ofNat 64 o) t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := VG.Proof.AesGcm.X86_64.length_bytesAt s₁.mem (W + BitVec.ofNat 64 o) t
  have f₂ : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₂.mem := by
    refine fz.trans ?_
    rw [hm₂]
    exact (VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 240) 16 = bytesAt s.mem (W + BitVec.ofNat 64 o) t ++ zeros (16 - t) := by
    rw [hm₂, hm₁, VG.Proof.AesGcm.X86_64.pad_bytes _ _ _ (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; exact h16), VG.Proof.AesGcm.X86_64.length_bytesAt, ← hm₁, hT]
  have hR₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = R ++ zeros (16 - t) := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hR]
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have r₁ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have r₂ := he₂.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₃ := he₂.perm.wR (show 248 + 8 ≤ 2560 by decide)
  have r₄ := he₂.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have h15₂ := he₂.r15
  generalize hX : (s₂.mem.readW (W + BitVec.ofNat 64 240) 64 ^^^ s₂.mem.readW (W + BitVec.ofNat 64 256) 64) |||
    (s₂.mem.readW (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64 ^^^
      s₂.mem.readW (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) 64) = X
  have hXe : X = 0 ↔ bytesAt s.mem (W + BitVec.ofNat 64 o) t = R := by
    rw [← hX, VG.Proof.AesGcm.X86_64.words_eq, hV, hR₂]
    constructor
    · intro e; exact List.append_cancel_right e
    · intro e; rw [e]
  have e248 : W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 248 := VG.Proof.AesGcm.X86_64.add_ofNat_assoc ..
  have e264 : W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 264 := VG.Proof.AesGcm.X86_64.add_ofNat_assoc ..
  rw [e248, e264] at hX
  refine WP.run (Q := fun s₃ => s₃.gpr .rax = (if X = 0 then 1 else 0) ∧ s₃.gpr .r13 = s₂.gpr .r13 ∧
      s₃.gpr .r14 = s₂.gpr .r14 ∧ s₃.gpr .r15 = s₂.gpr .r15 ∧ s₃.gpr .rsp = s₂.gpr .rsp ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr)
    ⟨_, by xrun [h15₂, r₁, r₂, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ fun s₃ ⟨hax, h13, h14, h15', hsp, hm, hrd, hwr⟩ =>
      ⟨he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hrd hwr,
       by rw [hax]; simp only [hXe], hm ▸ f₂⟩
  · simp only [gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, ite_true, ite_false, reduceCtorEq, hX]
    by_cases e : X = 0
    · subst e; rfl
    · have : ¬ X.toNat < 1 := fun h => e (BitVec.eq_of_toNat_eq (by simp; omega))
      simp only [e, ite_false, show (1#64 : BitVec 64).toNat = 1 from rfl, this, decide_false]
      rfl
  all_goals rfl

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk`. -/
section

/-!
# AES-GCM on x86-64: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

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
  rw [VG.Proof.AesGcm.X86_64.bytesAt_add, VG.Proof.AesGcm.X86_64.bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, VG.Proof.AesGcm.X86_64.length_bytesAt]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n s.mem (min (16 - P % 16) n)) := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.minLen_ok s h.rbx h.rbp (by omega) hn') fun s₁ ⟨hcx, hg, hm, hrd, hwr⟩ => ?_)
  generalize hk : min (16 - P % 16) n = k at hcx ⊢
  have hk1 : 1 ≤ k := by omega
  have hk16 : P % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rdi (.reg .r12),
      .mov .rsi (.reg .r14), .alu .add .rsi (.reg .rbx), .alu .add .rsi (imm 64)] s₁ = some s₂ ∧
      s₂.gpr .rdi = D ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 (64 + P % 16) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg _ (by decide : Reg.r12 ≠ .rcx), h.r12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg _ (by decide : Reg.r14 ≠ .rcx), hg _ (by decide : Reg.rbx ≠ .rcx), he.r14, h.rbx,
        VG.Proof.AesGcm.X86_64.add_ofNat_assoc, Nat.add_comm]
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have lp : LoopPre s₂ (St + BitVec.ofNat 64 (64 + P % 16)) D k := by
    refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], hk1, by omega, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂, hrd, hwr]; exact VG.Proof.AesGcm.X86_64.covers_left (he.perm.stC (by omega))
    · rw [hwr₂, hwr]; exact (h.data.take hkn).wr
    · exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.seq (WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
  rw [hm₂, hm] at hm₃
  rw [hrd₂, hrd] at hrd₃
  rw [hwr₂, hwr] at hwr₃
  have hreg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₃.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [hg₃ r a b c, hg₂ r d e, hg r f]
  have h3rcx : s₃.gpr .rcx = BitVec.ofNat 64 k := by
    rw [hg₃ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide), hcx]
  have hxl := length_xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  obtain ⟨s₄, run₄, h12, hbp, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)] s₃ = some s₄ ∧
      s₄.gpr .r12 = D + BitVec.ofNat 64 k ∧ s₄.gpr .rbp = BitVec.ofNat 64 (n - k) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have e12 := hreg .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebp := hreg .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e12, h3rcx, h.r12]
    · simp [gpr_setReg, ebp, h3rcx, h.rbp, VG.Proof.AesGcm.X86_64.ofNat_sub hkn hn']
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have he₄ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide),
        hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  have hc₄ : VG.Proof.AesGcm.X86_64.ciphOf s₄.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R := by
    rw [hm₄]; exact VG.Proof.AesGcm.X86_64.ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx) h.rounds.2
  refine ⟨he₄, hkn, h12, hbp, h.data.of_eq (hrd₄.trans hrd₃) (hwr₄.trans hwr₃), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₄]; exact VG.Proof.AesGcm.X86_64.rounds_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.data.take hkn).ok.w.sub_right (Lay.wSub (by decide))).symm) h.rounds
  · intro hc₀
    rw [hm₄]
    refine (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega)
    rw [hxl] at e
    rw [hm₄, hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem D k) (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; exact hk16)
    rw [VG.Proof.AesGcm.X86_64.length_bytesAt, VG.Proof.AesGcm.X86_64.add_ofNat_assoc] at this
    exact this
  · rw [hm₄]
    exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesGcm.X86_64.split_disj hkn hn').symm) (by omega)
  · by_cases hkk : k = n
    · left; omega
    · right; omega
  · rw [hm₄]; exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
/-- The arguments of a call of `vg_aes_ctr32`, from `W + 176` and the state. -/
theorem ctrArgs_ok {R : Nat} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) :
    ∃ s', runBlock isa (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
        ptr .r9 .r15 scrO) s = some s' ∧
      s'.gpr .rdi = Ctx ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  have r₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  refine ⟨_, by xrun [h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h13]
  · simp [gpr_setReg, hR.1]
  · simp [gpr_setReg, h14]
  · simp [gpr_setReg, h15]
  · intro r a b c d; simp [gpr_setReg, a, b, c, d]
  all_goals rfl

omit L in
theorem CrMid.data_eq {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ j s) : bytesAt s.mem D n =
      bytesAt s.mem D j ++ bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) := by
  rw [← VG.Proof.AesGcm.X86_64.bytesAt_add, Nat.add_sub_cancel' h.le]

/-- The arguments of `cryptWhole`'s call of `vg_aes_ctr32`. -/
theorem cwCall_of {R : Nat} {D : Addr} {n j nb : Nat} {s₂ : State} (he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂)
    (hd : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s₂ D n) (hj : j ≤ n) (h16 : 16 * nb ≤ n - j) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hdi : s₂.gpr .rdi = Ctx) (hsi : s₂.gpr .rsi = BitVec.ofNat 64 R) (hdx : s₂.gpr .rdx = St + BitVec.ofNat 64 48)
    (hcx : s₂.gpr .rcx = D + BitVec.ofNat 64 j) (h8 : s₂.gpr .r8 = BitVec.ofNat 64 nb)
    (h9 : s₂.gpr .r9 = W + BitVec.ofNat 64 512) :
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R nb := by
  have hdj := (hd.drop hj).take (k := 16 * nb) h16
  have hk := he₂.rsp
  refine ⟨hdi, hsi, hdx, hcx, h8, h9, hR, hdj.ok.wrap,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    hdj.ctx.sub_left (Region.sub_prefix (by decide)),
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm, L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    hdj.ok.w.sub_right (Lay.wSub (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact hdj.ok.stk
  · rw [hk]; exact L.stk_w (by decide)
  · refine VG.Proof.AesGcm.X86_64.covers_cons ?_ (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons ?_
      (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by decide)))))
    · exact fun a m' ⟨r, hr, hc'⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
    · exact VG.Proof.AesGcm.X86_64.covers_left hdj.wr
  · exact VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.stC (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons hdj.wr (he₂.perm.wC (by decide)))

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ j s) (hc : VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) :
    WP isa (cryptWhole v.callees) s (VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ (j + 16 * ((n - j) / 16))) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain ⟨s₁, run₁, hcx, h8, h12, hbp, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ :=
    VG.Proof.AesGcm.X86_64.wholeSplit_ok .rcx .r8 (.inr ⟨rfl, rfl⟩) hn' h.le h.r12 h.rbp
  generalize hnb : (n - j) / 16 = nb at *
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hrd₁ hwr₁
  have hd₁ : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s₁ D n := h.data.of_eq hrd₁ hwr₁
  refine WP.ite (decide (nb = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    simp only [Nat.mul_zero, Nat.add_zero]
    refine WP.block_nil ⟨he₁, h.le, by rw [h12]; rfl, by rw [hbp]; rfl, hd₁, by rw [hm₁]; exact h.rounds,
      fun hc₀ => by rw [hm₁]; exact h.ctr hc₀, fun hc₀ => by rw [hm₁]; exact h.done hc₀, by rw [hm₁]; exact h.rest, h.whole,
      by rw [hm₁]; exact h.frame⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := (h.data.drop h.le).take (k := 16 * nb) h16
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, hm₂, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.ctrArgs_ok he₁ (by rw [hm₁]; exact h.rounds)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have hk := he₂.rsp
    have hcall := VG.Proof.AesGcm.X86_64.cwCall_of L he₂ (hd₁.of_eq hrd₂ hwr₂) h.le h16 h.rounds.2 hdi hsi hdx
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), hcx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h8]) h9
    refine WP.mono (ctr_call v.ctr hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    rw [hm₂, hm₁] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem) (dp := D + BitVec.ofNat 64 j)
      (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨he₂.of_saved g.saved g.rd g.wr, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hrd₂) (g.wr.trans hwr₂),
      ?_, ?_, ?_, ?_, .inr (by omega), ?_⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h12]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), hbp]
    · refine VG.Proof.AesGcm.X86_64.rounds_frame gframe (fun r hr => ?_) h.rounds
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (hdj.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [hk]; exact (L.stk_w (by decide)).symm
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add, VG.Proof.AesGcm.X86_64.bytesAt_add,
          List.take_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _), List.take_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact VG.Proof.AesGcm.X86_64.split_disj (D := D) (j := j) (n := n) h.le hn' |>.sub_right (Region.sub_prefix (by omega))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact (h.data.take h.le).ok.stk.symm) (by omega)
      exact VG.Proof.AesGcm.X86_64.done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hdis : ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨W + BitVec.ofNat 64 512, 2048⟩, below (s₂.gpr .rsp) 8],
          (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hrest := (h.data.drop (k := j + 16 * nb) (by omega))
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hrest.ok.st.sub_right (Lay.stSub (by decide))
        · rw [← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
          have := VG.Proof.AesGcm.X86_64.split_disj (D := D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega] at this
          exact this.symm
        · exact hrest.ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact hrest.ok.stk.symm
      rw [bytesAt_frame gframe hdis (by omega)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add,
          List.drop_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _), VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base D (by omega))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ j s) (hj : n - j < 16) (hc : VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) :
    WP isa (cryptTail v.callees) s (VG.Proof.AesGcm.X86_64.CrOut Ctx St W SP R icb P D n m₀) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s .rbp h.rbp (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.rounds, fun hc₀ => by rw [hm₁]; exact h.ctr hc₀,
      fun hc₀ => by rw [hm₁]; exact h.done hc₀,
      by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.drop h.le
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    have r₁ := he₁.perm.wR (show 176 + 8 ≤ 2560 by decide)
    have w₁ := he₁.perm.stW (show 64 + 8 ≤ 80 by decide)
    have w₂ := he₁.perm.stW (show 72 + 8 ≤ 80 by decide)
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
          .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
          ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
          (St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
        s₂.gpr .rcx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
        s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧
        s₂.rd = s.rd ∧ s₂.wr = s.wr := by
      have hR := h.rounds.1
      rw [← hm₁] at hR
      have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (St + BitVec.ofNat 64 64) x).writeW
          (St + BitVec.ofNat 64 72) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
        intro m x y
        rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 72) (n := 8) (by decide)
            (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
          Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 64) (n := 8) (by decide)
            (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
      refine ⟨_, by xrun [h13, h14, h15, w₁, w₂, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesGcm.X86_64.add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, hsep, hR]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg]
      · simp [gpr_setReg, h15]
      · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hk := he₂.rsp
    have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store2 _ _ _
    have hKS0 : blockAt s₂.mem (St + BitVec.ofNat 64 64) = 0 := by
      rw [blockAt, hm₂, VG.Proof.AesGcm.X86_64.zeroT_bytes]; decide
    have hCB : blockAt s₂.mem (St + BitVec.ofNat 64 48) = blockAt s.mem (St + BitVec.ofNat 64 48) :=
      blockAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by decide)) (by decide) (by decide)
    have hc₂ : VG.Proof.AesGcm.X86_64.ciphOf s₂.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R := by
      rw [VG.Proof.AesGcm.X86_64.ciph_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds.2, hc]
    have hcall : CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 := by
      refine ⟨hdi, hsi, hdx, hcx, h8, h9, h.rounds.2, by have := L.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
        (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
        L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
        L.st_st (.inl (by decide)) (by decide) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
        L.st_w (by decide) (.inr ⟨by decide, by decide⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
      · rw [hk]; exact L.stk_st (by decide)
      · rw [hk]; exact L.stk_st (by decide)
      · rw [hk]; exact L.stk_w (by decide)
      · refine VG.Proof.AesGcm.X86_64.covers_cons ?_ (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
          (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by decide))) (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by decide)))))
        exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · exact VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.stC (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.stC (by decide))
          (he₂.perm.wC (by decide)))
    refine WP.seq (WP.mono (ctr_call v.ctr hcall) fun s₃ g => ?_)
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    rw [VG.Proof.AesGcm.X86_64.blocksAt_one, VG.Proof.AesGcm.X86_64.blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
    have hKS : blockAt s₃.mem (St + BitVec.ofNat 64 64) = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R (blockAt s.mem (St + BitVec.ofNat 64 48)) := by
      rw [gout.1, ← hc₂, hCB]
    have hCB₃ : blockAt s₃.mem (St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt s.mem (St + BitVec.ofNat 64 48)) := by
      rw [gctr, hCB]; rfl
    have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he₂.of_saved g.saved g.rd g.wr
    obtain ⟨s₄, run₄, hdi₄, hsi₄, hcx₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
        ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r14 64 ++ [.mov .rcx (.reg .rbp)]) s₃ = some s₄ ∧
        s₄.gpr .rdi = D + BitVec.ofNat 64 j ∧ s₄.gpr .rsi = St + BitVec.ofNat 64 64 ∧
        s₄.gpr .rcx = BitVec.ofNat 64 (n - j) ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧
        s₄.wr = s₃.wr := by
      have e12 : s₃.gpr .r12 = D + BitVec.ofNat 64 j := by
        rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.r12]
      have ebp : s₃.gpr .rbp = BitVec.ofNat 64 (n - j) := by
        rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.rbp]
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, e12]
      · simp [gpr_setReg, he₃.r14]
      · simp [gpr_setReg, ebp]
      · intro r a b c; simp [gpr_setReg, a, b, c]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have lp : LoopPre s₄ (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
      refine ⟨hsi₄, hdi₄, hcx₄, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hrd₄, hwr₄, g.rd, g.wr]; exact VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by omega))
      · rw [hwr₄, g.wr, hwr₂]; exact hdj.wr
      · exact (hdj.ok.st.sub_right (Lay.stSub (by omega))).symm
    refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, hg₅, hrd₅, hwr₅⟩ => ?_
    rw [hm₄] at hm₅
    have hxl := length_xorBytes s₃.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)
    have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s₃.mem s₅.mem := by rw [hm₅]; exact VG.Proof.AesGcm.X86_64.writeBytes_frame' _ hxl
    have hd₃ : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      rw [← h.rest, bytesAt_frame gframe (fun r hr => ?_) (by omega), bytesAt_frame fz (fun r hr => ?_) (by omega)]
      · simp only [List.mem_singleton] at hr; subst hr; exact hdj.ok.st.sub_right (Lay.stSub (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdj.ok.st.sub_right (Lay.stSub (by decide))
        · exact hdj.ok.st.sub_right (Lay.stSub (by decide))
        · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact hdj.ok.stk.symm
    have ht := fun hc₀ => Proof.Gcm.ctr_tail (h.ctr hc₀) hw (m₁ := s₃.mem) hKS (by rw [hCB₃]) (d := bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j))
      (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; omega) (by rw [VG.Proof.AesGcm.X86_64.length_bytesAt]; omega)
    rw [VG.Proof.AesGcm.X86_64.length_bytesAt] at ht
    have dW : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hdj.ok.w.sub_right (Lay.wSub (by decide))).symm
    have dS : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
        (⟨St + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
      intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
      exact (hdj.ok.st.sub_right (Lay.stSub hk)).symm
    have hrd₅' : s₅.rd = s.rd := by rw [hrd₅, hrd₄, g.rd, hrd₂]
    have hwr₅' : s₅.wr = s.wr := by rw [hwr₅, hwr₄, g.wr, hwr₂]
    refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [hg₅ _ (by decide) (by decide) (by decide), hg₄ _ (by decide) (by decide) (by decide)])
      (by rw [hrd₅, hrd₄]) (by rw [hwr₅, hwr₄]), ?_, ?_, ?_, ?_⟩
    · refine VG.Proof.AesGcm.X86_64.rounds_frame fw dW (VG.Proof.AesGcm.X86_64.rounds_frame gframe (fun r hr => ?_) (VG.Proof.AesGcm.X86_64.rounds_frame fz (fun r hr => ?_) h.rounds))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · rw [hk]; exact (L.stk_w (by decide)).symm
      · simp only [List.mem_singleton] at hr; subst hr
        exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · intro hc₀
      rw [show P + n = P + j + (n - j) by omega]
      exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
        (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
    · intro hc₀
      have hdone : bytesAt s₅.mem D j = bytesAt s.mem D j := by
        rw [bytesAt_frame fw (fun r hr => ?_) (by omega), bytesAt_frame gframe (fun r hr => ?_) (by omega),
          bytesAt_frame fz (fun r hr => ?_) (by omega)]
        · simp only [List.mem_singleton] at hr; subst hr
          exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
          · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
          · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
          · rw [hk]; exact (h.data.take h.le).ok.stk.symm
        · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86_64.split_disj (D := D) h.le hn'
      have hpiece : bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) =
          xorKs (VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) := by
        have e := VG.Proof.AesGcm.X86_64.bytesAt_writeBytes_self s₃.mem (D + BitVec.ofNat 64 j)
          (xorBytes s₃.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega)
        rw [hxl] at e
        rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
      rw [show n = j + (n - j) by omega]
      exact VG.Proof.AesGcm.X86_64.done_append (hdone.trans (h.done hc₀)) hpiece
    · refine h.frame.trans (Frame.trans (Frame.trans (fz.sub fun r hr => ?_) (gframe.sub fun r hr => ?_))
        (fw.sub fun r hr => ?_))
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub_base D (by omega)⟩

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ j s) : VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf m₀ Ctx R :=
  VG.Proof.AesGcm.X86_64.ciph_frame h.frame (VG.Proof.AesGcm.X86_64.ctx_crFrame L h.data) h.rounds.2

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s) :
    WP isa (crypt v.callees) s (VG.Proof.AesGcm.X86_64.CrOut Ctx St W SP R icb P D n s.mem) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s .rbp h.rbp hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.rounds, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    have h₁ : VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s₁ := ⟨he₁, by rw [hg₁]; exact h.r12, by rw [hg₁]; exact h.rbp,
      by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds⟩
    obtain ⟨s₂, run₂, hzf₂, hg₂, hm₂, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.test_ok s₁ .rbx h₁.rbx
      (by have := Nat.mod_lt P (show 16 > 0 by decide); omega)
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he₁.keep (fun r _ => by rw [hg₂]) hrd₂ hwr₂
    have h₂ : VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s₂ := ⟨he₂, by rw [hg₂]; exact h₁.r12, by rw [hg₂]; exact h₁.rbp,
      by rw [hg₂]; exact h₁.rbx, h₁.data.of_eq hrd₂ hwr₂, by rw [hm₂]; exact h₁.rounds⟩
    have hm₀ : s₂.mem = s.mem := hm₂.trans hm₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (Q := fun s' => ∃ j, VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n s.mem j s')
      (WP.ite (decide (P % 16 = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf₂) (fun ht => ?_) (fun hf => ?_)) fun s' hj => ?_)
    · have ho : P % 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨0, he₂, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
        h₂.rounds, fun hc₀ => by rw [hm₀]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by rw [hm₀],
        .inr (by omega), by rw [← hm₀]; exact Frame.refl _ _⟩
    · have := VG.Proof.AesGcm.X86_64.cryptHead_ok h₂ h0 (by simpa using hf)
      rw [hm₀] at this; exact WP.mono this fun _ h => ⟨_, h⟩
    · obtain ⟨j, hj⟩ := hj
      refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.cryptWhole_ok v L hj (hj.ciph L)) fun s'' hj' => ?_)
      exact VG.Proof.AesGcm.X86_64.cryptTail_ok v L hj' (by have := hj.le; omega) (hj'.ciph L)

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Fn`. -/
section

/-!
# AES-GCM on x86-64: what every function does

Untrusted: everything here is checked by Lean. Each function saves our
caller's `rbx, rbp, r12–r15` at `W + 128` (`save_ok`) and restores them
(`restore_ok`); the pieces it runs in between never write there.

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => exact ⟨_, _, .seq ea (.seq eb e₂), q⟩

/-- A run of five programs, then one more. -/
theorem WP.seq5 {a b c d e T : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s P) (k : ∀ s', P s' → WP isa T s' Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e T))))) s Q := by
  refine WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
    WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
      WP.seq (WP.mono h k)))))

/-- Code never changes the permissions. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, q⟩ := h; exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (W : Addr) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

/-- The saved registers' slots. -/
abbrev savedR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 48⟩

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.AesGcm.X86_64.SavedAt s'.mem W s ∧ Frame [VG.Proof.AesGcm.X86_64.savedR W] s.mem s'.mem := by
  have w₁ := VG.Proof.AesGcm.X86_64.in_off hw (show 128 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off hw (show 136 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.in_off hw (show 144 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := VG.Proof.AesGcm.X86_64.in_off hw (show 152 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := VG.Proof.AesGcm.X86_64.in_off hw (show 160 + 8 ≤ 2560 by decide) (by decide)
  have w₆ := VG.Proof.AesGcm.X86_64.in_off hw (show 168 + 8 ≤ 2560 by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have s128_136 := sep 128 136 (by decide) (by decide) (by decide)
  have s128_144 := sep 128 144 (by decide) (by decide) (by decide)
  have s128_152 := sep 128 152 (by decide) (by decide) (by decide)
  have s128_160 := sep 128 160 (by decide) (by decide) (by decide)
  have s128_168 := sep 128 168 (by decide) (by decide) (by decide)
  have s136_144 := sep 136 144 (by decide) (by decide) (by decide)
  have s136_152 := sep 136 152 (by decide) (by decide) (by decide)
  have s136_160 := sep 136 160 (by decide) (by decide) (by decide)
  have s136_168 := sep 136 168 (by decide) (by decide) (by decide)
  have s144_152 := sep 144 152 (by decide) (by decide) (by decide)
  have s144_160 := sep 144 160 (by decide) (by decide) (by decide)
  have s144_168 := sep 144 168 (by decide) (by decide) (by decide)
  have s152_160 := sep 152 160 (by decide) (by decide) (by decide)
  have s152_168 := sep 152 168 (by decide) (by decide) (by decide)
  have s160_168 := sep 160 168 (by decide) (by decide) (by decide)
  refine ⟨_, by simp only [save, saved, List.map]; xrun [hb, w₁, w₂, w₃, w₄, w₅, w₆], ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 3
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := first | decide | with_reducible assumption) only [hb, Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · have c : ∀ d, 128 ≤ d → d + 8 ≤ 176 → (VG.Proof.AesGcm.X86_64.savedR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [hb]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 144 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 152 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 160 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))
  all_goals rfl

theorem restore_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr))
    {s₀ : State} (hs : VG.Proof.AesGcm.X86_64.SavedAt s.mem W s₀) :
    ∃ s', runBlock isa VG.Impl.AesGcm.X86_64.restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := VG.Proof.AesGcm.X86_64.in_off hr (show 128 + 8 ≤ 2560 by decide) (by decide)
  have r₂ := VG.Proof.AesGcm.X86_64.in_off hr (show 136 + 8 ≤ 2560 by decide) (by decide)
  have r₃ := VG.Proof.AesGcm.X86_64.in_off hr (show 144 + 8 ≤ 2560 by decide) (by decide)
  have r₄ := VG.Proof.AesGcm.X86_64.in_off hr (show 152 + 8 ≤ 2560 by decide) (by decide)
  have r₅ := VG.Proof.AesGcm.X86_64.in_off hr (show 160 + 8 ≤ 2560 by decide) (by decide)
  have r₆ := VG.Proof.AesGcm.X86_64.in_off hr (show 168 + 8 ≤ 2560 by decide) (by decide)
  have e₁ := hs (.rbx, 128) (by simp [saved])
  have e₂ := hs (.rbp, 136) (by simp [saved])
  have e₃ := hs (.r12, 144) (by simp [saved])
  have e₄ := hs (.r13, 152) (by simp [saved])
  have e₅ := hs (.r14, 160) (by simp [saved])
  have e₆ := hs (.r15, 168) (by simp [saved])
  simp only at e₁ e₂ e₃ e₄ e₅ e₆
  refine ⟨_, by simp only [VG.Impl.AesGcm.X86_64.restore, saved, List.map]; xrun [h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, h15, e₁, e₂, e₃, e₄, e₅, e₆]
  · intro r hr
    simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g⟩ := hr
    simp [gpr_setReg, a, b, c, d, f, g]
  all_goals rfl

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {W : Addr} {s₀ : State} (h : VG.Proof.AesGcm.X86_64.SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r) : VG.Proof.AesGcm.X86_64.SavedAt m' W s₀ := by
  intro p hp
  have hp' := hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hs : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.AesGcm.X86_64.savedR W) := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Offset.sub _ (by decide) (by decide)
  rw [hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

theorem ret_below (SP : Addr) : (⟨SP, 8⟩ : Region).Disjoint (below SP 8) :=
  Offset.base_disjoint_below SP (n := 8) (k := 8) (by decide)

/-- The return address stays where it is, outside a frame. -/
theorem ret_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {SP : Addr}
    (hd : ∀ r ∈ rs, (⟨SP, 8⟩ : Region).Disjoint r) : m'.readW SP 64 = m.readW SP 64 :=
  hf.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) hd (by decide)

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h15 : s.gpr .r15 = W) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hs : VG.Proof.AesGcm.X86_64.SavedAt s.mem W s₀)
    (hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64) :
    WP isa (.block VG.Impl.AesGcm.X86_64.restore) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .rax = s.gpr .rax := by
  obtain ⟨s', run, hsv, hother, hm, -, -⟩ := VG.Proof.AesGcm.X86_64.restore_ok s h15 hr hs
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr => ?_, by rw [hm, hret]⟩, hm, hother .rax (by simp [saved])⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.rbx, 128) (by simp [saved])
  · exact hsv (.rbp, 136) (by simp [saved])
  · rw [hother .rsp (by simp [saved]), hsp]
  · exact hsv (.r12, 144) (by simp [saved])
  · exact hsv (.r13, 152) (by simp [saved])
  · exact hsv (.r14, 160) (by simp [saved])
  · exact hsv (.r15, 168) (by simp [saved])

section
variable {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame St W SP yo, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP yo, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ VG.Proof.AesGcm.X86_64.tagFrame St W SP o, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ VG.Proof.AesGcm.X86_64.j0Frame St W SP, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.crFrame St W SP D n, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

end

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {Ctx St W SP : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩)
    (kc : (below SP 8).Disjoint ⟨Ctx, 256⟩) (ks : (below SP 8).Disjoint ⟨St, 80⟩)
    (kw : (below SP 8).Disjoint ⟨W, 2560⟩) : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl


end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Contract`. -/
section

/-!
# AES-GCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others, whose return addresses are
in the 8 bytes below the stack pointer (`stk`), which no buffer overlaps,
nor the return address (`ret`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk (s : State) : Region := below (s.gpr .rsp) 8

/-- The stack `seal` and `open` use: a frame of one argument, and the return
addresses of a call and of its own calls. -/
abbrev stk24 (s : State) : Region := below (s.gpr .rsp) 24

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- `vg_aes_gcm_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧ (VG.Proof.AesGcm.ret s).Disjoint ctx ∧ (VG.Proof.AesGcm.ret s).Disjoint scr ∧
      (VG.Proof.AesGcm.stk s).Disjoint key ∧ (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint scr ∧
      (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_init(ctx = rdi, nonce = rsi, nonce_len = rdx, state = rcx, scratch = r8)`. -/
def streamInitX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let st : Region := ⟨s.gpr .rcx, 80⟩
    let scr : Region := ⟨s.gpr .r8, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (VG.Proof.AesGcm.ret s).Disjoint st ∧ (VG.Proof.AesGcm.ret s).Disjoint scr ∧
      (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint nonce ∧ (VG.Proof.AesGcm.stk s).Disjoint st ∧ (VG.Proof.AesGcm.stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .rcx) ciph (ctxH s.mem (s.gpr .rdi))
    (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) [] []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_aad(ctx = rdi, state = rsi, aad_len = rdx, data = rcx, len = r8, scratch = r9)`. -/
def streamAadX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let st : Region := ⟨s.gpr .rsi, 80⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (VG.Proof.AesGcm.ret s).Disjoint st ∧ (VG.Proof.AesGcm.ret s).Disjoint scr ∧
      (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint data ∧ (VG.Proof.AesGcm.stk s).Disjoint st ∧ (VG.Proof.AesGcm.stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv a [] →
    s.gpr .rdx = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv
      (a ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx, text_len = r8, data = r9, len = [rsp + 8],
scratch = [rsp + 16])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let data : Region := ⟨s.gpr .r9, (VG.Proof.AesGcm.arg s 0).toNat⟩
  let scr : Region := ⟨VG.Proof.AesGcm.arg s 1, 2560⟩
  s.rd = [ctx, VG.Proof.AesGcm.args s 2] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (VG.Proof.AesGcm.args s 2) ∧ data.Disjoint scr ∧
    data.Disjoint (VG.Proof.AesGcm.args s 2) ∧ scr.Disjoint (VG.Proof.AesGcm.args s 2) ∧
    (VG.Proof.AesGcm.ret s).Disjoint st ∧ (VG.Proof.AesGcm.ret s).Disjoint data ∧ (VG.Proof.AesGcm.ret s).Disjoint scr ∧
    (VG.Proof.AesGcm.stk24 s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk24 s).Disjoint st ∧ (VG.Proof.AesGcm.stk24 s).Disjoint data ∧ (VG.Proof.AesGcm.stk24 s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (VG.Proof.AesGcm.arg s 0).toNat ≤ 2 ^ 64 ∧ (VG.Proof.AesGcm.arg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.rounds s

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ VG.Proof.AesGcm.arg s₁ 0 = VG.Proof.AesGcm.arg s₂ 0 ∧ VG.Proof.AesGcm.arg s₁ 1 = VG.Proof.AesGcm.arg s₂ 1

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a p, StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (VG.Proof.AesGcm.arg s 0).toNat)
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r9) (VG.Proof.AesGcm.arg s 0).toNat = c.drop p.length
  pub := VG.Proof.AesGcm.streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r9) (VG.Proof.AesGcm.arg s 0).toNat
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r9) (VG.Proof.AesGcm.arg s 0).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := VG.Proof.AesGcm.streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, tag = r9, work = [rsp + 8])`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let tag : Region := ⟨s.gpr .r9, 16⟩
  let work : Region := ⟨VG.Proof.AesGcm.arg s 0, 2560⟩
  s.rd = [ctx, VG.Proof.AesGcm.args s 1] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint st ∧ tag.Disjoint work ∧
    (VG.Proof.AesGcm.ret s).Disjoint st ∧ (VG.Proof.AesGcm.ret s).Disjoint tag ∧ (VG.Proof.AesGcm.ret s).Disjoint work ∧
    (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint st ∧ (VG.Proof.AesGcm.stk s).Disjoint tag ∧ (VG.Proof.AesGcm.stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 16 ≤ 2 ^ 64 ∧
    (VG.Proof.AesGcm.arg s 0).toNat + 2560 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.rounds s

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, tag = r9, tag_len = [rsp + 8], work = [rsp + 16])`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let tag : Region := ⟨s.gpr .r9, (VG.Proof.AesGcm.arg s 0).toNat⟩
  let work : Region := ⟨VG.Proof.AesGcm.arg s 1, 2560⟩
  s.rd = [ctx, tag, VG.Proof.AesGcm.args s 2] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint work ∧ work.Disjoint (VG.Proof.AesGcm.args s 2) ∧
    (VG.Proof.AesGcm.ret s).Disjoint st ∧ (VG.Proof.AesGcm.ret s).Disjoint work ∧
    (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint st ∧ (VG.Proof.AesGcm.stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (VG.Proof.AesGcm.arg s 0).toNat ≤ 2 ^ 64 ∧ (VG.Proof.AesGcm.arg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.rounds s

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      bytesAt s'.mem (s.gpr .r9) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    VG.Proof.AesGcm.arg s₁ 0 = VG.Proof.AesGcm.arg s₂ 0

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    let tl := (VG.Proof.AesGcm.arg s 0).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r9) tl then (s'.gpr .rax).setWidth 32 = 1
      else (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    VG.Proof.AesGcm.arg s₁ 0 = VG.Proof.AesGcm.arg s₂ 0 ∧ VG.Proof.AesGcm.arg s₁ 1 = VG.Proof.AesGcm.arg s₂ 1

/-- What `vg_aes_gcm_seal` and `vg_aes_gcm_open` both need, but for `tag` and
the permissions: `(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24])`,
`work` the `w`-th argument on the stack, and `n` arguments there. -/
def oneLay (w n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesGcm.arg s 0, (VG.Proof.AesGcm.arg s 1).toNat⟩
  let work : Region := ⟨VG.Proof.AesGcm.arg s w, 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.args s n) ∧ work.Disjoint (VG.Proof.AesGcm.args s n) ∧
    (VG.Proof.AesGcm.ret s).Disjoint data ∧ (VG.Proof.AesGcm.ret s).Disjoint work ∧
    (VG.Proof.AesGcm.stk24 s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk24 s).Disjoint nonce ∧ (VG.Proof.AesGcm.stk24 s).Disjoint aad ∧ (VG.Proof.AesGcm.stk24 s).Disjoint data ∧
    (VG.Proof.AesGcm.stk24 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (VG.Proof.AesGcm.arg s 0).toNat + (VG.Proof.AesGcm.arg s 1).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesGcm.arg s w).toNat + 2560 ≤ 2 ^ 64 ∧ 24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 * (n + 1) ≤ 2 ^ 64 ∧
    VG.Proof.AesGcm.rounds s

/-- What `vg_aes_gcm_seal` needs: `oneLay`, with `tag` a 16-byte buffer to
write and `work = [rsp + 32]`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesGcm.arg s 0, (VG.Proof.AesGcm.arg s 1).toNat⟩
  let tag : Region := ⟨VG.Proof.AesGcm.arg s 2, 16⟩
  let work : Region := ⟨VG.Proof.AesGcm.arg s 3, 2560⟩
  s.rd = [ctx, nonce, aad, VG.Proof.AesGcm.args s 4] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesGcm.oneLay 3 4 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (VG.Proof.AesGcm.ret s).Disjoint tag ∧ (VG.Proof.AesGcm.arg s 2).toNat + 16 ≤ 2 ^ 64

/-- What `vg_aes_gcm_open` needs: `oneLay`, with the received tag the
`tag_len = [rsp + 32]` bytes at `tag`, to read, and `work = [rsp + 40]`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesGcm.arg s 0, (VG.Proof.AesGcm.arg s 1).toNat⟩
  let tag : Region := ⟨VG.Proof.AesGcm.arg s 2, (VG.Proof.AesGcm.arg s 3).toNat⟩
  let work : Region := ⟨VG.Proof.AesGcm.arg s 4, 2560⟩
  s.rd = [ctx, nonce, aad, tag, VG.Proof.AesGcm.args s 5] ∧ s.wr = [data, work] ∧ VG.Proof.AesGcm.oneLay 4 5 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (VG.Proof.AesGcm.stk24 s).Disjoint tag ∧ (VG.Proof.AesGcm.arg s 2).toNat + (VG.Proof.AesGcm.arg s 3).toNat ≤ 2 ^ 64

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < n, VG.Proof.AesGcm.arg s₁ i = VG.Proof.AesGcm.arg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) 16
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat, bytesAt s'.mem (VG.Proof.AesGcm.arg s 2) 16)
  pub := VG.Proof.AesGcm.onePub 4

/-- What `vg_aes_gcm_open` may leak (`Spec.Gcm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesGcm.rounds s then [] else
  [if (openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (VG.Proof.AesGcm.arg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (VG.Proof.AesGcm.arg s 2) (VG.Proof.AesGcm.arg s 3).toNat)).isSome
    then 1 else 0]

/-- `vg_aes_gcm_open`. -/
def openX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.openPre
  post s s' :=
    match openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (VG.Proof.AesGcm.arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (VG.Proof.AesGcm.arg s 2) (VG.Proof.AesGcm.arg s 3).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat = bytesAt s.mem (VG.Proof.AesGcm.arg s 0) (VG.Proof.AesGcm.arg s 1).toNat
  pub s₁ s₂ := VG.Proof.AesGcm.onePub 5 s₁ s₂ ∧ VG.Proof.AesGcm.openLeak s₁ = VG.Proof.AesGcm.openLeak s₂

end VG.Proof.AesGcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_encrypt_blocks`
and `vg_aes_gcm_decrypt_blocks` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, data = r8, n = r9, scratch = [rsp + 8])`; the shared contracts of
`Spec/Gcm/Contract.lean` imply these (`BlocksVerified.lean`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- What both need. -/
def blocksPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let scr : Region := ⟨VG.Proof.AesGcm.arg s 0, 2112⟩
  s.rd = [ctx, VG.Proof.AesGcm.args s 1] ∧ s.wr = [ctr, y, data, scr] ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint data ∧ ctr.Disjoint scr ∧ ctr.Disjoint (VG.Proof.AesGcm.args s 1) ∧
    y.Disjoint data ∧ y.Disjoint scr ∧ y.Disjoint (VG.Proof.AesGcm.args s 1) ∧
    data.Disjoint scr ∧ data.Disjoint (VG.Proof.AesGcm.args s 1) ∧ scr.Disjoint (VG.Proof.AesGcm.args s 1) ∧
    (VG.Proof.AesGcm.ret s).Disjoint ctr ∧ (VG.Proof.AesGcm.ret s).Disjoint y ∧ (VG.Proof.AesGcm.ret s).Disjoint data ∧ (VG.Proof.AesGcm.ret s).Disjoint scr ∧
    (VG.Proof.AesGcm.stk s).Disjoint ctx ∧ (VG.Proof.AesGcm.stk s).Disjoint ctr ∧ (VG.Proof.AesGcm.stk s).Disjoint y ∧ (VG.Proof.AesGcm.stk s).Disjoint data ∧
    (VG.Proof.AesGcm.stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧ (VG.Proof.AesGcm.arg s 0).toNat + 2112 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ VG.Proof.AesGcm.rounds s

def blocksPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ VG.Proof.AesGcm.arg s₁ 0 = VG.Proof.AesGcm.arg s₂ 0

/-- `vg_aes_gcm_encrypt_blocks`. -/
def encryptBlocksX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx))
      (blocksAt s.mem (s.gpr .r8) n)
    blocksAt s'.mem (s.gpr .r8) n = c ∧ blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := VG.Proof.AesGcm.blocksPub

/-- `vg_aes_gcm_decrypt_blocks`. -/
def decryptBlocksX86_64 : Contract isa where
  pre := VG.Proof.AesGcm.blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := blocksAt s.mem (s.gpr .r8) n
    blocksAt s'.mem (s.gpr .r8) n =
        ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx)) c ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := VG.Proof.AesGcm.blocksPub

end VG.Proof.AesGcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT`. -/
section

/-!
# AES-GCM on x86-64: `crypt` in two runs

Untrusted: everything here is checked by Lean. Two runs of `crypt` over
data at the same address, of the same length, after the same number of
bytes modulo 16, with the same number of rounds, leak the same: the code
between the calls of `vg_aes_ctr32` is checked by the taint analysis, from
the registers `CrIn` and `CrMid` fix, and each call has the same arguments
in both runs.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
theorem CrMid.agree {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁) (h₂ : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) :
    ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r12, h₂.r12]
  · rw [h₁.rbp, h₂.rbp]
  · rw [h₁.env.r13, h₂.env.r13]
  · rw [h₁.env.r14, h₂.env.r14]
  · rw [h₁.env.r15, h₂.env.r15]
  · rw [h₁.env.rsp, h₂.env.rsp]

/-- Whole blocks. -/
theorem cryptWhole_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptWhole v.callees) fun _ _ => True := by
  let Sp : State → Prop := fun s₁ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.DataW Ctx St W SP s₁ D n ∧ j ≤ n ∧
    VG.Proof.AesGcm.X86_64.RoundsAt s₁.mem W R ∧ s₁.gpr .rcx = D + BitVec.ofNat 64 j ∧ s₁.gpr .r8 = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m j s →
      WP isa (.block (splitWhole .rcx .r8 ++ [.alu .test .r8 (.reg .r8)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hcx, h8, -, -, -, hg₁, hm₁, hrd₁, hwr₁⟩ :=
      VG.Proof.AesGcm.X86_64.wholeSplit_ok .rcx .r8 (.inr ⟨rfl, rfl⟩) h.data.ok.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le,
      by rw [hm₁]; exact h.rounds, hcx, h8⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  let Ar : State → Prop := fun s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
      ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO)) s Ar := fun s ⟨he, hd, hj, hR, hcx, h8⟩ => by
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, -, hrd₂, hwr₂⟩ := VG.Proof.AesGcm.X86_64.ctrArgs_ok he hR
    have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    exact WP.of_runBlock ⟨s₂, run₂, he₂, VG.Proof.AesGcm.X86_64.cwCall_of L he₂ (hd.of_eq hrd₂ hwr₂) hj (by omega) hR.2 hdi hsi hdx
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), hcx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h8]) h9⟩
  have b := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1.2.1.1, h.1.2.2.1, fun _ h => by cases h⟩)
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

/-- The arguments of `cryptTail`'s call of `vg_aes_ctr32`. -/
theorem ctTailArgs_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m₀ j s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s fun s₂ =>
      VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
      CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
      s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j) := by
  have he := h.env
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  have r₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s = some s₂ ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hR := h.rounds.1
    have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (St + BitVec.ofNat 64 64) x).writeW
        (St + BitVec.ofNat 64 72) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
      intro m x y
      rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 72) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
        Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 64) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    refine ⟨_, by xrun [h13, h14, h15, w₁, w₂, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hsep, hR]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  refine ⟨he₂, ?_, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    h.r12], by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]⟩
  refine ⟨hdi, hsi, hdx, hcx, h8, h9, h.rounds.2, by have := L.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    L.st_st (.inl (by decide)) (by decide) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_w (by decide)
  · refine VG.Proof.AesGcm.X86_64.covers_cons ?_ (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
      (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.stC (by decide))) (VG.Proof.AesGcm.X86_64.covers_left (he₂.perm.wC (by decide)))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
  · exact VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.stC (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons (he₂.perm.stC (by decide))
      (he₂.perm.wC (by decide)))

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptTail v.callees) fun _ _ => True := by
  have hT : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m j s →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) s (VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb P D n m j) := fun s h => by
    obtain ⟨s₁, run₁, -, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s .rbp h.rbp (by have := h.data.ok.lt; omega)
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.le, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds, fun hc => by rw [hm₁]; exact h.ctr hc,
      fun hc => by rw [hm₁]; exact h.done hc, by rw [hm₁]; exact h.rest, h.whole, by rw [hm₁]; exact h.frame⟩
  have t := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)
  refine RelCT.seq t (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The arguments of the call, and what it keeps.
  let G : State → Prop := fun s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
    s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j)
  let K : State → Prop := fun s₃ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ ∧
    s₃.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₃.gpr .rbp = BitVec.ofNat 64 (n - j)
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => ((((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => CrMid.agree h.1.2.1 h.1.2.2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (G₁ := G) (G₂ := G) (fun s h => VG.Proof.AesGcm.X86_64.ctTailArgs_ok L h)
    (fun s h => VG.Proof.AesGcm.X86_64.ctTailArgs_ok L h)
  have hK : ∀ s, G s → WP isa (.call v.ctr.callee.name v.ctr.callee.code) s K := fun s ⟨he, hc, h12, hbp⟩ =>
    WP.mono (ctr_call v.ctr hc) fun _ g => ⟨he.of_saved g.saved g.rd g.wr,
      by rw [g.saved _ (by decide), h12], by rw [g.saved _ (by decide), hbp]⟩
  have c := VG.Proof.AesGcm.X86_64.rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧ G s₁ ∧ G s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, _, h.2.1.2.1, h.2.2.2.1, by rw [h.2.1.1.rsp, h.2.2.1.rsp]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  have d := VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ K s₁ ∧ K s₂)
    (c := .seq (.block ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r14 64 ++ [.mov .rcx (.reg .rbp)])) xorLoop)
    [.r12, .rbp, .r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]
      · rw [h.2.1.1.r13, h.2.2.1.r13]
      · rw [h.2.1.1.r14, h.2.2.1.r14]
      · rw [h.2.1.1.r15, h.2.2.1.r15]
      · rw [h.2.1.1.rsp, h.2.2.1.rsp]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq c d)

/-- `crypt`, over data at the same address, of the same length, after the
same number of bytes modulo 16, with the same number of rounds. -/
theorem crypt_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP : P₁ % 16 = P₂ % 16) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂)
      (crypt v.callees) fun _ _ => True := by
  have hag : ∀ s₁ s₂, VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂ →
      ∀ r ∈ VG.Proof.AesGcm.X86_64.absRegs, s₁.gpr r = s₂.gpr r := fun s₁ s₂ h r hr => by
    simp only [VG.Proof.AesGcm.X86_64.absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hP]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hT : ∀ {r : Reg} {icb : Block} {P : Nat} {k : Nat} (s : State), VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb P D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcm.X86_64.test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds⟩, hz⟩
  have t₁ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
      VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂) VG.Proof.AesGcm.X86_64.absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
  refine RelCT.seq t₁ (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt P₁ (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt P₂ (show 16 > 0 by decide)
  have t₂ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      VG.Proof.AesGcm.X86_64.absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega))
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (P₁ % 16 = 0))) ∧
        VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (P₂ % 16 = 0)))
      (.ite .e (.block []) cryptHead) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ := by
    refine VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : P₁ % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, ?_, ?_⟩
      · have h₂ := h.1.2.1.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega), Frame.refl _ _⟩
      · have h₂ := h.1.2.2.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega), Frame.refl _ _⟩
    · by_cases ho : P₁ % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.rel_taint VG.Proof.AesGcm.X86_64.absRegs (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
          VG.Proof.AesGcm.X86_64.CrIn Ctx St W SP R icb₂ P₂ D n s₂) hag ⟨_, by taint_decide⟩).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₁ P₁ D n m (min (16 - P₁ % 16) n) s)
        (G₂ := fun s => ∃ m, VG.Proof.AesGcm.X86_64.CrMid Ctx St W SP R icb₂ P₂ D n m (min (16 - P₂ % 16) n) s)
        (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.cryptHead_ok h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.cryptHead_ok h hn0 (by omega)) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hP]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.cryptWhole_rel v L (R := R) (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => VG.Proof.AesGcm.X86_64.cryptWhole_ok v L h (h.ciph L)) (fun s h => VG.Proof.AesGcm.X86_64.cryptWhole_ok v L h (h.ciph L))
  exact RelCT.seq hw ((VG.Proof.AesGcm.X86_64.cryptTail_rel v L).mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.FinTag`. -/
section

/-!
# AES-GCM on x86-64: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text if there is)
and writes the tag to `W + o`, from the lengths kept at `W + 184` and
`W + 192` (`finTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock)

theorem lensBlock_mod (a c : Nat) : lensBlock (a % 2 ^ 64) (c % 2 ^ 64) = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a), ← Proof.Gcm.be64_mod (8 * (c % 2 ^ 64)),
    ← Proof.Gcm.be64_mod (8 * c)]
  congr 2 <;> omega

theorem lensBlock_mod_left (a c : Nat) : lensBlock (a % 2 ^ 64) c = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2; omega

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- `finTag o`, for buffered input `x` (of the length the lengths give modulo 16). -/
theorem finTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s)
    (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (finTag v.callees o) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧ VG.Proof.AesGcm.X86_64.RoundsAt s'.mem W R ∧
      Frame (VG.Proof.AesGcm.X86_64.tagFrame St W SP o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
            (VG.Spec.Gcm.ghash (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
            [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R (blockAt s.mem St))) := by
  have h15 := he.r15
  have r₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
  generalize hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  obtain ⟨s₁, run₁, hbx₁, hax₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)), .alu .test .rbx (.reg .rbx)] s =
        some s₁ ∧
      s₁.gpr .rbx = tL ∧ s₁.gpr .rax = aL ∧ s₁.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hT]
    · simp [gpr_setReg, hA]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hT]
      have := VG.Proof.AesGcm.X86_64.and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  -- `rbx`: the length of the buffered input, modulo 16.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = (if tL = 0 then aL else tL) ∧
      s₂.mem = s.mem) (WP.ite (decide (tL.toNat = 0)) (VG.Proof.AesGcm.X86_64.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)) fun s₂ h₂ => ?_)
  · have h0 : tL = 0 := by
      have : tL.toNat = 0 := by simpa using ht
      exact BitVec.eq_of_toNat_eq (by simpa using this)
    refine WP.run (Q := fun s₂ => s₂ = s₁.setReg .rbx (s₁.gpr .rax)) ⟨_, by xrun [], rfl⟩ fun s₂ e => ?_
    subst e
    exact ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl,
      by simp [gpr_setReg, hax₁, h0], by rw [mem_setReg, hm₁]⟩
  · have h0 : tL ≠ 0 := fun e => by subst e; simp at hf
    exact WP.block_nil ⟨he₁, by simp only [hbx₁, h0, ↓reduceIte], hm₁⟩
  obtain ⟨he₂, hbx₂, hm₂⟩ := h₂
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (if tL = 0 then aL else tL)
    rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbx₂, hand, hx]
      split <;> rfl
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hm₃' : s₃.mem = s.mem := hm₃.trans hm₂
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₃, by rw [hm₃', hH]⟩ hbx₃) fun s₄ hf => ?_)
  rw [hm₃'] at hf
  have he₄ := hf.env
  have dT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  have hA₄ : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = aL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _) (dT 184 (by decide) (by decide))
      (by decide), hA]
  have hT₄ : s₄.mem.readW (W + BitVec.ofNat 64 192) 64 = tL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (dT 192 (by decide) (by decide))
      (by decide), hT]
  have r₃ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₄ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧
      s₅.gpr .rbx = aL ∧ s₅.gpr .rbp = tL ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧
      s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hA₄]
    · simp [gpr_setReg, hT₄]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have f₅ : Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP 16) s.mem s₅.mem := hm₅ ▸ hf.frame
  have hR₅ : VG.Proof.AesGcm.X86_64.RoundsAt s₅.mem W R := VG.Proof.AesGcm.X86_64.rounds_frame f₅ (fun r hr => dT 176 (by decide) (by decide) r hr) hR
  have hJ₅ : blockAt s₅.mem St = blockAt s.mem St := blockAt_frame f₅ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hc₅ : VG.Proof.AesGcm.X86_64.ciphOf s₅.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R := VG.Proof.AesGcm.X86_64.ciph_frame f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm) hR.2
  refine WP.mono (VG.Proof.AesGcm.X86_64.tag_ok v L ho he₅ (by rw [hm₅, hf.hH]) hR₅ hJ₅) fun s₆ ht => ?_
  refine ⟨ht.env, ht.rounds, ?_, fun ha => ?_⟩
  · refine (f₅.sub fun r hr => ?_).trans ht.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [ht.out, hc₅, hbx₅, hbp₅]
    have hw := (hf.abs ha).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [hm₅, hw]

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.TagCT`. -/
section

/-!
# AES-GCM on x86-64: `flush`, `lens` and `tag` in two runs

Untrusted: everything here is checked by Lean. Each leaks only what its
public registers (the number of buffered bytes, the lengths) and the
environment say: the code around the calls is checked by the taint
analysis, and the calls of `vg_ghash` and `vg_aes_ctr32` have the same
arguments in both runs (for `tag`, by `tagMid_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- `flush yo`, with the same number of buffered bytes. -/
theorem flush_rel : RelCT isa (VG.Proof.AesGcm.X86_64.EnvAgree Ctx St W SP [.rbx]) (flush v.callees yo) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.AesGcm.X86_64.rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (VG.Proof.AesGcm.X86_64.rel_regs ([.rbx] ++ [.r13, .r14, .r15, .rsp]) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine VG.Proof.AesGcm.X86_64.rel_reassoc2 (RelCT.seq (VG.Proof.AesGcm.X86_64.rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (VG.Proof.AesGcm.X86_64.rel_taint ([.rbx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1) ⟨_, by taint_decide⟩))
    ?_)
  refine (VG.Proof.AesGcm.X86_64.ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (VG.Proof.AesGcm.X86_64.gh1Check_r15_96 hyo) (F₁ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP) (F₂ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], VG.Proof.AesGcm.X86_64.covers_left (he.perm.wC (by decide))⟩

/-- `lens yo`, with the same lengths. -/
theorem lens_rel : RelCT isa (VG.Proof.AesGcm.X86_64.EnvAgree Ctx St W SP [.rbx, .rbp]) (lens v.callees yo) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.AesGcm.X86_64.rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (VG.Proof.AesGcm.X86_64.rel_taint ([.rbx, .rbp] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine (VG.Proof.AesGcm.X86_64.ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (VG.Proof.AesGcm.X86_64.gh1Check_r15_96 hyo) (F₁ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP) (F₂ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], VG.Proof.AesGcm.X86_64.covers_left (he.perm.wC (by decide))⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- `tag o`, with the same lengths and number of rounds. -/
theorem tag_rel {o R : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧ VG.Proof.AesGcm.X86_64.RoundsAt s₁.mem W R ∧ VG.Proof.AesGcm.X86_64.RoundsAt s₂.mem W R)
      (tag v.callees o) fun _ _ => True := by
  -- The arguments of the call, in each run.
  let G : State → Prop := fun s => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧
    CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  have hG : ∀ s, (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) → WP isa (.seq (lens v.callees 16)
      (.block ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO))) s G := fun s h =>
    WP.mono (VG.Proof.AesGcm.X86_64.tagMid_ok v L ho h.1 rfl h.2 rfl) fun _ M => ⟨M.env, M.call⟩
  have hL : ∀ s, VG.Proof.AesGcm.X86_64.Env Ctx St W SP s → WP isa (lens v.callees 16) s (VG.Proof.AesGcm.X86_64.Env Ctx St W SP) := fun s he =>
    WP.mono (VG.Proof.AesGcm.X86_64.lens_ok v L (.inr rfl) he rfl) fun _ h => h.1
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block ([.mov .rax (.mem (at_ .r14 16)),
      .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
      .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
      ptr .r9 .r15 scrO)) hc).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  let P₀ : State → State → Prop := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧
    VG.Proof.AesGcm.X86_64.RoundsAt s₁.mem W R ∧ VG.Proof.AesGcm.X86_64.RoundsAt s₂.mem W R
  have l : RelCT isa P₀ (lens v.callees 16) fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ :=
    VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.lens_rel v L (.inr rfl)).mono (fun _ _ h => h.1) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) hL hL
  have b : RelCT isa (fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂) _ fun _ _ => True :=
    VG.Proof.AesGcm.X86_64.rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1, h.2.2, fun _ h => by cases h⟩) hc
  have pre : RelCT isa P₀ _ fun s₁ s₂ => True ∧ G s₁ ∧ G s₂ :=
    VG.Proof.AesGcm.X86_64.rel_wp (RelCT.seq l b) (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2.1, h.2.2⟩⟩) (fun s h => hG s h) (fun s h => hG s h)
  refine VG.Proof.AesGcm.X86_64.rel_reassoc2 (RelCT.seq pre (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩))
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.J0CT`. -/
section

/-!
# AES-GCM on x86-64: `j0` in two runs

Untrusted: everything here is checked by Lean. Two runs of `j0` for nonces
at the same address, of the same length, leak the same: the branch is on the
length, and the GHASH of a nonce of any other length is `absorb`, `flush`
and `lens` (`absorb_rel`, `flush_rel`, `lens_rel`), with the length kept at
`W + 216` between them.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- The nonce's length is kept at `W + 216`. -/
def AuxN (Ctx St W SP : Addr) (n : Nat) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

omit L in
theorem j0hashA_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s) :
    WP isa (.block [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax, .store (at_ .r14 8) .rax,
      .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)]) s fun s₁ =>
      (∃ H', VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 0 H' [] Np n s₁) ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁ := by
  have he := h.env
  have h14 := he.r14; have h15 := he.r15
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have wa := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax,
      .store (at_ .r14 8) .rax, .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, h15, z₀, z₁, wa], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, h.rbp, Mem.readW_writeW_self64]
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨s₁, run₁, ⟨_, he₁, by rw [hg₁ _ (by decide) (by decide), h.r12],
    by rw [hg₁ _ (by decide) (by decide), h.rbp], by rw [hbx₁]; rfl, h.data.of_eq hrd₁ hwr₁, rfl⟩, he₁, hm₁⟩

omit L in
theorem auxLoad_ok {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s) (hn : n < 2 ^ 64) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 auxO)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) := by
  have ra := h.1.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have hand := VG.Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨s₁, run₁, hbx, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 auxO)),
      .alu .and .rbx (imm 15)] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, h.2, hand]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ⟨h.1.keep (fun r hr => ?_) hrd hwr, by rw [hm]; exact h.2⟩, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

omit L in
theorem auxLens_ok {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s) :
    WP isa (.block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))]) s fun s₁ =>
      VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n := by
  have ra := h.1.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbx, hbp, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov32 .rbx (imm 0),
      .mov .rbp (.mem (at_ .r15 auxO))] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.2]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hrd hwr, hbx, hbp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- `J₀` of a nonce of any length but 12, for nonces at the same address, of
the same length. -/
theorem j0hash_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂) (j0hash v.callees)
      fun _ _ => True := by
  by_cases hlt : n < 2 ^ 64
  swap
  · exact RelCT.of_false fun _ _ h => hlt h.1.data.lt
  -- After `absorb` and `flush`, the length is still kept.
  have hA : ∀ s, (∃ H', VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 0 H' [] Np n s) ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s →
      WP isa (absorb v.callees 0) s (VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n) := fun s ⟨⟨_, h⟩, ha⟩ =>
    WP.mono (VG.Proof.AesGcm.X86_64.absorb_ok v L (.inl rfl) h) fun _ o =>
      ⟨o.env, by rw [o.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.aux_absFrame L)
        (by decide), ha.2]⟩
  have hF : ∀ s, VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s ∧ s.gpr .rbx = BitVec.ofNat 64 (n % 16) →
      WP isa (flush v.callees 0) s (VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n) := fun s ⟨ha, hbx⟩ =>
    WP.mono (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 0) (.inl rfl) (x := List.replicate n 0) ⟨ha.1, rfl⟩ (by simpa using hbx))
      fun _ o => ⟨o.env, by
        rw [o.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.aux_tFrame L)
          (by decide), ha.2]⟩
  have r₀ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂)
      [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [h.1.r12, h.2.r12]
        · rw [h.1.rbp, h.2.rbp]
        · rw [h.1.env.r13, h.2.env.r13]
        · rw [h.1.env.r14, h.2.env.r14]
        · rw [h.1.env.r15, h.2.env.r15]
        · rw [h.1.env.rsp, h.2.env.rsp]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => VG.Proof.AesGcm.X86_64.j0hashA_ok h) (fun s h => VG.Proof.AesGcm.X86_64.j0hashA_ok h)
  let PA : State → State → Prop := fun s₁ s₂ => True ∧
    ((∃ H', VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 0 H' [] Np n s₁) ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁) ∧
    ((∃ H', VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 0 H' [] Np n s₂) ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₂)
  have a₁ : RelCT isa PA (absorb v.callees 0) fun _ _ => True :=
    (RelCT.exists_ fun H₁' => RelCT.exists_ fun H₂' =>
      VG.Proof.AesGcm.X86_64.absorb_rel v L (.inl rfl) (H₁ := H₁') (H₂ := H₂') (x₁ := []) (x₂ := []) (D := Np) (n := n) rfl).mono
      (fun s₁ s₂ (h : PA s₁ s₂) => by
        obtain ⟨_, ⟨⟨H₁', h₁⟩, _⟩, ⟨⟨H₂', h₂⟩, _⟩⟩ := h; exact ⟨H₁', H₂', h₁, h₂⟩) fun _ _ h => h
  have r₁ := VG.Proof.AesGcm.X86_64.rel_wp a₁ (fun _ _ h => h.2) hA hA
  have r₂ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁ ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₂)
      (c := .block [.mov .rbx (.mem (at_ .r15 auxO)), .alu .and .rbx (imm 15)])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1.1, h.2.2.1, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => VG.Proof.AesGcm.X86_64.auxLoad_ok h hlt) (fun s h => VG.Proof.AesGcm.X86_64.auxLoad_ok h hlt)
  have r₃ := VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.flush_rel v L (yo := 0) (.inl rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16)) ∧
      (VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (n % 16)))
      (fun _ _ h => ⟨h.2.1.1.1, h.2.2.1.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  have r₄ := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₁ ∧ VG.Proof.AesGcm.X86_64.AuxN Ctx St W SP n s₂)
      (c := .block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1.1, h.2.2.1, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => VG.Proof.AesGcm.X86_64.auxLens_ok h) (fun s h => VG.Proof.AesGcm.X86_64.auxLens_ok h)
  have r₅ := (VG.Proof.AesGcm.X86_64.lens_rel v L (yo := 0) (.inl rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n) ∧
      (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧ s₂.gpr .rbp = BitVec.ofNat 64 n))
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅))))

/-- `j0`, for nonces at the same address, of the same length. -/
theorem j0_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂) (j0 v.callees)
      fun _ _ => True := by
  have hag : ∀ s₁ s₂, VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂ →
      ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := fun _ _ h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hC : ∀ {H : Block} (s : State), VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s →
      WP isa (.block [.alu .cmp .rbp (imm 12)]) s (fun s₁ => VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H Np n s₁ ∧
        s₁.zf = some (decide (n = 12))) := fun s h => by
    have hlt := h.data.lt
    obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rbp (imm 12)] s = some s₁ ∧
        s₁.zf = some (decide (n = 12)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [], ?_, by rfl, by rfl, by rfl, by rfl⟩
      rw [zf_arithFlags, h.rbp]
      exact congrArg some (VG.Proof.AesGcm.X86_64.sub_beq hlt (by decide))
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hm₁]; exact h.hH,
      by rw [hg₁]; exact h.r12, by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁⟩, hzf⟩
  have c := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hC s h) (fun s h => hC s h)
  let P₀ : State → State → Prop := fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))
  refine RelCT.seq c (RelCT.seq (R := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂)
    (VG.Proof.AesGcm.X86_64.rel_ite_e (P := P₀) (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_) ?_)
  · let P₁ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some true
    have ht : RelCT isa P₁ (.block j012) fun _ _ => True :=
      VG.Proof.AesGcm.X86_64.rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩)
        ⟨_, by taint_decide⟩
    exact (VG.Proof.AesGcm.X86_64.rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.env, h.1.2.2.1.env⟩) ht).mono (fun _ _ h => h)
      fun _ _ h => h.2
  · by_cases h12 : n = 12
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [h12] at this
    let P₂ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (VG.Proof.AesGcm.X86_64.J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some false
    have hj : RelCT isa P₂ (j0hash v.callees) fun _ _ => True :=
      (VG.Proof.AesGcm.X86_64.j0hash_rel v L).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
    exact (VG.Proof.AesGcm.X86_64.rel_wp hj (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (G₁ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP) (G₂ := VG.Proof.AesGcm.X86_64.Env Ctx St W SP)
      (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.j0hash_ok v L h h12) fun _ m => m.env)
      (fun s h => WP.mono (VG.Proof.AesGcm.X86_64.j0hash_ok v L h h12) fun _ m => m.env)).mono (fun _ _ h => h) fun _ _ h => h.2
  · exact VG.Proof.AesGcm.X86_64.rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.FnCT`. -/
section

/-!
# AES-GCM on x86-64: functions in two runs

Untrusted: everything here is checked by Lean. A function is its entry,
checked by the taint analysis from the public arguments, after which
correctness says what each run holds (`I₁`, `I₂`); its body, related from
those; and `restore`, checked from the environment the body leaves
(`fn_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

theorem restore_check : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block VG.Impl.AesGcm.X86_64.restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A function `entry; body; restore`, in two runs from `s₀` and `s₀'`. -/
theorem fn_rel {E : List Instr} {B : Prog isa} {s₀ s₀' : State} {I₁ I₂ : State → Prop} {Ctx St W SP : Addr}
    (rs : List Reg) (hag : ∀ r ∈ rs, s₀.gpr r = s₀'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) (.block E) hc).isSome = true)
    (hE₁ : WP isa (.block E) s₀ I₁) (hE₂ : WP isa (.block E) s₀' I₂)
    (hB : RelCT isa (fun s₁ s₂ => True ∧ I₁ s₁ ∧ I₂ s₂) B
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.seq (.block E) (.seq B (.block VG.Impl.AesGcm.X86_64.restore))) fun _ _ => True := by
  have e := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') rs (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h; exact hag) hc) (fun _ _ h => h) (G₁ := I₁) (G₂ := I₂)
    (fun s h => h ▸ hE₁) (fun s h => h ▸ hE₂)
  exact RelCT.seq e (RelCT.seq hB (VG.Proof.AesGcm.X86_64.rel_taint [.r13, .r14, .r15, .rsp]
    (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) VG.Proof.AesGcm.X86_64.restore_check))

/-- A stack argument loaded into `rax`. -/
theorem loadArg_ok {s : State} {k : Nat}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp k))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 k) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [VG.X86_64.RegUpd.gpr_setReg]
  · intro r a; simp [VG.X86_64.RegUpd.gpr_setReg, a]

/-- A function whose entry first loads `W`, a stack argument, into `rax`. -/
theorem fn_rel₂ {E₁ : List Instr} {B : Prog isa} {s₀ s₀' : State} {I₁ I₂ : State → Prop} {Ctx St W SP : Addr}
    {k : Nat} (rs : List Reg) (hrs : .rsp ∈ rs)
    (hc₀ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp k))]) hc).isSome = true) (hag : ∀ r ∈ rs, s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 k) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 k) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 k) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 k) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (.rax :: rs)) (.block E₁) hc).isSome = true)
    (hE₁ : WP isa (.block (([.mov .rax (.mem (at_ .rsp k))] : List Instr) ++ E₁)) s₀ I₁)
    (hE₂ : WP isa (.block (([.mov .rax (.mem (at_ .rsp k))] : List Instr) ++ E₁)) s₀' I₂)
    (hB : RelCT isa (fun s₁ s₂ => True ∧ I₁ s₁ ∧ I₂ s₂) B
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block (([.mov .rax (.mem (at_ .rsp k))] : List Instr) ++ E₁)) (.seq B (.block VG.Impl.AesGcm.X86_64.restore))) fun _ _ => True := by
  have l := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ hrs) hc₀)
    (fun _ _ h => h) (G₁ := fun s' => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 k) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (G₂ := fun s' => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 k) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    (fun s h => by subst h; exact VG.Proof.AesGcm.X86_64.loadArg_ok hr₁) (fun s h => by subst h; exact VG.Proof.AesGcm.X86_64.loadArg_ok hr₂)
  have e := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_block_split (RelCT.seq l (VG.Proof.AesGcm.X86_64.rel_taint (.rax :: rs) (fun _ _ h r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.1, h.2.2.1, hw]
      · by_cases hx : r = .rax
        · subst hx; rw [h.2.1.1, h.2.2.1, hw]
        · rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) hc))) (fun _ _ h => h) (G₁ := I₁) (G₂ := I₂)
    (fun s h => by subst h; exact hE₁) (fun s h => by subst h; exact hE₂)
  exact RelCT.seq e (RelCT.seq hB (VG.Proof.AesGcm.X86_64.rel_taint [.r13, .r14, .r15, .rsp]
    (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) VG.Proof.AesGcm.X86_64.restore_check))

/-- Constant time, from runs related from each pair of states. -/
theorem ct_of_rel {k : Contract isa} {c : Prog isa}
    (h : ∀ s₀ s₀', k.pre s₀ → k.pre s₀' → k.pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') c fun _ _ => True) :
    ConstantTime isa k.pre k.pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (h _ _ h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT`. -/
section

/-!
# AES-GCM on x86-64: `finTag` in two runs

Untrusted: everything here is checked by Lean. Two runs of `finTag o` with
the same lengths kept at `W + 184` and `W + 192` and the same number of
rounds leak the same: the branch is on the length of the text, `flush` has
the same number of buffered bytes and `tag` the same lengths
(`flush_rel`, `tag_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- The lengths and rounds kept in `W`. -/
def FinS (Ctx St W SP : Addr) (R : Nat) (aL tL : BitVec 64) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R ∧ s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

omit L in
theorem FinS.keep {R : Nat} {aL tL : BitVec 64} {s s' : State} (h : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s' :=
  ⟨h.1.keep hg hrd hwr, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2.1, by rw [hm]; exact h.2.2.2⟩

theorem FinS.frame {R : Nat} {aL tL : BitVec 64} {s s' : State} (h : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s)
    (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s') (hf : Frame (VG.Proof.AesGcm.X86_64.tFrame St W SP 16) s.mem s'.mem) : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s' := by
  have dT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  refine ⟨he, VG.Proof.AesGcm.X86_64.rounds_frame hf (dT 176 (by decide) (by decide)) h.2.1, ?_, ?_⟩
  · rw [hf.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _) (dT 184 (by decide) (by decide))
      (by decide), h.2.2.1]
  · rw [hf.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (dT 192 (by decide) (by decide))
      (by decide), h.2.2.2]

omit L in
theorem env_agree {s₁ s₂ : State} (e₁ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁) (e₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂) :
    ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  EnvAgree.regs (rs := []) ⟨e₁, e₂, fun _ h => by cases h⟩

/-- After loading the lengths. -/
def FinA (Ctx St W SP : Addr) (R : Nat) (aL tL : BitVec 64) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s ∧ s.zf = some (decide (tL.toNat = 0)) ∧ s.gpr .rax = aL ∧ s.gpr .rbx = tL

/-- With the length of the buffered input in `rbx` (modulo 16 if `k`). -/
def FinB (Ctx St W SP : Addr) (R : Nat) (aL tL : BitVec 64) (k : Bool) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s ∧ s.gpr .rbx =
    if k then BitVec.ofNat 64 ((if tL = 0 then aL else tL).toNat % 16) else if tL = 0 then aL else tL

/-- With the lengths for the tag. -/
def FinD (Ctx St W SP : Addr) (R : Nat) (aL tL : BitVec 64) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s ∧ s.gpr .rbx = aL ∧ s.gpr .rbp = tL

omit L in
theorem finA_ok {R : Nat} {aL tL : BitVec 64} {s : State} (h : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)),
      .alu .test .rbx (.reg .rbx)]) s (VG.Proof.AesGcm.X86_64.FinA Ctx St W SP R aL tL) := by
  have r₁ := h.1.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := h.1.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbx₁, hax₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)), .alu .test .rbx (.reg .rbx)] s =
        some s₁ ∧
      s₁.gpr .rbx = tL ∧ s₁.gpr .rax = aL ∧ s₁.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.2.2]
    · simp [gpr_setReg, h.2.2.1]
    · simp only [zf_arithFlags, h.2.2.2]
      have := VG.Proof.AesGcm.X86_64.and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hzf₁, hax₁, hbx₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)

omit L in
theorem finSel_rel {R : Nat} {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.FinA Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinA Ctx St W SP R aL tL s₂)
      (.ite .e (.block [.mov .rbx (.reg .rax)]) (.block []))
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false s₁ ∧ VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false s₂ := by
  refine VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1]) ?_ ?_
  · by_cases h0 : tL = 0
    swap
    · exact RelCT.of_false fun _ _ h => by
        have := h.1.2.1.2.1.symm.trans h.2; simp at this; exact h0 (BitVec.eq_of_toNat_eq (by simpa using this))
    have hM : ∀ s, VG.Proof.AesGcm.X86_64.FinA Ctx St W SP R aL tL s → WP isa (.block [.mov .rbx (.reg .rax)]) s
        (VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false) :=
      fun s h => WP.run (Q := fun s₂ => s₂ = s.setReg .rbx (s.gpr .rax)) ⟨_, by xrun [], rfl⟩ fun s₂ e => by
        subst e
        exact ⟨h.1.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
          by simp [gpr_setReg, h.2.2.1, h0]⟩
    exact (VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint [] (fun _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
      (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hM hM).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases h0 : tL = 0
    · exact RelCT.of_false fun _ _ h => by
        have := h.1.2.1.2.1.symm.trans h.2; simp [h0] at this
    exact RelCT.block_nil fun _ _ h => ⟨⟨h.1.2.1.1, by rw [h.1.2.1.2.2.2]; simp only [h0, ↓reduceIte, Bool.false_eq_true]⟩,
      ⟨h.1.2.2.1, by rw [h.1.2.2.2.2.2]; simp only [h0, ↓reduceIte, Bool.false_eq_true]⟩⟩

omit L in
theorem finMod_ok {R : Nat} {aL tL : BitVec 64} {s : State} (h : VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false s) :
    WP isa (.block [.alu .and .rbx (imm 15)]) s (VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true) := by
  have hand := VG.Proof.AesGcm.X86_64.and15 (if tL = 0 then aL else tL)
  rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨s₁, run₁, hbx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .and .rbx (imm 15)] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 ((if tL = 0 then aL else tL).toNat % 16) ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, h.2, hand, Bool.false_eq_true, ↓reduceIte]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, by simpa using hbx₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)

omit L in
theorem finD_ok {R : Nat} {aL tL : BitVec 64} {s : State} (h : VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))]) s
      (VG.Proof.AesGcm.X86_64.FinD Ctx St W SP R aL tL) := by
  have r₃ := h.1.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₄ := h.1.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₅ ∧
      s₅.gpr .rbx = aL ∧ s₅.gpr .rbp = tL ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s.gpr r) ∧
      s₅.mem = s.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.2.1]
    · simp [gpr_setReg, h.2.2.2]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₅, run₅, h.keep (fun r hr => ?_) hm₅ hrd₅ hwr₅, hbx₅, hbp₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)

/-- The buffered bytes absorbed. -/
theorem finFlush_rel {R : Nat} {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true s₁ ∧ VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true s₂)
      (flush v.callees 16) fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₂ := by
  have hF : ∀ s, VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true s → WP isa (flush v.callees 16) s (VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL) :=
    fun s ⟨h, hbx⟩ => WP.mono (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 16) (.inr rfl)
      (x := List.replicate ((if tL = 0 then aL else tL).toNat % 16) 0) ⟨h.1, rfl⟩ (by simpa using hbx))
      fun _ o => h.frame L o.env o.frame
  have f : RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true s₁ ∧ VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL true s₂)
      (flush v.callees 16) fun _ _ => True :=
    (VG.Proof.AesGcm.X86_64.flush_rel v L (.inr rfl)).mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]⟩) fun _ _ h => h
  exact VG.Proof.AesGcm.X86_64.rel_wp f (fun _ _ h => h) hF hF

/-- The tag. -/
theorem finTag2_rel {o R : Nat} (ho : o = 0 ∨ o = 112) {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₂)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))]) (tag v.callees o))
      fun _ _ => True := by
  have d := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => VG.Proof.AesGcm.X86_64.env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => VG.Proof.AesGcm.X86_64.finD_ok h) (fun s h => VG.Proof.AesGcm.X86_64.finD_ok h)
  have t : RelCT isa (fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.FinD Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinD Ctx St W SP R aL tL s₂)
      (tag v.callees o) fun _ _ => True :=
    (VG.Proof.AesGcm.X86_64.tag_rel v L (R := R) ho).mono (fun _ _ h => ⟨⟨h.2.1.1.1, h.2.2.1.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩, h.2.1.1.2.1, h.2.2.1.2.1⟩) fun _ _ h => h
  exact RelCT.seq d t

/-- `finTag o`, with the same lengths and number of rounds. -/
theorem finTag_rel {o R : Nat} (ho : o = 0 ∨ o = 112) {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₂) (finTag v.callees o)
      fun _ _ => True := by
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₁ ∧ VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => VG.Proof.AesGcm.X86_64.env_agree h.1.1 h.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => VG.Proof.AesGcm.X86_64.finA_ok h) (fun s h => VG.Proof.AesGcm.X86_64.finA_ok h)
  have b := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false s₁ ∧ VG.Proof.AesGcm.X86_64.FinB Ctx St W SP R aL tL false s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => VG.Proof.AesGcm.X86_64.env_agree h.1.1.1 h.2.1.1) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun s h => VG.Proof.AesGcm.X86_64.finMod_ok h) (fun s h => VG.Proof.AesGcm.X86_64.finMod_ok h)
  exact RelCT.seq a (RelCT.seq VG.Proof.AesGcm.X86_64.finSel_rel (RelCT.seq b (RelCT.seq ((VG.Proof.AesGcm.X86_64.finFlush_rel v L).mono (fun _ _ h => h.2)
    fun _ _ h => h) (VG.Proof.AesGcm.X86_64.finTag2_rel v L ho))))

end

/-- The environment, and the address `T` of `tag` in memory at `b + d`. -/
def TagAt (Ctx St W SP : Addr) (b : Reg) (d : Nat) (T : Addr) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ s.mem.readW (s.gpr b + BitVec.ofNat 64 d) 64 = T ∧
    InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 d) 8

/-- `tagOut src`, with the address of `tag` the same `T` in both runs. -/
theorem tagOut_rel {Ctx St W SP T : Addr} {b : Reg} {d : Nat} (hb : b ∈ [Reg.r13, .r14, .r15, .rsp])
    (hc : ∃ hc, (taint.check (Taint.ofRegs [b]) (.block [.mov .rdi (.mem (at_ b d))]) hc).isSome = true)
    {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesGcm.X86_64.TagAt Ctx St W SP b d T s₁ ∧ VG.Proof.AesGcm.X86_64.TagAt Ctx St W SP b d T s₂) :
    RelCT isa P (.block (tagOut (at_ b d))) fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := by
  have hL : ∀ s, VG.Proof.AesGcm.X86_64.TagAt Ctx St W SP b d T s →
      WP isa (.block [.mov .rdi (.mem (at_ b d))]) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧ s'.gpr .rdi = T :=
    fun s ⟨he, hT, r₁⟩ => by
      obtain ⟨s₁, run₁, hdi, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rdi (.mem (at_ b d))] s = some s₁ ∧
          s₁.gpr .rdi = T ∧ (∀ r, r ≠ .rdi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
        refine ⟨_, by xrun [r₁], ?_, ?_, ?_, ?_⟩
        · simp [gpr_setReg, hT]
        · intro r a; simp [gpr_setReg, a]
        all_goals rfl
      refine WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => ?_) hrd hwr, hdi⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)
  have hb' : ∀ s₁ s₂, VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ → VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ → s₁.gpr b = s₂.gpr b := fun s₁ s₂ e₁ e₂ =>
    VG.Proof.AesGcm.X86_64.env_agree e₁ e₂ b hb
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := P) [b] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hb' _ _ (hP _ _ h).1.1 (hP _ _ h).2.1)
      hc) hP hL hL
  have c := VG.Proof.AesGcm.X86_64.rel_env (by decide) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩)
    (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ s₁.gpr .rdi = T) ∧ (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
      s₂.gpr .rdi = T)) (c := .block [.mov .rax (.mem (at_ .r15 0)), .mov .rdx (.mem (at_ .r15 8)),
        .store (at_ .rdi 0) .rax, .store (at_ .rdi 8) .rdx]) ([.rdi] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩)
  exact (VG.Proof.AesGcm.X86_64.rel_block_split (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩) c)).mono
    (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Init`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_aes_expand_key_scratch`, then the hash subkey `CIPH_K(0¹²⁸)` at byte 240 from
`vg_aes_ctr32` over a zero block with a zero counter block (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr ctxH)

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `vg_aes_gcm_init`. -/
theorem init_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.initX86_64.pre s) :
    WP isa (init v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.initX86_64.post s s' := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, r_c, r_s, k_k, k_c, k_s, wc, ws, hL⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hLn : (s.gpr .rsi).toNat = L at *
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := VG.Proof.AesGcm.X86_64.save_ok s .rcx hW pW
  have hsi : s.gpr .rsi = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hR : BitVec.ofNat 64 L >>> 2 + 6#64 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
    rcases hL with rfl | rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h15, h13, hbx, hcx, hdi, hsi₂, hdx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi), .shift .shr .rbx 2,
        .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO) s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rbx = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 512 ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 L ∧
      s₂.gpr .rdx = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, hg₁, hW, hCtx, hK, hsi, hSP, hR]
  generalize hRd : Spec.Aes.rounds (L / 4) = R at hbx
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  refine WP.seq ?_
  rw [List.append_assoc]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := VG.Proof.AesGcm.X86_64.covers_off pW (by decide) (by decide)
  have kc : KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L := by
    refine ⟨hdi, hsi₂, hdx, hcx, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), by rw [hsp]; exact k_k, by rw [hsp]; exact k_c.sub_right (Region.sub_prefix (by decide)),
      by rw [hsp]; exact k_s.sub_right (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂, hrd]
      exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_prefix pC (by decide)) pS))
    · rw [wr₂]; exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_prefix pC (by decide)) pS
  refine WP.seq (WP.mono (key_call v.key kc) fun s₃ g => ?_)
  have g15 : s₃.gpr .r15 = W := by rw [g.saved .r15 (by decide), h15]
  have g13 : s₃.gpr .r13 = Ctx := by rw [g.saved .r13 (by decide), h13]
  have gbx : s₃.gpr .rbx = BitVec.ofNat 64 R := by rw [g.saved .rbx (by decide), hbx]
  have gsp : s₃.gpr .rsp = SP := by rw [g.saved .rsp (by decide), hsp]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂
  have w₁ := VG.Proof.AesGcm.X86_64.in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := VG.Proof.AesGcm.X86_64.in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = BitVec.ofNat 64 R ∧ s₄.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .rcx = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₄.gpr .r9 = W + BitVec.ofNat 64 512 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc, VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, gbx]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), gsp]
  have rd₄ : s₄.rd = s.rd := hrd₄.trans rd₃
  have wr₄ : s₄.wr = s.wr := hwr₄.trans wr₃
  -- The disjointness of the parts.
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, VG.Proof.AesGcm.X86_64.zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      VG.Proof.AesGcm.X86_64.zeroT_bytes]
    decide
  have hk₄ : bytesAt s₄.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      ← hRd, g.out, hm₂, bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Lay.wSub (by decide)))
        (by rcases hL with rfl | rfl | rfl <;> decide)]
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 := by
    refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hR', ?_, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
    · simpa using dCW 0 240 (by decide) 96 16 (by decide)
    · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
    · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact dCW 240 16 (by decide) 512 2048 (by decide)
    · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
    · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
    · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
    · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_prefix pC' (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
        (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
        (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pC' (by decide) (by decide))) (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)))))
    · exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_off pC' (by decide) (by decide))
        (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)))
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have gout := c.out
  rw [VG.Proof.AesGcm.X86_64.blocksAt_one, VG.Proof.AesGcm.X86_64.blocksAt_one, VG.Proof.AesGcm.X86_64.ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c15 : s₅.gpr .r15 = W := by rw [c.saved .r15 (by decide), hg₄ .r15 (by decide), g15]
  have c5sp : s₅.gpr .rsp = SP := by rw [c.saved .rsp (by decide), g4sp]
  have cfr := c.frame
  rw [g4sp] at cfr
  -- The saved registers and the return address.
  have dSv : ∀ r ∈ [(⟨Ctx, 240⟩ : Region), ⟨W + BitVec.ofNat 64 512, 512⟩, below SP 8], (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)) |>.symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (k_s.sub_right (Lay.wSub (by decide))).symm
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩], (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8], (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (k_s.sub_right (Lay.wSub (by decide))).symm
  have hsv₅ : VG.Proof.AesGcm.X86_64.SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← hm₂]; exact g.frame) (by rw [hsp]; exact dSv)).frame f₄ dSv₄).frame cfr dSv₅)
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [VG.Proof.AesGcm.X86_64.ret_kept cfr (fun r hr => ?_), VG.Proof.AesGcm.X86_64.ret_kept f₄ (fun r hr => ?_), VG.Proof.AesGcm.X86_64.ret_kept g.frame (fun r hr => ?_), hm₂,
      VG.Proof.AesGcm.X86_64.ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_s.sub_right (Lay.wSub (by decide))
    · rw [hsp] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact r_c.sub_right (Region.sub_prefix (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.X86_64.ret_below SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.X86_64.ret_below SP
  refine WP.mono (VG.Proof.AesGcm.X86_64.exit_ok c15 (by rw [c5sp, hSP]) (by rw [c.rd, c.wr, wr₄]; exact VG.Proof.AesGcm.X86_64.covers_left pW) hsv₅
    (by rw [hSP, hret])) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.initX86_64]
  rw [hK, hLn, hCtx, hm]
  refine ⟨?_, ?_⟩
  · rw [VG.Proof.AesGcm.X86_64.length_bytesAt, hRd, bytesAt_frame cfr (fun r hr => ?_) (by omega), hk₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact dK0.sub_left (Region.sub_prefix hRb)
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact (k_c.sub_right (Region.sub_prefix (by omega))).symm
  · rw [VG.Proof.AesGcm.X86_64.ctxH_eq, gout.1, Spec.Gcm.aes, VG.Proof.AesGcm.X86_64.length_bytesAt, hRd]
    simp
end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.InitCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code between the calls
is checked by the taint analysis from the public arguments; the calls of
`vg_aes_expand_key_scratch` and `vg_aes_ctr32` have the same arguments in both runs,
which correctness gives (`initA_ok`, `initC_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- After the entry: the call of `vg_aes_expand_key_scratch`, and what stays for the rest. -/
structure InitA (K Ctx W SP : Addr) (L R : Nat) (rd wr : List Region) (s : State) : Prop where
  call : KeyCall s K Ctx (W + BitVec.ofNat 64 512) L
  r15 : s.gpr .r15 = W
  r13 : s.gpr .r13 = Ctx
  rbx : s.gpr .rbx = BitVec.ofNat 64 R
  rsp : s.gpr .rsp = SP
  rd : s.rd = rd
  wr : s.wr = wr

theorem initA_ok {s : State} (hp : Proof.AesGcm.initX86_64.pre s) :
    WP isa (.block (save .rcx ++ ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi),
      .shift .shr .rbx 2, .alu .add .rbx (imm 6)] : List Instr) ++ ptr .rcx .r15 scrO)) s
      (VG.Proof.AesGcm.X86_64.InitA (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsp) (s.gpr .rsi).toNat
        (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4)) s.rd s.wr) := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, -, -, k_k, k_c, k_s, -, -, hL⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hLn : (s.gpr .rsi).toNat = L at *
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := VG.Proof.AesGcm.X86_64.save_ok s .rcx hW pW
  have hsi : s.gpr .rsi = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hR : BitVec.ofNat 64 L >>> 2 + 6#64 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
    rcases hL with rfl | rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h15, h13, hbx, hcx, hdi, hsi₂, hdx, hsp, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi), .shift .shr .rbx 2,
        .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO) s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rbx = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 512 ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 L ∧
      s₂.gpr .rdx = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, gpr_setFlags, rd_setFlags, wr_setFlags, hg₁, hW, hCtx, hK, hsi, hSP, hR]
  rw [List.append_assoc]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_, h15, h13, hbx, hsp,
    hrd₂.trans hrd₁, hwr₂.trans hwr₁⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := VG.Proof.AesGcm.X86_64.covers_off pW (by decide) (by decide)
  refine ⟨hdi, hsi₂, hdx, hcx, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
    d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (by decide)), by rw [hsp]; exact k_k, by rw [hsp]; exact k_c.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact k_s.sub_right (Lay.wSub (by decide)), ?_, ?_⟩
  · rw [rd₂, wr₂, hrd]
    exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_prefix pC (by decide)) pS))
  · rw [wr₂]; exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_prefix pC (by decide)) pS

/-- After the call of `vg_aes_expand_key_scratch`: the call of `vg_aes_ctr32`. -/
theorem initC_ok {s : State} (hp : Proof.AesGcm.initX86_64.pre s) {R : Nat} (hR' : R = 10 ∨ R = 12 ∨ R = 14)
    {s₃ : State} (h15 : s₃.gpr .r15 = s.gpr .rcx) (h13 : s₃.gpr .r13 = s.gpr .rdx)
    (hbx : s₃.gpr .rbx = BitVec.ofNat 64 R) (hsp : s₃.gpr .rsp = s.gpr .rsp) (hwr : s₃.wr = s.wr) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] : List Instr) ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO)) s₃ fun s₄ =>
      CtrCall s₄ (s.gpr .rdx) (s.gpr .rcx + BitVec.ofNat 64 96) (s.gpr .rdx + BitVec.ofNat 64 240)
        (s.gpr .rcx + BitVec.ofNat 64 512) R 1 ∧ s₄.gpr .r15 = s.gpr .rcx ∧ s₄.gpr .rsp = s.gpr .rsp := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨-, hwr', -, -, d_cs, -, -, -, k_c, k_s, wc, -, -⟩ := hp
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr']; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr']; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
  have w₁ := VG.Proof.AesGcm.X86_64.in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := VG.Proof.AesGcm.X86_64.in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) s₃ = some s₄ ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = BitVec.ofNat 64 R ∧ s₄.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .rcx = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₄.gpr .r9 = W + BitVec.ofNat 64 512 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [h15, h13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hbx]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [hg₄ .r15 (by decide), h15], by rw [hg₄ .rsp (by decide), hsp]⟩
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), hsp]
  have wr₄ : s₄.wr = s.wr := hwr₄.trans hwr
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hR', ?_, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
  · simpa using dCW 0 240 (by decide) 96 16 (by decide)
  · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact dCW 240 16 (by decide) 512 2048 (by decide)
  · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
  · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
  · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
  · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
  · exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_prefix pC' (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
      (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide))) (VG.Proof.AesGcm.X86_64.covers_cons
      (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pC' (by decide) (by decide))) (VG.Proof.AesGcm.X86_64.covers_left (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)))))
  · exact VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)) (VG.Proof.AesGcm.X86_64.covers_cons (VG.Proof.AesGcm.X86_64.covers_off pC' (by decide) (by decide))
      (VG.Proof.AesGcm.X86_64.covers_off pW' (by decide) (by decide)))

theorem init_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.initX86_64.pre s₀)
    (hp' : Proof.AesGcm.initX86_64.pre s₀') (hq : Proof.AesGcm.initX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (init v.callees) fun _ _ => True := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅⟩ := hq
  have hL : (s₀.gpr .rsi).toNat = 16 ∨ (s₀.gpr .rsi).toNat = 24 ∨ (s₀.gpr .rsi).toNat = 32 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  generalize hRd : Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) = R
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with h | h | h <;> rw [h] <;> decide
  let A₁ := VG.Proof.AesGcm.X86_64.InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R s₀.rd s₀.wr
  let A₂ := VG.Proof.AesGcm.X86_64.InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R s₀'.rd s₀'.wr
  have hA₂ := VG.Proof.AesGcm.X86_64.initA_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, hRd] at hA₂
  have hA₁ := VG.Proof.AesGcm.X86_64.initA_ok hp
  rw [hRd] at hA₁
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (c := .block (save .rcx ++ [.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi),
        .shift .shr .rbx 2, .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO)) [.rdi, .rsi, .rdx, .rcx, .rsp]
      (fun _ _ h r hr => by
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := A₁) (G₂ := A₂) (fun s h => by subst h; exact hA₁) (fun s h => by subst h; exact hA₂)
  -- After the call of `vg_aes_expand_key_scratch`.
  let K₁ : State → Prop := fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
    s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr
  let K₂ : State → Prop := fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
    s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = s₀'.rd ∧ s₃.wr = s₀'.wr
  have hK : ∀ {rd wr : List Region} (s : State),
      VG.Proof.AesGcm.X86_64.InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R rd wr s →
      WP isa (.call v.key.fn.name v.key.fn.code) s fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
        s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = rd ∧ s₃.wr = wr := fun s h =>
    WP.mono (key_call v.key h.call) fun _ g => ⟨by rw [g.saved .r15 (by decide), h.r15],
      by rw [g.saved .r13 (by decide), h.r13], by rw [g.saved .rbx (by decide), h.rbx],
      by rw [g.saved .rsp (by decide), h.rsp], by rw [g.rd, h.rd], by rw [g.wr, h.wr]⟩
  have k := VG.Proof.AesGcm.X86_64.rel_wp (key_rel v.key (P := fun s₁ s₂ => True ∧ A₁ s₁ ∧ A₂ s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.2.1.call, h.2.2.call, by rw [h.2.1.rsp, h.2.2.rsp]⟩)
    (fun _ _ h => h.2) (G₁ := K₁) (G₂ := K₂) (fun s h => hK s h) (fun s h => hK s h)
  -- The call of `vg_aes_ctr32`.
  let C₁ : State → Prop := fun s₄ => CtrCall s₄ (s₀.gpr .rdx) (s₀.gpr .rcx + BitVec.ofNat 64 96)
    (s₀.gpr .rdx + BitVec.ofNat 64 240) (s₀.gpr .rcx + BitVec.ofNat 64 512) R 1 ∧ s₄.gpr .r15 = s₀.gpr .rcx ∧
    s₄.gpr .rsp = s₀.gpr .rsp
  have hC₁ : ∀ s, K₁ s → WP isa _ s C₁ := fun s h => VG.Proof.AesGcm.X86_64.initC_ok hp hR' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2
  have hC₂ : ∀ s, K₂ s → WP isa _ s C₁ := fun s h => by
    have := VG.Proof.AesGcm.X86_64.initC_ok hp' hR' (s₃ := s) (by rw [h.1, q₄]) (by rw [h.2.1, q₃]) h.2.2.1 (by rw [h.2.2.2.1, q₅])
      h.2.2.2.2.2
    rw [← q₃, ← q₄, ← q₅] at this
    exact this
  have c := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ K₁ s₁ ∧ K₂ s₂) [.r13, .r15, .rbx, .rsp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.1, h.2.2.1]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1]
        · rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hC₁ hC₂
  have hE : ∀ s, C₁ s → WP isa (.call v.ctr.callee.name v.ctr.callee.code) s fun s' =>
      s'.gpr .r15 = s₀.gpr .rcx ∧ s'.gpr .rsp = s₀.gpr .rsp := fun s h =>
    WP.mono (ctr_call v.ctr h.1) fun _ g => ⟨by rw [g.saved .r15 (by decide), h.2.1],
      by rw [g.saved .rsp (by decide), h.2.2]⟩
  have d := VG.Proof.AesGcm.X86_64.rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧ C₁ s₁ ∧ C₁ s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.2, h.2.2.2.2]⟩) (fun _ _ h => h.2) hE hE
  have e := VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ (s₁.gpr .r15 = s₀.gpr .rcx ∧ s₁.gpr .rsp = s₀.gpr .rsp) ∧
      (s₂.gpr .r15 = s₀.gpr .rcx ∧ s₂.gpr .rsp = s₀.gpr .rsp)) (c := .block VG.Impl.AesGcm.X86_64.restore) [.r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.1, h.2.2.1]
      · rw [h.2.1.2, h.2.2.2]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq k (RelCT.seq c (RelCT.seq d e)))

theorem init_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.initX86_64.pre Proof.AesGcm.initX86_64.pub (init v.callees) :=
  VG.Proof.AesGcm.X86_64.ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.init_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry of `finish` and
`verify` takes `W` from the stack and keeps the number of rounds and the
lengths in it (`finEntry_ok`); `finish` keeps the address of `tag` there too,
computes the tag (`finTag 0`) for any message the state represents and
copies it to `tag` (`tagOut_ok`, `streamFinish_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

/-- The kept public values. -/
abbrev slotsR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 176, 32⟩

/-- After `finEntry`: the registers, the kept values, and what changed. -/
structure FinEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9
  saved : VG.Proof.AesGcm.X86_64.SavedAt s.mem W s₀
  frame : Frame [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `finEntry wo`, with `W` at `[rsp + wo]`. -/
theorem finEntry_ok {s : State} {wo : Nat} {Ctx St W SP : Addr} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 wo) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 wo) 8) (hperm : VG.Proof.AesGcm.X86_64.Perm Ctx St W s)
    (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry wo)) s (VG.Proof.AesGcm.X86_64.FinEntry s Ctx St W SP) := by
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp wo))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, ha], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : VG.Proof.AesGcm.X86_64.Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := VG.Proof.AesGcm.X86_64.save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : VG.Proof.AesGcm.X86_64.SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  rw [hm₀] at f₁
  have w₁ := VG.Proof.AesGcm.X86_64.in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃
  have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
  obtain ⟨s₂, run₂, h15, h14, h13, hsp, h9, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
        .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.gpr .r9 = s.gpr .r9 ∧
      s₂.mem = ((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hax : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    refine ⟨_, by xrun [hax, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax]
    · simp [gpr_setReg, g .rdx (by decide), hSt]
    · simp [gpr_setReg, g .rdi (by decide), hCtx]
    · simp [gpr_setReg, g .rsp (by decide), hSP]
    · simp [gpr_setReg, g .r9 (by decide)]
    · simp [mem_setReg, gpr_setReg, g .rsi (by decide), g .rcx (by decide), g .r8 (by decide)]
    all_goals rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have s₁₂ := sep 176 184 (by decide) (by decide) (by decide)
  have s₁₃ := sep 176 192 (by decide) (by decide) (by decide)
  have s₂₃ := sep 184 192 (by decide) (by decide) (by decide)
  have f₂ : Frame [VG.Proof.AesGcm.X86_64.slotsR W] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 208 → (VG.Proof.AesGcm.X86_64.slotsR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, ⟨?_, hR⟩, ?_, ?_, h9, ?_, ?_, hrd', hwr'⟩
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
    exact BitVec.eq_of_toNat_eq (by simp)
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · refine hsv₁'.frame f₂ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · exact (f₁.mono fun r hr => by simp at hr; subst hr; simp).trans (f₂.mono fun r hr => by simp at hr; subst hr; simp)

/-- `tagOut src`: the 16 bytes at `W` copied to `T`, whose address is at `b + d`. -/
theorem tagOut_ok {s : State} {W T : Addr} {b : Reg} {d : Nat} (h15 : s.gpr .r15 = W)
    (hs : s.mem.readW (s.gpr b + BitVec.ofNat 64 d) 64 = T)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 d) 8) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hT : Covers [⟨T, 16⟩] s.wr) :
    ∃ s', runBlock isa (tagOut (at_ b d)) s = some s' ∧ bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧
      Frame [⟨T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .rdi → r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := VG.Proof.AesGcm.X86_64.in_left (rd := s.rd) (VG.Proof.AesGcm.X86_64.in_off hw (show 0 + 8 ≤ 2560 by decide) (by decide))
  have r₁ := VG.Proof.AesGcm.X86_64.in_left (rd := s.rd) (VG.Proof.AesGcm.X86_64.in_off hw (show 8 + 8 ≤ 2560 by decide) (by decide))
  have t₀ := VG.Proof.AesGcm.X86_64.in_off hT (show 0 + 8 ≤ 16 by decide) (by decide)
  have t₁ := VG.Proof.AesGcm.X86_64.in_off hT (show 8 + 8 ≤ 16 by decide) (by decide)
  have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
  have f0 : T + BitVec.ofNat 64 0 = T := BitVec.add_zero T
  rw [e0] at r₀
  rw [f0] at t₀
  refine ⟨_, by simp only [tagOut]; xrun [hs, hr, h15, r₀, r₁, t₀, t₁, e0, f0], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hs, f0]
    rw [Cmac.bytesAt_store2, Cmac.le8_readW, Cmac.le8_readW, ← Cmac.bytesAt_split]
  · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hs, f0]
    exact Cmac.frame_store2 _ _ _
  · intro r a b c; simp [gpr_setReg, a, b, c]
  all_goals rfl

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput ghashFrom ghash blocks zeros padLen ofBytes
  toBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

theorem ghashInput_mod (a c : List Byte) :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

/-- The entry of `finish`, and the address `T` of `tag` kept at `W + 200`. -/
theorem finishEntry_ok {s : State} {Ctx St W SP T : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rdx = St) (hSP : s.gpr .rsp = SP) (hT : s.gpr .r9 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W) (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8)
    (hperm : VG.Proof.AesGcm.X86_64.Perm Ctx St W s)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry 8 ++ ([.store (at_ .r15 tagPO) .r9] : List Instr))) s fun s₂ =>
      VG.Proof.AesGcm.X86_64.FinEntry s Ctx St W SP s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T := by
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.X86_64.finEntry_ok hCtx hSt hSP hW ha hperm L.ww hR) fun s₁ he => ?_)
  have w₁ := he.env.perm.wW (show 200 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.store (at_ .r15 tagPO) .r9] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 200) T ∧ (∀ r, s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.r15, w₁], ?_, ?_, ?_, ?_⟩
    · simp [he.r9, hT]
    all_goals intros; rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have f₂ : Frame [⟨W + BitVec.ofNat 64 200, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 200 ∨ 208 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  refine ⟨⟨he.env.keep (fun r _ => hg₂ r) hrd₂ hwr₂,
    ⟨by rw [rd₂ 176 (.inl (by decide)) (by decide)]; exact he.rounds.1, he.rounds.2⟩,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen, by rw [hg₂]; exact he.r9,
    he.saved.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by decide)) (by decide) (by decide),
    he.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.AesGcm.X86_64.slotsR W, by simp, Offset.sub _ (by decide) (by decide)⟩), hrd₂.trans he.rd, hwr₂.trans he.wr⟩,
    by rw [hm₂, Mem.readW_writeW_self64]⟩

/-- One run of `vg_aes_gcm_stream_finish`, for the input `x` GHASH has. -/
theorem streamFinish_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rdx + BitVec.ofNat 64 16) (s.gpr .rdx + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        bytesAt s'.mem (s.gpr .r9) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .rdi)) (VG.Spec.Gcm.ghash (ctxH s.mem (s.gpr .rdi))
            (blocks (x ++ zeros (padLen x.length)))) [ofBytes (lensBlock (s.gpr .rcx).toNat (s.gpr .r8).toNat)] ^^^
            ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat (blockAt s.mem (s.gpr .rdx)))) := by
  have hp' := hp
  simp only [Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret,
    Proof.AesGcm.rounds, Proof.AesGcm.args, Proof.AesGcm.arg] at hp'
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, d_ts, d_tw, r_s, r_t, r_w, k_c, k_s, -, k_w, wc, ws, -, ww, hR⟩ := hp'
  have hWa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  rw [hA] at hrd
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hT : s.gpr .r9 = T at *
  generalize hW : stackArg s 0 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have hperm : VG.Proof.AesGcm.X86_64.Perm Ctx St W s := ⟨by rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  have hra : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 := by
    rw [hrd]
    exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩
  have hTw : Covers [⟨T, 16⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- The entry, and the address of `tag` kept at `W + 200`.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.finishEntry_ok L hCtx hSt hSP hT hWa hra hperm hR) fun s₂ ⟨he, hT₂⟩ => ?_)
  have F₂ := he.frame
  have he₂ := he.env
  have dF : ∀ d k, (d + k ≤ 16 ∨ (16 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
  have dC : ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact d_cw.sub_right (Lay.wSub (by decide))
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [VG.Proof.AesGcm.X86_64.ctxH_eq, blockAt_frame F₂ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))]
  refine WP.seq (WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.finTag_ok v L (o := 0) (.inl rfl) he₂ he.rounds he.alen he.tlen hx))
    fun s₃ ⟨⟨he₃, _, f₃, ht⟩, hrd₃, hwr₃⟩ => ?_))
  -- The tag copied to `tag`.
  have dT : ∀ r ∈ VG.Proof.AesGcm.X86_64.tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 200, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have hT₃ : s₃.mem.readW (s₃.gpr .r15 + BitVec.ofNat 64 200) 64 = T := by
    rw [he₃.r15, f₃.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) dT (by decide), hT₂]
  obtain ⟨s₄, run₄, hb₄, f₄, hg₄, hrd₄, hwr₄⟩ := VG.Proof.AesGcm.X86_64.tagOut_ok (b := .r15) (d := 200) he₃.r15 hT₃
    (by rw [he₃.r15]; exact he₃.perm.wR (show 200 + 8 ≤ 2560 by decide)) he₃.perm.w
    (by rw [hwr₃, he.wr]; exact hTw)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have he₄ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  have hsv₄ : VG.Proof.AesGcm.X86_64.SavedAt s₄.mem W s :=
    (he.saved.frame f₃ (VG.Proof.AesGcm.X86_64.saved_tagFrame L (.inl rfl))).frame f₄
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (d_tw.sub_right (Lay.wSub (by decide))).symm
  have k₄ : s₄.mem.readW SP 64 = s₃.mem.readW SP 64 := VG.Proof.AesGcm.X86_64.ret_kept f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact r_t
  have k₃ : s₃.mem.readW SP 64 = s₂.mem.readW SP 64 := VG.Proof.AesGcm.X86_64.ret_kept f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Region.sub_prefix (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86_64.ret_below SP
  have k₂ : s₂.mem.readW SP 64 = s.mem.readW SP 64 := VG.Proof.AesGcm.X86_64.ret_kept F₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by rw [k₄, k₃, k₂]
  refine WP.mono (VG.Proof.AesGcm.X86_64.exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (VG.Proof.AesGcm.X86_64.covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ha => ?_⟩
  have ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s₂.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH]
    exact ha.congr (blockAt_frame F₂ (dF 16 16 (.inr ⟨by decide, by decide⟩)))
      (bytesAt_frame F₂ (dF 32 (x.length % 16) (.inr ⟨by decide, by omega⟩)) (by omega))
  have hc : VG.Proof.AesGcm.X86_64.ciphOf s₂.mem Ctx (s.gpr .rsi).toNat = ctxCiph s.mem Ctx (s.gpr .rsi).toNat :=
    VG.Proof.AesGcm.X86_64.ciph_frame F₂ dC hR
  have hJ : blockAt s₂.mem St = blockAt s.mem St := by
    simpa using blockAt_frame F₂ (dF 0 16 (.inl (by decide)))
  rw [hm, hb₄, show W = W + BitVec.ofNat 64 0 by simp, ht ha₂, hc, hJ, hH]

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH ctxCiph ghashInput)

theorem toNat_eq_zero {x : BitVec 64} : x = 0 ↔ x.toNat = 0 :=
  ⟨fun h => by subst h; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- The length GHASH has buffered, from `aad_len` and `text_len`. -/
theorem ghashInput_lens {a c : List Byte} {aL tL : BitVec 64} (ha : aL = BitVec.ofNat 64 a.length)
    (hc : tL.toNat = c.length) :
    (ghashInput a c).length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16 := by
  rw [VG.Proof.AesGcm.X86_64.ghashInput_mod]
  by_cases h : c = []
  · subst h
    have : tL = 0 := toNat_eq_zero.mpr hc
    simp only [this, ↓reduceIte, ha, VG.Proof.AesGcm.X86_64.toNat_mod16]
  · have : tL ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero (by rw [← hc, toNat_eq_zero.mp e]))
    simp only [h, this, ↓reduceIte, hc]

/-- `vg_aes_gcm_stream_finish`. -/
theorem streamFinish_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamFinishX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (VG.Proof.AesGcm.X86_64.streamFinish_run v hp (x := List.replicate
      ((if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (VG.Proof.AesGcm.X86_64.streamFinish_run v hp (VG.Proof.AesGcm.X86_64.ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  rw [hq (iv, a, c) ⟨hA, hT⟩ ha, Proof.Gcm.fullTag_eq, hj, hA, hT, BitVec.toNat_ofNat, VG.Proof.AesGcm.X86_64.lensBlock_mod_left]
  rfl

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. A tag length §5.2.1.2 does
not allow gives 0; any other pads the received tag, read from `tag`
(`recv`), computes the tag (`finTag 0`) and compares (`cmp 0`), without a
branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput ghashFrom ghash blocks zeros padLen ofBytes
  toBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

/-- The regions the check of a received tag writes. -/
abbrev verFrame (St W SP : Addr) : List Region :=
  [⟨St, 32⟩, ⟨W, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩,
    below SP 8]

/-- The tag `finTag` computes, for buffered input `x`. -/
abbrev tagOf (m : Mem) (Ctx St : Addr) (R : Nat) (aL tL : BitVec 64) (x : List Byte) : List Byte :=
  toBytes (ghashFrom (blockAt m (Ctx + BitVec.ofNat 64 240))
    (VG.Spec.Gcm.ghash (blockAt m (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
    [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ VG.Proof.AesGcm.X86_64.ciphOf m Ctx R (blockAt m St))

theorem bytesAt_take (m : Mem) (p : Addr) {t n : Nat} (h : t ≤ n) : bytesAt m p t = (bytesAt m p n).take t := by
  rw [show n = t + (n - t) by omega, VG.Proof.AesGcm.X86_64.bytesAt_add, List.take_left' (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _)]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- A received tag of an allowed length `t`, at `Tp` (in `rsi`), checked. -/
theorem verifyCheck_ok {R t : Nat} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s) (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R)
    {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {Tp : Addr} (hsi : s.gpr .rsi = Tp)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 2560⟩) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
      fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧ Frame (VG.Proof.AesGcm.X86_64.verFrame St W SP) s.mem s'.mem ∧
        (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
          s'.gpr .rax = (if (VG.Proof.AesGcm.X86_64.tagOf s.mem Ctx St R aL tL x).take t = bytesAt s.mem Tp t then 1 else 0)) := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.recv_ok he hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide))))
    fun s₁ ⟨he₁, hrc, f₁, _⟩ => ?_)
  have dW : ∀ d k, (d + k ≤ 256 ∨ 272 ≤ d) → d + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h h' r hr; simp only [List.mem_singleton] at hr; subst hr
    exact L.w_w (by omega) h' (by decide)
  have dS : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], ∀ d k, d + k ≤ 80 →
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro r hr d k hk; simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have rd₁ : ∀ d, d + 8 ≤ 256 → s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₁.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dW d 8 (.inl hd) (by omega))
      (by decide)
  have hR₁ : VG.Proof.AesGcm.X86_64.RoundsAt s₁.mem W R := ⟨by rw [rd₁ 176 (by decide)]; exact hR.1, hR.2⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.finTag_ok v L (o := 0) (.inl rfl) he₁ hR₁ (by rw [rd₁ 184 (by decide), hA])
    (by rw [rd₁ 192 (by decide), hT]) hx) fun s₂ ⟨he₂, _, f₂, ht⟩ => ?_)
  have dT : ∀ d k, 112 ≤ d → d + k ≤ 512 → ∀ r ∈ VG.Proof.AesGcm.X86_64.tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := d) (k := k) (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  have rd₂ : ∀ d, 112 ≤ d → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dT d 8 h₁ h₂) (by decide)
  have r₂ := he₂.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [he₂.r15, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, rd₂ 224 (by decide) (by decide), rd₁ 224 (by decide), htl]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hrc₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem Tp t ++ zeros (16 - t) := by
    rw [hm₃, bytesAt_frame f₂ (dT 256 16 (by decide) (by decide)) (by decide), hrc]
  refine WP.mono (VG.Proof.AesGcm.X86_64.cmp_ok L (o := 0) (.inl rfl) he₃ hbx₃ h1 h16 (VG.Proof.AesGcm.X86_64.length_bytesAt _ _ _) hrc₃)
    fun s₄ ⟨he₄, hax₄, f₄⟩ => ⟨he₄, ?_, fun ha => ?_⟩
  · rw [hm₃] at f₄
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 32⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W, 16⟩, by simp, by simpa using Region.sub_prefix (base := W) (show 16 ≤ 16 by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, fun _ h => h⟩
      · exact ⟨below SP 8, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
  · have dC : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨Ctx, 256⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
      blockAt_frame f₁ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
    have hJ₁ : blockAt s₁.mem St = blockAt s.mem St := by simpa using blockAt_frame f₁ fun r hr => dS r hr 0 16 (by decide)
    have hc₁ : VG.Proof.AesGcm.X86_64.ciphOf s₁.mem Ctx R = VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R := VG.Proof.AesGcm.X86_64.ciph_frame f₁ dC hR.2
    have ha₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
        (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) x := by
      rw [hH₁]
      exact ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide))
        (bytesAt_frame f₁ (fun r hr => dS r hr 32 (x.length % 16) (by omega)) (by omega))
    have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 0) 16 = VG.Proof.AesGcm.X86_64.tagOf s.mem Ctx St R aL tL x := by
      rw [ht ha₁, hH₁, hc₁, hJ₁]
    have hT₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 0) t = (VG.Proof.AesGcm.X86_64.tagOf s.mem Ctx St R aL tL x).take t := by
      rw [hm₃, VG.Proof.AesGcm.X86_64.bytesAt_take _ _ h16, hT₂]
    rw [hax₄, hT₃]

end

/-- After the entry of `verify`: `FinEntry`, the tag length at `W + 224` and
in `rbx`, and the address of `tag` in `rsi`. -/
structure VerEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  tl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s₀ 0
  rbx : s.gpr .rbx = stackArg s₀ 0
  rsi : s.gpr .rsi = s₀.gpr .r9
  saved : VG.Proof.AesGcm.X86_64.SavedAt s.mem W s₀
  frame : Frame [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `verify`, with `W` at `[rsp + 16]` and the tag length at `[rsp + 8]`. -/
theorem verifyEntry_ok {s : State} {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rdx = St) (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8) (ht : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8)
    (dA : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨W, 2560⟩) (hperm : VG.Proof.AesGcm.X86_64.Perm Ctx St W s)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry 16 ++ ([.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx,
      .mov .rsi (.reg .r9)] : List Instr))) s (VG.Proof.AesGcm.X86_64.VerEntry s Ctx St W SP) := by
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.X86_64.finEntry_ok hCtx hSt hSP hW ha hperm L.ww hR) fun s₁ he => ?_)
  have dA' : ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W], (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact dA.sub_right (Lay.wSub (by decide))
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = stackArg s 0 := by
    rw [he.frame.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) dA' (by decide), ← hSP]; rfl
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 8) 8 := by rw [he.rd, he.wr]; exact ht
  have w₁ := he.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hsi₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 8)),
      .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r9)] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 0 ∧
      s₂.gpr .rsi = s.gpr .r9 ∧ (∀ r, r ≠ .rbx → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 0) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.rsp, he.env.r15, r₁, w₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₁]
    · simp [gpr_setReg, he.r9]
    · intro r a b; simp [gpr_setReg, a, b]
    · simp [mem_setReg, gpr_setReg, htl₁]
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 224 ∨ 232 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  exact ⟨he.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    ⟨by rw [rd₂ 176 (.inl (by decide)) (by decide)]; exact he.rounds.1, he.rounds.2⟩,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen,
    by rw [hm₂, Mem.readW_writeW_self64], hbx₂, hsi₂,
    he.saved.frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by decide)) (by decide) (by decide)),
    (he.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp).trans
      (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp),
    hrd₂.trans he.rd, hwr₂.trans he.wr⟩

/-- What the precondition of `verify` gives. -/
theorem ver_lay {s : State} (hp : Proof.AesGcm.verifyPre s) :
    VG.Proof.AesGcm.X86_64.Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) ∧
      VG.Proof.AesGcm.X86_64.Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) s ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      (⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 80⟩ ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) := by
  simp only [Proof.AesGcm.verifyPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, d_tw, d_wa, r_s, r_w, k_c, k_s, k_w, wc, ws, -, ww, -, hR⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  rw [hA] at hrd d_wa
  have pa : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  refine ⟨Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w,
    ⟨by rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩, ?_,
    by simpa using VG.Proof.AesGcm.X86_64.in_off pa (d := 0) (n := 8) (by decide) (by decide),
    d_wa.symm.sub_left (Region.sub_prefix (by decide)),
    by rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
    by simpa using d_tw, r_s, r_w, d_sw, hR⟩
  have := VG.Proof.AesGcm.X86_64.in_off pa (d := 8) (n := 8) (by decide) (by decide)
  rwa [VG.Proof.AesGcm.X86_64.add_ofNat_assoc] at this

/-- One run of `vg_aes_gcm_stream_verify`, for the input `x` GHASH has. -/
theorem streamVerify_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamVerifyX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rdx + BitVec.ofNat 64 16) (s.gpr .rdx + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        let T := VG.Proof.AesGcm.X86_64.tagOf s.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x
        let t := (stackArg s 0).toNat
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s.mem (s.gpr .r9) t then s'.gpr .rax = 1
        else s'.gpr .rax = 0) := by
  obtain ⟨L, hperm, ha, hta, dA, hTr, dTW, r_s, r_w, d_sw, hR⟩ := VG.Proof.AesGcm.X86_64.ver_lay hp
  have hW : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hTp : s.gpr .r9 = Tp at *
  generalize hWd : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  -- The entry, and the tag length kept at `W + 224`.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.verifyEntry_ok L hCtx hSt hSP hW ha hta dA hperm hR) fun s₂ he => ?_)
  generalize htl : stackArg s 0 = tl at *
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.tagLenOk_ok s₂ (t := tl.toNat) (by rw [he.rbx, htl]; simp) tl.isLt) fun s₃ ⟨hz₃, k₃⟩ => ?_)
  have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₃ := he.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k₃.gpr _ (by decide)) k₃.rd k₃.wr
  have F₃ : Frame [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₃.mem := by rw [k₃.mem]; exact he.frame
  have dF : ∀ p k, (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact h.sub_right (Lay.wSub (by decide))
  generalize ht : tl.toNat = t at *
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [k₃.mem, he.tl, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k₃.gpr _ (by decide), he.rbx, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsi₃ : s₃.gpr .rsi = Tp := by rw [k₃.gpr _ (by decide), he.rsi, hTp]
  have hR₃ : VG.Proof.AesGcm.X86_64.RoundsAt s₃.mem W (s.gpr .rsi).toNat := by rw [k₃.mem]; exact he.rounds
  have hA₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = s.gpr .rcx := by rw [k₃.mem]; exact he.alen
  have hT₃ : s₃.mem.readW (W + BitVec.ofNat 64 192) 64 = s.gpr .r8 := by rw [k₃.mem]; exact he.tlen
  have hTr₃ : Covers [⟨Tp, t⟩] (s₃.rd ++ s₃.wr) := by rw [k₃.rd, k₃.wr, he.rd, he.wr]; exact hTr
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₄ ∧ Frame (VG.Proof.AesGcm.X86_64.verFrame St W SP) s₃.mem s₄.mem ∧
      (Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
          (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x →
        let T := VG.Proof.AesGcm.X86_64.tagOf s₃.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s₃.mem Tp t then s₄.gpr .rax = 1 else s₄.gpr .rax = 0))
    (WP.ite (!Spec.Gcm.tagLenOk t) (VG.Proof.AesGcm.X86_64.eval_e hz₃) (fun hbad => ?_) (fun hok => ?_)) fun s₄ h₄ => ?_)
  · -- A length §5.2.1.2 does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₄ => s₄.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
        s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₄ ⟨hax, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
    refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄, by rw [hm₄]; exact Frame.refl _ _,
      fun _ => ?_⟩
    simp only [hbad', Bool.false_eq_true, false_and, ↓reduceIte]
    exact hax
  · -- An allowed length.
    have hok' : Spec.Gcm.tagLenOk t = true := by simpa using hok
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok'
      omega
    refine WP.mono (VG.Proof.AesGcm.X86_64.verifyCheck_ok v L he₃ hR₃ hA₃ hT₃ htl₃ hbx₃ hb.1 hb.2 hsi₃
      hTr₃ dTW hx)
      fun s₄ ⟨he₄, f₄, hq⟩ => ⟨he₄, f₄, fun ha => ?_⟩
    simp only [hok', true_and]
    have hax := hq ha
    split
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
  obtain ⟨he₄, f₄, hq⟩ := h₄
  have dV : ∀ r ∈ VG.Proof.AesGcm.X86_64.verFrame St W SP, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := 128) (k := 48) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have hsv₃ : VG.Proof.AesGcm.X86_64.SavedAt s₃.mem W s := by rw [k₃.mem]; exact he.saved
  have hsv₄ : VG.Proof.AesGcm.X86_64.SavedAt s₄.mem W s := hsv₃.frame f₄ dV
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [VG.Proof.AesGcm.X86_64.ret_kept f₄ (fun r hr => ?_), VG.Proof.AesGcm.X86_64.ret_kept F₃ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.X86_64.ret_below SP
  refine WP.mono (VG.Proof.AesGcm.X86_64.exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (VG.Proof.AesGcm.X86_64.covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, _, hax⟩ => ⟨hg, fun ha => ?_⟩
  have dS : ∀ d k, d + k ≤ 80 → ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W, VG.Proof.AesGcm.X86_64.slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun d k hk => dF _ _ (d_sw.sub_left (Lay.stSub hk))
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [VG.Proof.AesGcm.X86_64.ctxH_eq]; exact blockAt_frame F₃ (dF _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))
  have ha₃ : Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
      (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH₃]
    exact ha.congr (blockAt_frame F₃ (dS 16 16 (by decide))) (bytesAt_frame F₃ (dS 32 _ (by omega)) (by omega))
  have hT : VG.Proof.AesGcm.X86_64.tagOf s₃.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x =
      VG.Proof.AesGcm.X86_64.tagOf s.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x := by
    simp only [VG.Proof.AesGcm.X86_64.tagOf]
    rw [hH₃, ← VG.Proof.AesGcm.X86_64.ctxH_eq, VG.Proof.AesGcm.X86_64.ciph_frame F₃ (dF _ _ L.cw') hR, show blockAt s₃.mem St = blockAt s.mem St by
      simpa using blockAt_frame F₃ (dS 0 16 (by decide))]
  have hrc : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame F₃ (dF _ _ dTW) (by rw [← ht]; exact Nat.le_of_lt tl.isLt)
  have hq' := hq ha₃
  rw [hT, hrc] at hq'
  dsimp only
  rw [hax]
  exact hq'

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH ctxCiph ghashInput zeros blockAt)

theorem tagOf_eq {m : Mem} {Ctx St : Addr} {R : Nat} {aL tL : BitVec 64} {ciph : Spec.Gcm.Block → Spec.Gcm.Block}
    {iv a c : List Byte} (hj : blockAt m St = Spec.Gcm.j0 (ctxH m Ctx) iv) (hc : ciph = ctxCiph m Ctx R)
    (hA : aL = BitVec.ofNat 64 a.length) (hT : tL.toNat = c.length) :
    VG.Proof.AesGcm.X86_64.tagOf m Ctx St R aL tL (ghashInput a c) = Spec.Gcm.fullTag ciph (ctxH m Ctx) iv a c := by
  rw [Proof.Gcm.fullTag_eq, VG.Proof.AesGcm.X86_64.tagOf, ← VG.Proof.AesGcm.X86_64.ctxH_eq, hj, hA, hT, BitVec.toNat_ofNat, VG.Proof.AesGcm.X86_64.lensBlock_mod_left, hc]
  rfl

/-- `vg_aes_gcm_stream_verify`. -/
theorem streamVerify_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamVerifyX86_64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamVerifyX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (VG.Proof.AesGcm.X86_64.streamVerify_run v hp (x := List.replicate
      ((if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (VG.Proof.AesGcm.X86_64.streamVerify_run v hp (VG.Proof.AesGcm.X86_64.ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  have e := hq (iv, a, c) ⟨hA, hT⟩ ha
  simp only [Proof.AesGcm.arg] at e ⊢
  rw [VG.Proof.AesGcm.X86_64.tagOf_eq hj rfl hA hT] at e
  split
  · next hc => simp only [hc, and_self, ↓reduceIte] at e; rw [e]; rfl
  · next hc => simp only [hc, ↓reduceIte] at e; rw [e]; rfl

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneShot`. -/
section

/-!
# AES-GCM on x86-64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. Their streaming state is in
`work`, at `W + 16`. The entry takes `W` from the stack and keeps the public
arguments in it (`oneEntry_ok`); `oneAad` computes `J₀` and absorbs the additional data,
padded (`oneAad_ok`); `oneCrypt` runs counter mode over the data from the
first counter block (`oneCrypt_ok`); and `oneTag o` absorbs the ciphertext,
padded, and writes the tag to `W + o` (`oneTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the entry of `seal` and `open` writes in `W`. -/
abbrev oneR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 112⟩

/-- What the precondition of `seal` (`k = 3`) and `open` (`k = 4`) gives. -/
structure OneCtx (s : State) (k : Nat) (Ctx W SP Np A D : Addr) (nl al n : Nat) : Prop where
  lay : VG.Proof.AesGcm.X86_64.Lay Ctx (W + BitVec.ofNat 64 16) W SP
  perm : VG.Proof.AesGcm.X86_64.Perm Ctx (W + BitVec.ofNat 64 16) W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : ∀ i < k, InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 * (i + 1))) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩
  nonce : VG.Proof.AesGcm.X86_64.DataOk (W + BitVec.ofNat 64 16) W SP s Np nl
  aad : VG.Proof.AesGcm.X86_64.DataOk (W + BitVec.ofNat 64 16) W SP s A al
  data : VG.Proof.AesGcm.X86_64.DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  /-- The stack of the call of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks`. -/
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

/-- `OneCtx`, from `oneLay` and where the buffers are, with `work` the `w`-th
of `k` arguments on the stack. -/
theorem OneCtx.of {w k : Nat} {s : State} (hp : Proof.AesGcm.oneLay w k s)
    (pc : Covers [⟨s.gpr .rdi, 256⟩] (s.rd ++ s.wr)) (pn : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (pa : Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr))
    (pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * k⟩] (s.rd ++ s.wr))
    (pd : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr) (pW : Covers [⟨stackArg s w, 2560⟩] s.wr) :
    VG.Proof.AesGcm.X86_64.OneCtx s k (s.gpr .rdi) (stackArg s w) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0)
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat := by
  simp only [Proof.AesGcm.oneLay, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨d_cd, d_cw, d_nd, d_nw, d_ad, d_aw, d_dw, d_da, d_wa, r_d, r_w, t_c, t_n, t_a, t_d, t_w,
    wc, wn, wa, wd, ww, sp24, wsp, hR⟩ := hp
  have b8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by decide) (by decide)
  have k_c := t_c.sub_left b8
  have k_n := t_n.sub_left b8
  have k_a := t_a.sub_left b8
  have k_d := t_d.sub_left b8
  have k_w := t_w.sub_left b8
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at d_da d_wa
  have hSt : (⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ : Region).Sub ⟨stackArg s w, 2560⟩ := Lay.wSub (by decide)
  have L : VG.Proof.AesGcm.X86_64.Lay (s.gpr .rdi) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) (s.gpr .rsp) := by
    refine ⟨wc, ?_, ww, d_cw.sub_right hSt, d_cw, ?_, ?_, k_c, k_w.sub_right hSt, k_w⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le ((stackArg s w).toNat + 16 % 2 ^ 64) (2 ^ 64)
      omega
    · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
        (by omega) (by omega)
    · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
        (by omega) (by omega)
  refine ⟨L, ⟨pc, VG.Proof.AesGcm.X86_64.covers_off pW (show 16 + 80 ≤ 2560 by decide) (by decide), pW⟩, ww, fun i hi => ?_,
    d_wa.symm, ⟨pn, by have := (s.gpr .rcx).isLt; omega, wn, d_nw.sub_right hSt, d_nw, k_n⟩,
    ⟨pa, by have := (s.gpr .r9).isLt; omega, wa, d_aw.sub_right hSt, d_aw, k_a⟩,
    ⟨⟨VG.Proof.AesGcm.X86_64.covers_left pd, by have := (stackArg s 1).isLt; omega, wd, d_dw.sub_right hSt, d_dw, k_d⟩, pd, d_cd⟩,
    r_d, r_w, d_dw, d_da.symm, hR, t_c, t_w, t_d, sp24⟩
  have := VG.Proof.AesGcm.X86_64.in_off pm (d := 8 * i) (n := 8) (by omega) (by omega)
  rwa [VG.Proof.AesGcm.X86_64.add_ofNat_assoc, show 8 + 8 * i = 8 * (i + 1) by omega] at this

/-- What `seal`'s precondition gives: `OneCtx`, and `tag`, 16 bytes to write
at `T` (the third argument on the stack). -/
theorem OneCtx.ofSeal {s : State} (hp : Proof.AesGcm.sealPre s) :
    VG.Proof.AesGcm.X86_64.OneCtx s 4 (s.gpr .rdi) (stackArg s 3) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0)
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat ∧ Covers [⟨stackArg s 2, 16⟩] s.wr ∧
      (⟨stackArg s 2, 16⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
      (⟨stackArg s 2, 16⟩ : Region).Disjoint ⟨stackArg s 3, 2560⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, 16⟩ := by
  have hp' := hp
  simp only [Proof.AesGcm.sealPre, Proof.AesGcm.ret, Proof.AesGcm.args, Proof.AesGcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, r_t, -⟩ := hp'
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 3) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, r_t⟩
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- What `open`'s precondition gives: `OneCtx`, and the received tag, the
`tag_len` (fourth argument on the stack) bytes to read at `T` (the third). -/
theorem OneCtx.ofOpen {s : State} (hp : Proof.AesGcm.openPre s) :
    VG.Proof.AesGcm.X86_64.OneCtx s 5 (s.gpr .rdi) (stackArg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0)
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat ∧
      Covers [⟨stackArg s 2, (stackArg s 3).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
      (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 4, 2560⟩ ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩ := by
  have hp' := hp
  simp only [Proof.AesGcm.openPre, Proof.AesGcm.stk24, Proof.AesGcm.args, Proof.AesGcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, t_t, -⟩ := hp'
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 4) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, t_t⟩
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- After `oneEntry`. -/
structure OneEntry (s₀ : State) (Ctx W SP A D : Addr) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W (s₀.gpr .rsi).toNat
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r9
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = s₀.gpr .rdx
  rbp : s.gpr .rbp = s₀.gpr .rcx
  rsp : s.gpr .rsp = SP
  saved : VG.Proof.AesGcm.X86_64.SavedAt s.mem W s₀
  frame : Frame [VG.Proof.AesGcm.X86_64.oneR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `oneEntry wo`, with `W` at `[rsp + wo]`. -/
theorem oneEntry_ok {s : State} {k : Nat} (hk : 2 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : VG.Proof.AesGcm.X86_64.OneCtx s k Ctx W SP Np A D nl al n) {wo : Nat} (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP)
    (hA : s.gpr .r8 = A) (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n)
    (hW' : s.mem.readW (SP + BitVec.ofNat 64 wo) 64 = W) (a₂ : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 wo) 8) :
    WP isa (.block (oneEntry wo)) s (VG.Proof.AesGcm.X86_64.OneEntry s Ctx W SP A D n) := by
  have hD' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D := by rw [← hD, ← hSP]; rfl
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  have a₀ := C.args 0 (by omega)
  have a₁ := C.args 1 (by omega)
  simp only [Nat.zero_add, Nat.mul_one] at a₀ a₁
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp wo))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, a₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : VG.Proof.AesGcm.X86_64.Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := C.perm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := VG.Proof.AesGcm.X86_64.save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : VG.Proof.AesGcm.X86_64.SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := VG.Proof.AesGcm.X86_64.in_off C.perm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.in_off C.perm.w (show 232 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.in_off C.perm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := VG.Proof.AesGcm.X86_64.in_off C.perm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := VG.Proof.AesGcm.X86_64.in_off C.perm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₀ a₁
  have dAW : ∀ i < 2, ∀ (m : Mem) (k' : Nat), Frame [⟨W + BitVec.ofNat 64 128, k'⟩] s.mem m → k' ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = s.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
    fun i hi m k' hf hk' => hf.readW (r := ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := (C.dA.sub_left (show Region.Sub ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ by
          rw [show 8 * (i + 1) = 8 + 8 * i by omega, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact Offset.sub_base _ (by omega)))
        exact this.sub_right (Lay.wSub (by omega))) (by decide)
  have hD₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = D := by
    have := dAW 0 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hD'] using this
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n := by
    have := dAW 1 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hn'] using this
  have sA : ∀ e d, (e = 8 ∨ e = 16) → 176 ≤ d → d + 8 ≤ 240 →
      Mem.Sep (SP + BitVec.ofNat 64 e) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) := by
    intro e d he h₁ h₂
    refine Region.Disjoint.sep (?_ : (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩)
      (Region.contains_self _ _) (Region.contains_self _ _)
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := by
      rcases he with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · rw [show (16 : Nat) = 8 + 8 by rfl, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
    exact (C.dA.sub_left hs).sub_right (Lay.wSub (by omega))
  have p₁ := sA 8 176 (.inl rfl) (by decide) (by decide)
  have p₂ := sA 8 232 (.inl rfl) (by decide) (by decide)
  have p₃ := sA 8 184 (.inl rfl) (by decide) (by decide)
  have p₄ := sA 16 176 (.inr rfl) (by decide) (by decide)
  have p₅ := sA 16 232 (.inr rfl) (by decide) (by decide)
  have p₆ := sA 16 184 (.inr rfl) (by decide) (by decide)
  have p₇ := sA 16 200 (.inr rfl) (by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have q₀ := sep 176 232 (by decide) (by decide) (by decide)
  have q₁ := sep 176 184 (by decide) (by decide) (by decide)
  have q₂ := sep 176 200 (by decide) (by decide) (by decide)
  have q₃ := sep 176 208 (by decide) (by decide) (by decide)
  have q₄ := sep 232 184 (by decide) (by decide) (by decide)
  have q₅ := sep 232 200 (by decide) (by decide) (by decide)
  have q₆ := sep 232 208 (by decide) (by decide) (by decide)
  have q₇ := sep 184 200 (by decide) (by decide) (by decide)
  have q₈ := sep 184 208 (by decide) (by decide) (by decide)
  have q₉ := sep 200 208 (by decide) (by decide) (by decide)
  have e : oneEntry wo = [.mov .rax (.mem (at_ .rsp wo))] ++ save .rax ++
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 16)),
        .store (at_ .r15 lenO) .rax, .mov .r12 (.reg .rdx), .mov .rbp (.reg .rcx)] := by
    simp [oneEntry, ptr, stO]
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 16)),
        .store (at_ .r15 lenO) .rax, .mov .r12 (.reg .rdx), .mov .rbp (.reg .rcx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = s.gpr .rdx ∧
      s₂.gpr .rbp = s.gpr .rcx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 232) A).writeW
        (W + BitVec.ofNat 64 184) (s.gpr .r9)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₀, a₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hrdi, hCtx]
    · simp [gpr_setReg, gpr_arithFlags, hrdx]
    · simp [gpr_setReg, gpr_arithFlags, hrcx]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, gpr_arithFlags,
        Mem.readW_writeW_sep, hD₁, hn₁, hrsi, hr8, hr9, hA]
    all_goals rfl
  rw [e]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 64⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 240 → (⟨W + BitVec.ofNat 64 176, 64⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 232 ∧ v = A) ∨ (d = 184 ∧ v = s.gpr .r9) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64,
        Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, C.perm.of_eq hrd' hwr'⟩, ⟨?_, C.rounds⟩, rd 232 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 184 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))), h12, hbp, hsp, ?_, ?_, hrd', hwr'⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by have := C.ww; omega) (by have := C.ww; omega)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `seal` and `open` write after their entry: `W` but for the saved
registers and the kept values, the data and the stack. -/
abbrev oneFrame (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 8]

/-- What the pieces but `crypt` and the tag write: `W` but for the received
tag, the saved registers and the kept values, and the stack. -/
abbrev wFrame (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, below SP 8]

theorem wFrame_one {W D SP : Addr} {n o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86_64.wFrame W SP) m m') : Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by omega)⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem wFrame_cons {W SP : Addr} {o : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86_64.wFrame W SP) m m' := h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem w_wFrame {W SP : Addr} {d k : Nat}
    (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ VG.Proof.AesGcm.X86_64.wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem st_wFrame {W SP : Addr} {d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ VG.Proof.AesGcm.X86_64.wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact VG.Proof.AesGcm.X86_64.w_wFrame (.inl ⟨by omega, by omega⟩)

section
variable {Ctx W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
/-- A part of `W` in `oneFrame`. -/
theorem w_oneFrame {D SP : Addr} {n d k : Nat} (h : d + k ≤ 128 ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit L in
theorem st_oneFrame {D SP : Addr} {n d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact VG.Proof.AesGcm.X86_64.w_oneFrame (.inl (by omega))

/-- The kept values are outside `oneFrame`. -/
theorem kept_oneFrame {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h : (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact (L.stk_w (by omega)).symm

theorem saved_oneFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, (VG.Proof.AesGcm.X86_64.savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (L.stk_w (by decide)).symm

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After `oneAad`: `J₀`, the additional data absorbed and padded, and the
first counter block. -/
structure OneAad (Ctx W SP : Addr) (H : Block) (iv a : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) m₀ s.mem

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem j0Frame_one {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.j0Frame (W + BitVec.ofNat 64 16) W SP) m m') :
    Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem absFrame_one {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16) m m') :
    Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86_64.st_wFrame (by decide)
  · exact VG.Proof.AesGcm.X86_64.st_wFrame (by decide)
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem tFrame_one {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16) m m') :
    Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86_64.st_wFrame (by decide)
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesGcm.X86_64.w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem crFrame_one {D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.crFrame (W + BitVec.ofNat 64 16) W SP D n) m m') :
    Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  · exact VG.Proof.AesGcm.X86_64.st_oneFrame (by decide)
  · exact VG.Proof.AesGcm.X86_64.w_oneFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem tagFrame_one {o : Nat} {m m' : Mem}
    (h : Frame (VG.Proof.AesGcm.X86_64.tagFrame (W + BitVec.ofNat 64 16) W SP o) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86_64.wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, hr, hs⟩ := VG.Proof.AesGcm.X86_64.w_wFrame (W := W) (SP := SP) (d := 16) (k := 32) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · obtain ⟨r, hr, hs⟩ := VG.Proof.AesGcm.X86_64.w_wFrame (W := W) (SP := SP) (d := 96) (k := 16) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · obtain ⟨r, hr, hs⟩ := VG.Proof.AesGcm.X86_64.w_wFrame (W := W) (SP := SP) (d := 512) (k := 2048) (.inr (.inr ⟨by decide, by decide⟩))
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

/-- `oneAad`. -/
theorem oneAad_ok {D Np A : Addr} {nl al n : Nat} {H : Block} {s : State} (he : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (h12 : s.gpr .r12 = Np) (hbp : s.gpr .rbp = BitVec.ofNat 64 nl)
    (hN : VG.Proof.AesGcm.X86_64.DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) (hAd : VG.Proof.AesGcm.X86_64.DataOk (W + BitVec.ofNat 64 16) W SP s A al)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) :
    WP isa (oneAad v.callees) s (VG.Proof.AesGcm.X86_64.OneAad Ctx W SP H (bytesAt s.mem Np nl) (bytesAt s.mem A al) s.mem) := by
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.j0_ok v L ⟨he, hH, h12, hbp, hN⟩)) fun s₁ ⟨jo, hrd₁, hwr₁⟩ => ?_)
  have f₁ := VG.Proof.AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (VG.Proof.AesGcm.X86_64.wFrame_cons (VG.Proof.AesGcm.X86_64.j0Frame_one jo.frame))
  have he₁ := jo.env
  have kp : ∀ {m m' : Mem}, Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) m m' → ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.kept_oneFrame L hDW hd)
      (by decide)
  have q₁ := he₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₁.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, h12₂, hbp₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)] s₁ = some s₂ ∧
      s₂.gpr .r12 = A ∧ s₂.gpr .rbp = BitVec.ofNat 64 al ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he₁.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₁ 232 (.inr ⟨by decide, by decide⟩), haad]
    · simp [gpr_setReg, kp f₁ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have dAj : ∀ r ∈ VG.Proof.AesGcm.X86_64.j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨A, al⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hAd.st
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.stk.symm
  have ha₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by
    rw [hm₂]; exact bytesAt_frame jo.frame dAj (by have := hAd.lt; omega)
  have hai : VG.Proof.AesGcm.X86_64.AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H [] A al s₂ :=
    ⟨he₂, h12₂, hbp₂, hbx₂, hAd.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]), by rw [hm₂]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₃ ⟨ho, hrd₃, hwr₃⟩ => ?_)
  rw [List.nil_append, ha₂] at ho
  have he₃ := ho.env
  have f₃ := VG.Proof.AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (VG.Proof.AesGcm.X86_64.wFrame_cons (VG.Proof.AesGcm.X86_64.absFrame_one ho.frame))
  rw [hm₂] at f₃
  have q₃ := he₃.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hbx₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s₃ = some s₄ ∧ s₄.gpr .rbx = BitVec.ofNat 64 ((bytesAt s.mem A al).length % 16) ∧
      (∀ r, r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 al)
    rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide), VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt (by have := hAd.lt; omega)] at hand
    refine ⟨_, by xrun [he₃.r15, q₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, kp f₃ 184 (.inl ⟨by decide, by decide⟩),
        kp f₁ 184 (.inl ⟨by decide, by decide⟩), hal, hand, VG.Proof.AesGcm.X86_64.length_bytesAt]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (VG.Proof.AesGcm.X86_64.ctx_absFrame L (.inr rfl)), hm₂, jo.hH]
  refine WP.mono (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₄, by rw [hm₄, hH₃]⟩ hbx₄) fun s₅ hf => ?_
  rw [hm₄] at hf
  have dS0 : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r ∧
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨(L.stk_st (by decide)).symm, (L.stk_st (by decide)).symm⟩
  have dT0 : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r ∧
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨(L.stk_st (by decide)).symm, (L.stk_st (by decide)).symm⟩
  have hj₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H (bytesAt s.mem Np nl) := by
    have e₁ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame hf.frame fun r hr => by simpa using (dT0 r hr).1
    have e₂ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = blockAt s₁.mem (W + BitVec.ofNat 64 16) := by
      rw [blockAt_frame ho.frame fun r hr => by simpa using (dS0 r hr).1, hm₂]
    rw [e₁, e₂]; exact jo.j0
  refine ⟨hf.env, hf.hH, hj₅, hf.abs (ho.abs (by rw [hm₂]; exact Proof.Gcm.absorbed_nil _ jo.y)), ?_, ?_⟩
  · rw [blockAt_frame hf.frame (fun r hr => (dT0 r hr).2), blockAt_frame ho.frame (fun r hr => (dS0 r hr).2), hm₂]
    exact jo.cb
  · have g₁ := VG.Proof.AesGcm.X86_64.j0Frame_one jo.frame
    have g₃ := VG.Proof.AesGcm.X86_64.absFrame_one ho.frame
    rw [hm₂] at g₃
    exact (g₁.trans g₃).trans (VG.Proof.AesGcm.X86_64.tFrame_one hf.frame)

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

theorem padded_eq (a c : List Byte) :
    a ++ zeros (padLen a.length) ++ c ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have : padLen (a ++ zeros (padLen a.length)).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [List.append_nil, this, padded, Proof.Gcm.ghashInput_nil]
    simp [zeros]
  · rw [padded, Proof.Gcm.ghashInput_of_ne hc]

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneCrypt`: counter mode over the data, from the first counter block. -/
theorem oneCrypt_ok {R : Nat} {icb : Block} {P : Nat} (hP : P % 16 = 0) {D : Addr} {n : Nat} {s : State}
    (he : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : VG.Proof.AesGcm.X86_64.DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneCrypt v.callees) s fun s' => VG.Proof.AesGcm.X86_64.CrOut Ctx (W + BitVec.ofNat 64 16) W SP R icb P D n s.mem s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hP]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have := WP.with_rdwr (VG.Proof.AesGcm.X86_64.crypt_ok v L (R := R) (icb := icb) (P := P)
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁]; exact hR⟩)
  rw [hm₁] at this
  exact WP.mono this fun s' ⟨h, a, b⟩ => ⟨h, a.trans hrd₁, b.trans hwr₁⟩

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneTag o`: the ciphertext absorbed, padded, and the tag into `W + o`. -/
theorem oneTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {D : Addr} {n N al : Nat} {H : Block} {x : List Byte}
    (hx16 : x.length % 16 = 0) {s : State}
    (he : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : VG.Proof.AesGcm.X86_64.RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hd : VG.Proof.AesGcm.X86_64.DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (oneTag v.callees o) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86_64.wFrame W SP) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ VG.Proof.AesGcm.X86_64.ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) := by
  have kp : ∀ {m m' : Mem}, Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) m m' → ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.kept_oneFrame L hDW hd)
      (by decide)
  have hlt := hd.lt
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hx16]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have hai : VG.Proof.AesGcm.X86_64.AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H x D n s₁ :=
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁, hH]⟩
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₂ ⟨ho', hrd₂, hwr₂⟩ => ?_)
  rw [hm₁] at ho'
  have he₂ := ho'.env
  have g₂ := VG.Proof.AesGcm.X86_64.absFrame_one ho'.frame
  have f₂ := VG.Proof.AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (VG.Proof.AesGcm.X86_64.wFrame_cons g₂)
  have q₃ := he₂.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 lenO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 ((x ++ bytesAt s.mem D n).length % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
    rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide), VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hlt] at hand
    have e : (x ++ bytesAt s.mem D n).length % 16 = n % 16 := by
      simp only [List.length_append, VG.Proof.AesGcm.X86_64.length_bytesAt]; omega
    refine ⟨_, by xrun [he₂.r15, q₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, kp f₂ 208 (.inl ⟨by decide, by decide⟩), hlen, hand, e]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho'.frame (VG.Proof.AesGcm.X86_64.ctx_absFrame L (.inr rfl)), hH]
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₃, by rw [hm₃, hH₂]⟩ hbx₃))
    fun s₄ ⟨hf, hrd₄, hwr₄⟩ => ?_)
  rw [hm₃] at hf
  have he₄ := hf.env
  have g₄ := VG.Proof.AesGcm.X86_64.tFrame_one hf.frame
  have f₄ := VG.Proof.AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (VG.Proof.AesGcm.X86_64.wFrame_cons g₄)
  have q₄ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have q₅ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧ s₅.gpr .rbx = BitVec.ofNat 64 al ∧
      s₅.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧
      s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, q₄, q₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₄ 184 (.inl ⟨by decide, by decide⟩), kp f₂ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg, kp f₄ 192 (.inl ⟨by decide, by decide⟩), kp f₂ 192 (.inl ⟨by decide, by decide⟩), htl]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : VG.Proof.AesGcm.X86_64.Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have g₅ : Frame (VG.Proof.AesGcm.X86_64.wFrame W SP) s.mem s₅.mem := by rw [hm₅]; exact g₂.trans g₄
  have f₅ : Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) s.mem s₅.mem := VG.Proof.AesGcm.X86_64.wFrame_one (o := 0) (.inl rfl) (VG.Proof.AesGcm.X86_64.wFrame_cons g₅)
  have hR₅ : VG.Proof.AesGcm.X86_64.RoundsAt s₅.mem W R := ⟨by rw [kp f₅ 176 (.inl ⟨by decide, by decide⟩)]; exact hR.1, hR.2⟩
  have dC : ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cw'.sub_right (Offset.sub_base W (show 0 + 128 ≤ 2560 by decide) |> fun h => by simpa using h)
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact hCD
    · exact L.kc.symm
  have dS0 : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_st (a := 0) (n := 16) (d := 32) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have dT0 : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [hm₅, blockAt_frame hf.frame dT0, blockAt_frame ho'.frame dS0]
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [hm₅, hf.hH]
  refine WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.tag_ok v L ho he₅ hH₅ hR₅ hJ₅)) fun s₆ ⟨ht, hrd₆, hwr₆⟩ =>
    ⟨ht.env, (VG.Proof.AesGcm.X86_64.wFrame_cons g₅).trans (VG.Proof.AesGcm.X86_64.tagFrame_one ht.frame), by rw [hrd₆, hrd₅, hrd₄, hrd₃, hrd₂, hrd₁],
      by rw [hwr₆, hwr₅, hwr₄, hwr₃, hwr₂, hwr₁], ?_, ht.j, fun hab => ?_⟩
  · have d48 : ∀ r ∈ VG.Proof.AesGcm.X86_64.tagFrame (W + BitVec.ofNat 64 16) W SP o,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (by omega)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
    have d48a : ∀ r ∈ VG.Proof.AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.st_st (.inr (by decide)) (by decide) (by decide)
      · exact L.st_st (.inr (by decide)) (by decide) (by decide)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
    have d48t : ∀ r ∈ VG.Proof.AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.st_st (.inr (by decide)) (by decide) (by decide)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
    rw [blockAt_frame ht.frame d48, hm₅, blockAt_frame hf.frame d48t, blockAt_frame ho'.frame d48a]
  have hw := (hf.abs (ho'.abs hab)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [ht.out, VG.Proof.AesGcm.X86_64.ciph_frame f₅ dC hR.2, hbx₅, hbp₅, VG.Proof.AesGcm.X86_64.toNat_ofNat_of_lt hN, BitVec.toNat_ofNat, VG.Proof.AesGcm.X86_64.lensBlock_mod_left,
    hm₅, hw]

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamAad`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The additional data absorbed
into GHASH (`absorb 16`), for any additional data so far of the length
`aad_len` gives modulo 16 (`streamAad_run`), and so for all of them
(`streamAad_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The regions `vg_aes_gcm_stream_aad` writes. -/
abbrev aadFrame (St W SP : Addr) : List Region := [⟨St + BitVec.ofNat 64 16, 32⟩, ⟨W, 2560⟩, below SP 8]

/-- One run, for additional data so far `x` (of `aad_len` bytes modulo 16). -/
theorem streamAad_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .rdx).toNat % 16) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧
      Frame (VG.Proof.AesGcm.X86_64.aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp)) s.mem s'.mem ∧
      (Absorbed s.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) x →
        Absorbed s'.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) (x ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) := by
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ds, d_dw, d_sw, r_s, r_w, k_c, k_d, k_s, k_w, wc, wd, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hD : s.gpr .rcx = D at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .r8).toNat = n at *
  have L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := VG.Proof.AesGcm.X86_64.save_ok s .r9 hW pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rcx),
        .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (s.gpr .rdx)
    rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hD]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg₁, hand, hx]
    · simp [gpr_setReg, gpr_arithFlags, hg₁, hSP]
    all_goals rfl
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have dsv : ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact d_dw.sub_right (Lay.wSub (by decide))
  have hdata : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [hm₂]; exact bytesAt_frame f₁ dsv (by omega)
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, VG.Proof.AesGcm.X86_64.ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)]
  have rdD : Covers [⟨D, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hai : VG.Proof.AesGcm.X86_64.AbsIn Ctx St W SP 16 (ctxH s.mem Ctx) x D n s₂ :=
    ⟨he₂, h12, hbp, hbx, ⟨rdD, by have := (s.gpr .r8).isLt; omega, wd, d_ds, d_dw, k_d⟩, hH⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.absorb_ok v L (yo := 16) (.inr rfl) hai) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hsv₃ : VG.Proof.AesGcm.X86_64.SavedAt s₃.mem W s := (hm₂ ▸ hsv₁).frame ho.frame (VG.Proof.AesGcm.X86_64.saved_absFrame L (.inr rfl))
  obtain ⟨s₄, run₄, hsv, hother, hm₄, hrd₄, hwr₄⟩ := VG.Proof.AesGcm.X86_64.restore_ok s₃ he₃.r15 (VG.Proof.AesGcm.X86_64.covers_left he₃.perm.w) hsv₃
  refine WP.of_runBlock ⟨s₄, run₄, ⟨?_, ?_⟩, ?_, fun ha => ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.rbx, 128) (by simp [saved])
    · exact hsv (.rbp, 136) (by simp [saved])
    · rw [hother .rsp (by simp [saved]), he₃.rsp, hSP]
    · exact hsv (.r12, 144) (by simp [saved])
    · exact hsv (.r13, 152) (by simp [saved])
    · exact hsv (.r14, 160) (by simp [saved])
    · exact hsv (.r15, 168) (by simp [saved])
  · rw [hm₄, hSP, VG.Proof.AesGcm.X86_64.ret_kept ho.frame (fun r hr => ?_), hm₂, VG.Proof.AesGcm.X86_64.ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.X86_64.ret_below SP
  · rw [hm₄]
    refine ((f₁.sub fun r hr => ?_).trans (hm₂ ▸ ho.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · have dS : ∀ r ∈ [VG.Proof.AesGcm.X86_64.savedR W], ∀ d k, d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
      intro r hr d k hk
      simp only [List.mem_singleton] at hr; subst hr
      exact (d_sw.sub_left (Lay.stSub hk)).sub_right (Lay.wSub (by decide))
    have ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH s.mem Ctx) x := by
      rw [hm₂]
      refine ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide)) (bytesAt_frame f₁
        (fun r hr => dS r hr 32 (x.length % 16) (by omega)) (by omega))
    rw [hm₄, ← hdata]
    exact ho.abs ha₂

/-- `vg_aes_gcm_stream_aad`. -/
theorem streamAad_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamAadX86_64.post s s' := by
  have h₀ := VG.Proof.AesGcm.X86_64.streamAad_run v hp (x := List.replicate ((s.gpr .rdx).toNat % 16) 0) (by simp)
  have h := WP.forall_det (P := fun a : List Byte => a.length % 16 = (s.gpr .rdx).toNat % 16)
    (R := fun s' => gprPreserved s s' ∧ Frame (VG.Proof.AesGcm.X86_64.aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp)) s.mem s'.mem)
    (WP.mono h₀ fun _ h => ⟨h.1, h.2.1⟩) fun a ha => WP.mono (VG.Proof.AesGcm.X86_64.streamAad_run v hp ha) fun _ h => h.2.2
  refine WP.mono h fun s' ⟨⟨hg, hf⟩, hq⟩ => ⟨hg, fun ciph iv a hr hl => ?_⟩
  have hp' := hp
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp'
  obtain ⟨-, -, -, -, -, -, d_sw, -, -, -, -, k_s, -, -, -, ws, -⟩ := hp'
  generalize s.gpr .rsi = St at *
  have dS : ∀ d k, (d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ VG.Proof.AesGcm.X86_64.aadFrame St (s.gpr .r9) (s.gpr .rsp),
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact d_sw.sub_left (Lay.stSub (by omega))
    · exact (k_s.sub_right (Lay.stSub (by omega))).symm
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [← hj]; simpa using blockAt_frame hf (dS 0 16 (.inl (by decide)))
  · rw [Proof.Gcm.ghashInput_nil] at ha ⊢
    refine hq a ?_ ha
    rw [hl, VG.Proof.AesGcm.X86_64.toNat_mod16]
  · exact hc.congr (blockAt_frame hf (dS 48 16 (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame hf (dS 64 16 (.inr ⟨by decide, by decide⟩)))

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamAadCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_aad` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
absorb data at the same address, of the same length, after the same number
of bytes modulo 16 (`absorb_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block)

/-- What the entry of `vg_aes_gcm_stream_aad` leaves. -/
theorem streamAadEntry_ok {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) :
    WP isa (.block (save .r9 ++ ([.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
        .mov .r12 (.reg .rcx), .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] : List Instr))) s
      fun s₂ => ∃ H, VG.Proof.AesGcm.X86_64.AbsIn (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) 16 H
        (List.replicate ((s.gpr .rdx).toNat % 16) 0) (s.gpr .rcx) (s.gpr .r8).toNat s₂ := by
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, -, -, d_ds, d_dw, -, -, -, -, k_d, -, -, -, wd, -, -⟩ := hp
  have pW : Covers [⟨s.gpr .r9, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := VG.Proof.AesGcm.X86_64.save_ok s .r9 rfl pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rcx),
        .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .r9 ∧ s₂.gpr .r14 = s.gpr .rsi ∧ s₂.gpr .r13 = s.gpr .rdi ∧ s₂.gpr .r12 = s.gpr .rcx ∧
      s₂.gpr .rbp = BitVec.ofNat 64 (s.gpr .r8).toNat ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((List.replicate ((s.gpr .rdx).toNat % 16) (0 : Byte)).length % 16) ∧
      s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hand := VG.Proof.AesGcm.X86_64.and15 (s.gpr .rdx)
    rw [VG.Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg₁, hand, List.length_replicate, Nat.mod_mod]
    · simp [gpr_setReg, hg₁]
    all_goals rfl
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, _, ⟨h13, h14, h15, hg₂, ?_⟩,
    h12, hbp, hbx, ⟨?_, by have := (s.gpr .r8).isLt; omega, wd, d_ds, d_dw, k_d⟩, rfl⟩⟩)
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
    · exact pW
  · rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem streamAad_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamAadX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamAadX86_64.pre s₀') (hq : Proof.AesGcm.streamAadX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamAad v.callees) fun _ _ => True := by
  have L : VG.Proof.AesGcm.X86_64.Lay (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp) := by
    simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
    obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, k_c, -, k_s, k_w, wc, -, ws, ww⟩ := hp
    exact Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have hE₂ := VG.Proof.AesGcm.X86_64.streamAadEntry_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇] at hE₂
  refine VG.Proof.AesGcm.X86_64.fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := s₀.gpr .r9) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    ⟨_, by taint_decide⟩ (VG.Proof.AesGcm.X86_64.streamAadEntry_ok hp) hE₂ ?_
  have a := RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
    VG.Proof.AesGcm.X86_64.absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := List.replicate ((s₀.gpr .rdx).toNat % 16) 0)
      (x₂ := List.replicate ((s₀.gpr .rdx).toNat % 16) 0) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat) rfl
  have hw : ∀ s, (∃ H, VG.Proof.AesGcm.X86_64.AbsIn (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp) 16 H
      (List.replicate ((s₀.gpr .rdx).toNat % 16) 0) (s₀.gpr .rcx) (s₀.gpr .r8).toNat s) →
      WP isa (absorb v.callees 16) s (VG.Proof.AesGcm.X86_64.Env (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp)) :=
    fun s ⟨_, h⟩ => WP.mono (VG.Proof.AesGcm.X86_64.absorb_ok v L (.inr rfl) h) fun _ o => o.env
  exact (VG.Proof.AesGcm.X86_64.rel_wp a (fun _ _ ⟨H₁, H₂, h₁, h₂⟩ => ⟨⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩) hw hw).mono
    (fun _ _ ⟨_, ⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩ => ⟨H₁, H₂, h₁, h₂⟩) fun _ _ h => h.2

theorem streamAad_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamAadX86_64.pre Proof.AesGcm.streamAadX86_64.pub (streamAad v.callees) :=
  VG.Proof.AesGcm.X86_64.ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.streamAad_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinishCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
compute the tag from the same lengths and number of rounds (`finTag_rel`),
and copy it to the same address, kept in `W` (`finishEntry_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

theorem fin_lay {s : State} (hp : Proof.AesGcm.finPre s) :
    VG.Proof.AesGcm.X86_64.Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) (s.gpr .rsp) ∧ VG.Proof.AesGcm.X86_64.Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) s ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) := by
  simp only [Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, -, -, -, -, -, k_c, k_s, -, k_w, wc, ws, -, ww, hR⟩ := hp
  exact ⟨Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w,
    ⟨by rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩,
    by rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Region.contains_self _ _⟩, hR⟩

theorem finishEntry_fin {s : State} (hp : Proof.AesGcm.finPre s) :
    WP isa (.block (finEntry 8 ++ ([.store (at_ .r15 tagPO) .r9] : List Instr))) s fun s' =>
      VG.Proof.AesGcm.X86_64.FinS (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) s' ∧
        s'.mem.readW (stackArg s 0 + BitVec.ofNat 64 200) 64 = s.gpr .r9 := by
  obtain ⟨L, hperm, ha, hR⟩ := VG.Proof.AesGcm.X86_64.fin_lay hp
  exact WP.mono (VG.Proof.AesGcm.X86_64.finishEntry_ok L rfl rfl rfl rfl rfl ha hperm hR) fun _ ⟨e, h⟩ =>
    ⟨⟨e.env, e.rounds, e.alen, e.tlen⟩, h⟩

theorem streamFinish_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamFinishX86_64.pre s₀') (hq : Proof.AesGcm.streamFinishX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamFinish v.callees) fun _ _ => True := by
  obtain ⟨L, -, ha₁, -⟩ := VG.Proof.AesGcm.X86_64.fin_lay hp
  obtain ⟨-, -, ha₂, -⟩ := VG.Proof.AesGcm.X86_64.fin_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq
  simp only [Proof.AesGcm.arg] at q₈
  have hw8 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 8) 64 :=
    q₈
  have hE₂ := VG.Proof.AesGcm.X86_64.finishEntry_fin hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  have hE₁ := VG.Proof.AesGcm.X86_64.finishEntry_fin hp
  rw [finEntry, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [streamFinish, finEntry, List.append_assoc, List.append_assoc]
  refine VG.Proof.AesGcm.X86_64.fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 0) (SP := s₀.gpr .rsp) (k := 8)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw8 ha₁ ha₂ ⟨_, by taint_decide⟩ hE₁ hE₂ ?_
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rdx = St at *
  generalize stackArg s₀ 0 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r9 = T at *
  have hw : ∀ s, VG.Proof.AesGcm.X86_64.FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) s ∧
      s.mem.readW (W + BitVec.ofNat 64 200) 64 = T → WP isa (finTag v.callees 0) s fun s' =>
        VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 200) 64 = T :=
    fun s h => WP.mono (VG.Proof.AesGcm.X86_64.finTag_ok v L (.inl rfl) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
      (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
      (by simp)) fun _ ⟨he, _, f, _⟩ => ⟨he, by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w (by decide)).symm) (by decide), h.2]⟩
  have a := VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.finTag_rel v L (R := (s₀.gpr .rsi).toNat) (aL := s₀.gpr .rcx) (tL := s₀.gpr .r8) (.inl rfl)).mono
      (P' := fun (s₁ s₂ : State) => True ∧ (VG.Proof.AesGcm.X86_64.FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = T) ∧ (VG.Proof.AesGcm.X86_64.FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx)
          (s₀.gpr .r8) s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T))
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2) hw hw
  -- The address of `tag`, loaded from `W + 200`, is the same in both runs.
  have tg : ∀ s, VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = T →
      VG.Proof.AesGcm.X86_64.TagAt Ctx St W SP .r15 200 T s := fun s ⟨he, hT⟩ =>
    ⟨he, by rw [he.r15]; exact hT, by rw [he.r15]; exact he.perm.wR (show 200 + 8 ≤ 2560 by decide)⟩
  exact RelCT.seq a ((VG.Proof.AesGcm.X86_64.tagOut_rel (b := .r15) (d := 200) (by simp) ⟨_, by taint_decide⟩
    (fun _ _ h => ⟨tg _ h.2.1, tg _ h.2.2⟩)).mono (fun _ _ h => h) fun _ _ h => h)

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamFinishX86_64.pre Proof.AesGcm.streamFinishX86_64.pub
      (streamFinish v.callees) :=
  VG.Proof.AesGcm.X86_64.ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.streamFinish_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamInit`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `J₀`, the accumulator and the
first counter block, from `j0` (`streamInit_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

/-- `vg_aes_gcm_stream_init`. -/
theorem streamInit_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamInitX86_64.pre s) :
    WP isa (streamInit v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamInitX86_64.post s s' := by
  simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp ⊢
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ns, d_nw, d_sw, r_s, r_w, k_c, k_n, k_s, k_w, wc, wn, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hSt : s.gpr .rcx = St at *
  generalize hW : s.gpr .r8 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .rdx).toNat = n at *
  have L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := VG.Proof.AesGcm.X86_64.save_ok s .r8 hW pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi),
        .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = Np ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hNp]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp [gpr_setReg, hg₁, hSP]
    all_goals rfl
  have he₂ : VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have rdN : Covers [⟨Np, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hiv : bytesAt s₂.mem Np n = bytesAt s.mem Np n := by
    rw [hm₂]; exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_nw.sub_right (Lay.wSub (by decide))) (by omega)
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, VG.Proof.AesGcm.X86_64.ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)]
  have hji : VG.Proof.AesGcm.X86_64.J0In Ctx St W SP (ctxH s.mem Ctx) Np n s₂ :=
    ⟨he₂, hH, h12, hbp, ⟨rdN, by have := (s.gpr .rdx).isLt; omega, wn, d_ns, d_nw, k_n⟩⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.j0_ok v L hji) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hret : s₃.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [VG.Proof.AesGcm.X86_64.ret_kept ho.frame (fun r hr => ?_), hm₂, VG.Proof.AesGcm.X86_64.ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact r_s
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.X86_64.ret_below SP
  refine WP.mono (VG.Proof.AesGcm.X86_64.exit_ok he₃.r15 (by rw [he₃.rsp, hSP]) (VG.Proof.AesGcm.X86_64.covers_left he₃.perm.w)
    ((hm₂ ▸ hsv₁).frame ho.frame (VG.Proof.AesGcm.X86_64.saved_j0Frame L)) (by rw [hSP, hret])) fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ciph => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, VG.Proof.AesGcm.X86_64.ofNat_lit, hm, ← hiv]
  refine ⟨ho.j0, Proof.Gcm.absorbed_nil _ ho.y, ho.cb, fun h => absurd rfl h⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamInitCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_init` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
compute `J₀` of nonces at the same address, of the same length (`j0_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block)

/-- What the entry of `vg_aes_gcm_stream_init` leaves. -/
theorem streamInitEntry_ok {s : State} (hp : Proof.AesGcm.streamInitX86_64.pre s) :
    WP isa (.block (save .r8 ++ ([.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi),
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] : List Instr))) s
      fun s₂ => ∃ H, VG.Proof.AesGcm.X86_64.J0In (s.gpr .rdi) (s.gpr .rcx) (s.gpr .r8) (s.gpr .rsp) H (s.gpr .rsi) (s.gpr .rdx).toNat s₂ := by
  simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, -, -, d_ns, d_nw, -, -, -, -, k_n, -, -, -, wn, -, -⟩ := hp
  have pW : Covers [⟨s.gpr .r8, 2560⟩] s.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := VG.Proof.AesGcm.X86_64.save_ok s .r8 rfl pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi),
        .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .r8 ∧ s₂.gpr .r14 = s.gpr .rcx ∧ s₂.gpr .r13 = s.gpr .rdi ∧ s₂.gpr .r12 = s.gpr .rsi ∧
      s₂.gpr .rbp = BitVec.ofNat 64 (s.gpr .rdx).toNat ∧ s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    all_goals rfl
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, _, ⟨h13, h14, h15, hg₂, ?_⟩,
    rfl, h12, hbp, ⟨?_, by have := (s.gpr .rdx).isLt; omega, wn, d_ns, d_nw, k_n⟩⟩⟩)
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_cons_self ..)
    · exact pW
  · rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact VG.Proof.AesGcm.X86_64.covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem streamInit_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamInitX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamInitX86_64.pre s₀') (hq : Proof.AesGcm.streamInitX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamInit v.callees) fun _ _ => True := by
  have L : VG.Proof.AesGcm.X86_64.Lay (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp) := by
    simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
    obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, k_c, -, k_s, k_w, wc, -, ws, ww⟩ := hp
    exact Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  have hE₂ := VG.Proof.AesGcm.X86_64.streamInitEntry_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆] at hE₂
  refine VG.Proof.AesGcm.X86_64.fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rcx) (W := s₀.gpr .r8) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    ⟨_, by taint_decide⟩ (VG.Proof.AesGcm.X86_64.streamInitEntry_ok hp) hE₂ ?_
  have a := RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
    VG.Proof.AesGcm.X86_64.j0_rel v L (H₁ := H₁) (H₂ := H₂) (Np := s₀.gpr .rsi) (n := (s₀.gpr .rdx).toNat)
  have hw : ∀ s, (∃ H, VG.Proof.AesGcm.X86_64.J0In (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp) H (s₀.gpr .rsi)
      (s₀.gpr .rdx).toNat s) →
      WP isa (j0 v.callees) s (VG.Proof.AesGcm.X86_64.Env (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp)) :=
    fun s ⟨_, h⟩ => WP.mono (VG.Proof.AesGcm.X86_64.j0_ok v L h) fun _ o => o.env
  exact (VG.Proof.AesGcm.X86_64.rel_wp a (fun _ _ ⟨H₁, H₂, h₁, h₂⟩ => ⟨⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩) hw hw).mono
    (fun _ _ ⟨_, ⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩ => ⟨H₁, H₂, h₁, h₂⟩) fun _ _ h => h.2

theorem streamInit_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamInitX86_64.pre Proof.AesGcm.streamInitX86_64.pub (streamInit v.callees) :=
  VG.Proof.AesGcm.X86_64.ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.streamInit_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. The only branch is on the
tag length (`tagLenOk`, checked by the taint analysis); the received tag is
read from the same address (`r9`), the tag is computed from the same lengths
and number of rounds (`finTag_rel`), and the comparison has no branch.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- The lengths and rounds kept, and the tag length at `W + 224`. -/
def VerS (Ctx St W SP : Addr) (R : Nat) (aL tL tl : BitVec 64) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.FinS Ctx St W SP R aL tL s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : VG.Proof.AesGcm.X86_64.Lay Ctx St W SP)
include L

/-- What `verify` has before checking a received tag of length `t` at `Tp`. -/
def VerT (R : Nat) (aL tL : BitVec 64) (t : Nat) (Tp : Addr) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧ s.gpr .rsi = Tp ∧
    Covers [⟨Tp, t⟩] (s.rd ++ s.wr)

omit L in
theorem VerT.keep {R : Nat} {aL tL : BitVec 64} {t : Nat} {Tp : Addr} {s s' : State}
    (h : VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s) (k : VG.Proof.AesGcm.X86_64.Keeps s s') :
    VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s' :=
  ⟨⟨h.1.1.keep (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) k.mem k.rd k.wr, by rw [k.mem]; exact h.1.2⟩,
    by rw [k.gpr _ (by decide), h.2.1], by rw [k.gpr _ (by decide), h.2.2.1], by rw [k.rd, k.wr]; exact h.2.2.2⟩

/-- The tag computed and compared, for an allowed length `t`. -/
theorem verifyCheck_rel {R t : Nat} (h1 : 1 ≤ t) (h16 : t ≤ 16) {aL tL : BitVec 64} {Tp : Addr}
    (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₁ ∧
        VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₂)
      (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0))))
      fun _ _ => True := by
  -- `recv` keeps the lengths.
  have hR : ∀ s, VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s →
      WP isa recv s (VG.Proof.AesGcm.X86_64.VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t)) := fun s ⟨⟨h, ht⟩, hbx, hsi, hTr⟩ =>
    WP.mono (VG.Proof.AesGcm.X86_64.recv_ok h.1 hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide)))) fun s' ⟨he', _, f, _⟩ => by
      have d : ∀ d, 176 ≤ d → d + 8 ≤ 256 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide)
      exact ⟨⟨he', VG.Proof.AesGcm.X86_64.rounds_frame f (d 176 (by decide) (by decide)) h.2.1,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 184 (by decide) (by decide)) (by decide), h.2.2.1],
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 192 (by decide) (by decide)) (by decide), h.2.2.2]⟩,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 224 (by decide) (by decide)) (by decide), ht]⟩
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₁ ∧
      VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₂) ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.1.1.1.1, h.2.1.1.1, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hR hR
  -- `finTag` keeps the tag length.
  have hT : ∀ s, VG.Proof.AesGcm.X86_64.VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s → WP isa (finTag v.callees 0) s fun s' =>
      VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := fun s ⟨h, ht⟩ =>
    WP.mono (VG.Proof.AesGcm.X86_64.finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2.1 h.2.2.2
      (x := List.replicate ((if tL = 0 then aL.toNat else tL.toNat) % 16) 0) (by simp)) fun _ ⟨he', _, f, _⟩ =>
      ⟨he', by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.st_w (a := 0) (n := 32) (d := 224) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · simpa using L.w_w (a := 224) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w (by decide)).symm) (by decide), ht]⟩
  have b := VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.finTag_rel v L (R := R) (aL := aL) (tL := tL) (.inl rfl)).mono
      (P' := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₁ ∧
        VG.Proof.AesGcm.X86_64.VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₂) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hT hT
  -- The tag length, and the comparison.
  have hL : ∀ s, (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) →
      WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO))]) s fun s' => VG.Proof.AesGcm.X86_64.Env Ctx St W SP s' ∧
        s'.gpr .rbx = BitVec.ofNat 64 t := fun s ⟨he, ht⟩ => by
    have r₁ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hbx, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s = some s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [he.r15, r₁], ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, ht]
      · intro r a; simp [gpr_setReg, a]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => ?_) hrd hwr, hbx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)
  have c := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧ (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧
      s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => VG.Proof.AesGcm.X86_64.env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hL hL
  have d := VG.Proof.AesGcm.X86_64.rel_taint (P := fun s₁ s₂ => True ∧ (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (VG.Proof.AesGcm.X86_64.Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t)) (c := cmp 0) ([.rbx] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c d))

end

theorem streamVerify_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamVerifyX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamVerifyX86_64.pre s₀') (hq : Proof.AesGcm.streamVerifyX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamVerify v.callees) fun _ _ => True := by
  obtain ⟨L, hperm, ha, hta, dA, hTr, dTW, -, -, -, hR⟩ := VG.Proof.AesGcm.X86_64.ver_lay hp
  obtain ⟨L', hperm', ha', hta', dA', hTr', -, -, -, -, hR'⟩ := VG.Proof.AesGcm.X86_64.ver_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq
  simp only [Proof.AesGcm.arg] at q₈ q₉
  have hw16 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 64 := q₉
  -- What the entry leaves in each run.
  let I : State → State → Prop := fun s₀ s => VG.Proof.AesGcm.X86_64.VerS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
      (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (stackArg s₀ 0) s ∧ s.gpr .rbx = stackArg s₀ 0 ∧
    s.gpr .rsi = s₀.gpr .r9 ∧ Covers [⟨s₀.gpr .r9, (stackArg s₀ 0).toNat⟩] (s.rd ++ s.wr)
  have hE : ∀ {s : State}, VG.Proof.AesGcm.X86_64.Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) →
      VG.Proof.AesGcm.X86_64.Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) s → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 →
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 →
      (⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ →
      Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] (s.rd ++ s.wr) →
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) →
      WP isa (.block (finEntry 16 ++ ([.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx,
        .mov .rsi (.reg .r9)] : List Instr))) s (I s) := fun L hperm ha hta dA hTr hR =>
    WP.mono (VG.Proof.AesGcm.X86_64.verifyEntry_ok L rfl rfl rfl rfl ha hta dA hperm hR) fun _ e =>
      ⟨⟨⟨e.env, e.rounds, e.alen, e.tlen⟩, e.tl⟩, e.rbx, e.rsi, by rw [e.rd, e.wr]; exact hTr⟩
  have hE₁ := hE L hperm ha hta dA hTr hR
  have hE₂ := hE L' hperm' ha' hta' dA' hTr' hR'
  simp only [I] at hE₁ hE₂
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  rw [finEntry, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [streamVerify, finEntry, List.append_assoc, List.append_assoc]
  refine VG.Proof.AesGcm.X86_64.rel_reassoc_inner (VG.Proof.AesGcm.X86_64.fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1)
    (SP := s₀.gpr .rsp) (k := 16) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw16 ha ha' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rdx = St at *
  generalize stackArg s₀ 1 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r9 = Tp at *
  generalize (s₀.gpr .rsi).toNat = R at *
  generalize htl : stackArg s₀ 0 = tl at *
  generalize ht : tl.toNat = t at *
  have htl' : tl = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst htl'
  -- The tag length.
  let A : State → Prop := fun s => VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s ∧
    s.zf = some (!Spec.Gcm.tagLenOk t)
  have hK : ∀ s, VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s →
      WP isa tagLenOk s A := fun s h =>
    WP.mono (VG.Proof.AesGcm.X86_64.tagLenOk_ok s h.2.1 (by rw [← ht]; exact (BitVec.ofNat 64 t).isLt)) fun s' ⟨hz, k⟩ => ⟨h.keep k, hz⟩
  have a := VG.Proof.AesGcm.X86_64.rel_wp (VG.Proof.AesGcm.X86_64.rel_regs (P := fun s₁ s₂ => True ∧
      VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s₁ ∧
      VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s₂)
      ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.1.1, h.2.2.1.1.1,
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hK hK
  refine RelCT.seq a (VG.Proof.AesGcm.X86_64.rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length §5.2.1.2 does not allow (`rax` is 0).
    exact (VG.Proof.AesGcm.X86_64.rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.1.1, h.1.2.2.1.1.1.1⟩)
      (VG.Proof.AesGcm.X86_64.rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => VG.Proof.AesGcm.X86_64.env_agree h.1.2.1.1.1.1.1 h.1.2.2.1.1.1.1)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega
    have hc : ∀ s, VG.Proof.AesGcm.X86_64.VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s →
        WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
          (VG.Proof.AesGcm.X86_64.Env Ctx St W SP) := fun s ⟨⟨h, hm⟩, hbx, hsi, hTr⟩ =>
      WP.mono (VG.Proof.AesGcm.X86_64.verifyCheck_ok v L h.1 h.2.1 h.2.2.1 h.2.2.2 hm hbx hb.1 hb.2 hsi hTr dTW
        (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
        (by simp)) fun _ h => h.1
    exact (VG.Proof.AesGcm.X86_64.rel_wp ((VG.Proof.AesGcm.X86_64.verifyCheck_rel v L hb.1 hb.2 dTW).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) hc hc).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamVerifyX86_64.pre Proof.AesGcm.streamVerifyX86_64.pub
      (streamVerify v.callees) :=
  VG.Proof.AesGcm.X86_64.ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.streamVerify_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end
