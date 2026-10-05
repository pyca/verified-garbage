import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Dbl32

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Env`. -/
section

/-!
# AES-GCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`), the working space (2560
bytes at `W`) and the `K` bytes of stack below `SP` used by the calls
(`Lay`): the state is disjoint from the parts of `W` other than `[16, 96)`
(where `seal` and `open` keep it), and the context from both. `Env` says
which registers hold `W`, the state and `SP`, that the context may be read
and the state and `W` written, and that `W + ctxO` holds `Ctx`. `xrun`
runs a straight-line block symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)

/-! ## Covering regions -/

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
  VG.Proof.AesGcm.X86.covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => VG.Proof.AesGcm.X86.in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_one {r : Region} {ts : List Region} (h : Covers [r] ts) : Covers [r] ts := h

/-! ## The layout -/

/-- The regions: the context, the state and `W`, and the `K` bytes of stack
below `SP` that the calls use (24 for `vg_ghash`, 28 for `vg_aes_ctr32`). -/
structure Lay (Ctx St W SP : BitVec 32) (K : Nat) : Prop where
  fc : Ctx.toNat + 256 ≤ 2 ^ 32
  fs : St.toNat + 80 ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32
  k24 : 24 ≤ K
  k28 : K ≤ 28
  sp : K ≤ SP.toNat
  cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩
  cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩
  sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩
  kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩
  ks : (below SP K).Disjoint ⟨w64 St, 80⟩
  kw : (below SP K).Disjoint ⟨w64 W, 2560⟩

/-- The registers holding `W`, the state and the stack pointer, what may be
accessed, and the context kept at `W + ctxO`. -/
structure Env (Ctx St W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx

namespace Lay

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

variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
include L

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (VG.Proof.AesGcm.X86.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.X86.Lay.aSub hd)
  · exact (L.sb.sub_left (VG.Proof.AesGcm.X86.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.X86.Lay.bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (VG.Proof.AesGcm.X86.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.X86.Lay.stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw.sub_left (VG.Proof.AesGcm.X86.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.X86.Lay.wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP K).Disjoint ⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (VG.Proof.AesGcm.X86.Lay.ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP K).Disjoint ⟨w64 St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (VG.Proof.AesGcm.X86.Lay.stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (VG.Proof.AesGcm.X86.Lay.wSub ha)

omit L in
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- The stack the calls use, at `esp = SP`. -/
theorem below_sub {k : Nat} (hk : k ≤ K) : Region.Sub (below SP k) (below SP K) :=
  VG.X86.below_sub hk L.sp

/-! ### Pointers into the regions, as the code computes them -/

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega)

theorem aS {o : Nat} (ho : o < 80) : w64 (St + BitVec.ofNat 32 o) = w64 St + BitVec.ofNat 64 o :=
  w64_add (by have := L.fs; omega)

theorem aC {o : Nat} (ho : o < 256) : w64 (Ctx + BitVec.ofNat 32 o) = w64 Ctx + BitVec.ofNat 64 o :=
  w64_add (by have := L.fc; omega)

theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega)

theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o :=
  toNat_add32 (by have := L.fs; omega)

theorem nC {o : Nat} (ho : o < 256) : (Ctx + BitVec.ofNat 32 o).toNat = Ctx.toNat + o :=
  toNat_add32 (by have := L.fc; omega)

end Lay

namespace Env

variable {Ctx St W SP : BitVec 32} {s : State} (E : VG.Proof.AesGcm.X86.Env Ctx St W SP s)
include E

theorem ctxIn {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (w64 Ctx + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86.in_off E.ctxR h (by decide)

theorem stIn {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (w64 St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86.in_off E.stW h (by decide)

theorem stIn' {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (w64 St + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86.in_left (E.stIn h)

theorem wIn {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86.in_off E.wW h (by decide)

theorem wIn' {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.X86.in_left (E.wIn h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨w64 Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.AesGcm.X86.covers_off E.ctxR h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨w64 St + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.X86.covers_off E.stW h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.X86.covers_off E.wW h (by decide)

end Env

/-- An environment, after code that keeps `ebp`, `esi`, `esp`, the
permissions and the context's slot. -/
theorem Env.keep {Ctx St W SP : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.X86.Env Ctx St W SP s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32) :
    VG.Proof.AesGcm.X86.Env Ctx St W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsi, h.esi], by rw [hsp, h.esp], by rw [hrd, hwr]; exact h.ctxR,
    by rw [hwr]; exact h.stW, by rw [hwr]; exact h.wW, by rw [hc, h.ctx]⟩

/-- The context's slot outside a frame that does not touch it. -/
theorem slot_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32} {o : Nat}
    (hd : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r) :
    m'.readW (w64 W + BitVec.ofNat 64 o) 32 = m.readW (w64 W + BitVec.ofNat 64 o) 32 :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) hd (by decide)

/-! ## Words written at offsets -/

/-- A word at `p + a`, after a word written at `p + b` elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {a b : Nat} (h : a + 4 ≤ b ∨ b + 4 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- A word at `p + a`, after a byte written at `q` elsewhere. -/
theorem readW_writeB_sep (m : Mem) {p q : Addr} (v : BitVec 8) (h : Mem.Sep p 4 q 1) :
    (m.writeW q v).readW p 32 = m.readW p 32 :=
  Mem.readW_writeW_sep h (by decide)

/-! ## Arithmetic -/

theorem ofNat_add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem sub_beq32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := VG.X86.Wp.sub_beq ha hb

theorem and_self_beq32 {a : Nat} (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 a &&& BitVec.ofNat 32 a == 0) = decide (a = 0) := by
  rw [BitVec.and_self]
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat32 ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem and15 (x : BitVec 32) : x &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 4 = BitVec.ofNat 32 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- `16 k`, by four doublings. -/
theorem times16 (x : BitVec 32) :
    x + x + (x + x) + (x + x + (x + x)) + (x + x + (x + x) + (x + x + (x + x))) =
      BitVec.ofNat 32 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `CF` after `a - b`, as natural numbers. -/
theorem lt_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) = (a < b) := by
  rw [toNat_ofNat32 ha, toNat_ofNat32 hb]

/-! ## Running a block -/

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind (runBlock isa (is ++ b)) =
      ((isa.exec i s).bind (runBlock isa is)).bind (runBlock isa b)
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

theorem runBlock_app_of {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.AesGcm.X86.runBlock_app, h₁]; exact h₂

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Gcm.blocksAt m p 1 = [Spec.Gcm.blockAt m p] := by
  simp [Spec.Gcm.blocksAt]


/-- A state with its memory replaced, kept folded (as `State.setReg` is) so
that a store does not copy the state into every field of a structure. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (VG.Proof.AesGcm.X86.setMem s (s.mem.writeW a v)) else none := rfl

theorem store8_eq (s : State) (a : Addr) (v : Byte) :
    s.store8 a v = if InRegions s.wr a 1 then some (VG.Proof.AesGcm.X86.setMem s (s.mem.writeW a v)) else none := rfl

theorem gpr_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).gpr = s.gpr := rfl
theorem mem_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).mem = m := rfl
theorem rd_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).rd = s.rd := rfl
theorem wr_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).wr = s.wr := rfl
theorem cf_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).cf = s.cf := rfl
theorem zf_setMem (s : State) (m : Mem) : (VG.Proof.AesGcm.X86.setMem s m).zf = s.zf := rfl

/-- Runs a block of the instructions the AES-GCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "xrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, stO, tO, uO, ctxO, roundsO, alO, ahO, xlO, xhO, dataO, lenO, aadO, tglO,
    auxO, zO, nlO, vO, rO, tpO, dO, nO, bO, scrO, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
    eq_self_iff_true, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "regs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := decide) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "mems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, stO, tO, uO,
    ctxO, roundsO, alO, ahO, xlO, xhO, dataO, lenO, aadO, tglO, auxO, zO, nlO, vO, rO, tpO, dO, nO, bO, scrO,
    Nat.reduceAdd, $ts,*]))

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Loops`. -/
section

/-!
# AES-GCM on x86: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `ecx` bytes
from `edi` to `edx`, and `xorLoop` XORs the `ecx` bytes at `edx` into those
at `edi`, a byte at a time, advancing both pointers (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap. Both are constant time from the
pointers and the count (`copyLoop_ct`, `xorLoop_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: the source `S` (`edi`), the
destination `D` (`edx`) and the count `n` (`ecx`). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edi : s.gpr .edi = S
  edx : s.gpr .edx = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem succ_ofNat32 (x : BitVec 32) (i : Nat) :
    x + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = x + BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_zero32 (x : BitVec 32) : x + BitVec.ofNat 32 0 = x := BitVec.add_zero x

theorem pred_count {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [VG.Proof.AesGcm.X86.ofNat_sub32 (by omega) (by omega)]; congr 1

theorem pred_beq {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = decide (i + 1 = n) := by
  rw [VG.Proof.AesGcm.X86.pred_count h hn, VG.X86.Wp.ofNat_beq_zero (by omega)]
  simp only [decide_eq_decide]
  omega

theorem setWidth8_32 (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext j hj; simp [hj]

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .store8 (at_ .edx 0) .al, .alu .add .edi (imm 1),
    .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .edi = S + BitVec.ofNat 32 i)
    (hd : s.gpr .edx = D + BitVec.ofNat 32 i) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eS : w64 (S + BitVec.ofNat 32 i) = w64 S + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.X86.copyBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i) (s.mem (w64 S + BitVec.ofNat 64 i)) ∧
      s'.gpr .edi = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edx = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [VG.Proof.AesGcm.X86.copyBody, VG.Proof.AesGcm.X86.add_zero32, hs, hd, eS, eD, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, ite_true, VG.Proof.AesGcm.X86.setWidth8_32]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, VG.Proof.AesGcm.X86.succ_ofNat32]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, VG.Proof.AesGcm.X86.succ_ofNat32]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [VG.Proof.AesGcm.X86.zf_setMem, VG.Proof.AesGcm.X86.gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · intro r h₁ h₂ h₃ h₄; simp [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 32) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

/-- What `copyLoop` leaves. -/
structure CopyPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n)
  edi : s'.gpr .edi = S + BitVec.ofNat 32 n
  edx : s'.gpr .edx = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.X86.LoopPre s S D n) :
    WP isa copyLoop s (VG.Proof.AesGcm.X86.CopyPost s S D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.X86.copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edi = S + BitVec.ofNat 32 i ∧
      t.gpr .edx = D + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) i) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr)
    ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edi, VG.Proof.AesGcm.X86.add_zero32], by rw [h.edx, VG.Proof.AesGcm.X86.add_zero32], by rw [h.ecx, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edi, edx, ecx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', edi', edx', ecx', zf', g', rd', wr'⟩ := VG.Proof.AesGcm.X86.copyStep_ok t edi edx ecx
    (w64_add (by have := h.fS; omega)) (w64_add (by have := h.fD; omega))
    (by rw [rd, wr]; exact VG.Proof.AesGcm.X86.in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact VG.Proof.AesGcm.X86.in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (w64 S) i).length = i := VG.Proof.AesGcm.X86.length_bytesAt _ _ _
  have hmem : t'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcm.X86.src_kept h.disj hi hn _ hlen, VG.Proof.AesGcm.X86.bytesAt_succ,
      writeBytes_snoc s.mem (w64 D) (bytesAt s.mem (w64 S) i) _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', VG.Proof.AesGcm.X86.pred_beq hi hn]
  have gg : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edi', he], by rw [edx', he], gg,
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edi', edx',
      by rw [ecx', VG.Proof.AesGcm.X86.pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.movzx8 .eax (at_ .edx 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .eax (.reg .ebx),
    .store8 (at_ .edi 0) .al, .alu .add .edi (imm 1), .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp [hj]

theorem xorStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .edx = S + BitVec.ofNat 32 i)
    (hd : s.gpr .edi = D + BitVec.ofNat 32 i) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eS : w64 (S + BitVec.ofNat 32 i) = w64 S + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1)
    (w' : InRegions (s.rd ++ s.wr) (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.X86.xorBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i)
        (s.mem (w64 S + BitVec.ofNat 64 i) ^^^ s.mem (w64 D + BitVec.ofNat 64 i)) ∧
      s'.gpr .edx = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edi = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [VG.Proof.AesGcm.X86.xorBody, VG.Proof.AesGcm.X86.add_zero32, hs, hd, eS, eD, r, w, w'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, VG.Proof.AesGcm.X86.setWidth8_xor]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, VG.Proof.AesGcm.X86.succ_ofNat32]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, VG.Proof.AesGcm.X86.succ_ofNat32]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [VG.Proof.AesGcm.X86.zf_setMem, VG.Proof.AesGcm.X86.gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · intro r h₁ h₂ h₃ h₄ h₅; simp [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄, h₅]
  all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    VG.Proof.AesGcm.X86.xorBytes m D S (i + 1) = VG.Proof.AesGcm.X86.xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [VG.Proof.AesGcm.X86.xorBytes, VG.Proof.AesGcm.X86.bytesAt_succ, List.zipWith_append, VG.Proof.AesGcm.X86.length_bytesAt]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (VG.Proof.AesGcm.X86.xorBytes m D S n).length = n := by
  simp [VG.Proof.AesGcm.X86.xorBytes, VG.Proof.AesGcm.X86.length_bytesAt]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

/-- What `xorLoop` (source `S` in `edx`, destination `D` in `edi`) leaves. -/
structure XorPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (VG.Proof.AesGcm.X86.xorBytes s.mem (w64 D) (w64 S) n)
  edx : s'.gpr .edx = S + BitVec.ofNat 32 n
  edi : s'.gpr .edi = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What `xorLoop` needs: the source `S` in `edx`, the destination `D` in `edi`. -/
structure XorPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edx : s.gpr .edx = S
  edi : s.gpr .edi = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.X86.XorPre s S D n) :
    WP isa xorLoop s (VG.Proof.AesGcm.X86.XorPost s S D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.X86.xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edx = S + BitVec.ofNat 32 i ∧
      t.gpr .edi = D + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (VG.Proof.AesGcm.X86.xorBytes s.mem (w64 D) (w64 S) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edx, VG.Proof.AesGcm.X86.add_zero32], by rw [h.edi, VG.Proof.AesGcm.X86.add_zero32], by rw [h.ecx, Nat.sub_zero],
      by simp [VG.Proof.AesGcm.X86.xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edx, edi, ecx, mem, g, rd, wr⟩
  have wD : InRegions t.wr (w64 D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact VG.Proof.AesGcm.X86.in_of_covers h.wr hi (by omega)
  obtain ⟨t', run', mem', edx', edi', ecx', zf', g', rd', wr'⟩ := VG.Proof.AesGcm.X86.xorStep_ok t edx edi ecx
    (w64_add (by have := h.fS; omega)) (w64_add (by have := h.fD; omega))
    (by rw [rd, wr]; exact VG.Proof.AesGcm.X86.in_of_covers h.rd hi (by omega)) wD (VG.Proof.AesGcm.X86.in_left wD)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := VG.Proof.AesGcm.X86.length_xorBytes s.mem (w64 D) (w64 S) i
  have hmem : t'.mem = writeBytes s.mem (w64 D) (VG.Proof.AesGcm.X86.xorBytes s.mem (w64 D) (w64 S) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcm.X86.src_kept h.disj hi hn _ hlen, VG.Proof.AesGcm.X86.dst_kept hi hn _ hlen, VG.Proof.AesGcm.X86.xorBytes_succ, BitVec.xor_comm,
      writeBytes_snoc s.mem (w64 D) _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', VG.Proof.AesGcm.X86.pred_beq hi hn]
  have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edx', he], by rw [edi', he], gg,
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edx', edi',
      by rw [ecx', VG.Proof.AesGcm.X86.pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## Constant time -/

theorem copyLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I copyLoop :=
  CT.taint _ hr (by taint_decide)

theorem xorLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I xorLoop :=
  CT.taint _ hr (by taint_decide)

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Ghash1`. -/
section

/-!
# AES-GCM on x86: calling `vg_ghash` from the pieces

Untrusted: everything here is checked by Lean. `ghArgs yo` sets up the
arguments of `vg_ghash` but the data (`ebx`) and the number of blocks (`edi`):
the hash subkey `Ctx + 240`, the accumulator `St + yo` and the working space
`W + 512` (`GhReady`); the call and `ebp` moved back to `W` continue the
accumulator over the blocks (`ghW_ok`, `GhOut`). `ghash1 yo b o` does it for
the block at `b + o` (`ghash1_ok`). Each is constant time from its
precondition (`ghW_ct`, `ghash1_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- The call of `vg_ghash` and `ebp` back to `W`. -/
abbrev ghW (vg : GcmImpl) : Prog isa := .seq (ghCall vg.callees) (.block unscr)

/-- Ready for `ghW`: the arguments of `vg_ghash` in their registers, `nb`
blocks at `P`. -/
structure GhReady (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx + BitVec.ofNat 32 240
  edx : s.gpr .edx = St + BitVec.ofNat 32 yo
  ebx : s.gpr .ebx = P
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W + BitVec.ofNat 32 512
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  fP : P.toNat + 16 * nb ≤ 2 ^ 32
  rP : Covers [⟨w64 P, 16 * nb⟩] (s.rd ++ s.wr)
  py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16 * nb⟩
  pw : (⟨w64 P, 16 * nb⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩
  pk : (below SP K).Disjoint ⟨w64 P, 16 * nb⟩

/-- What `ghW` leaves. -/
structure GhOut (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s'
  frame : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s'.mem
  out : blockAt s'.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (blockAt s.mem (w64 Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (w64 St + BitVec.ofNat 64 yo))
      (blocksAt s.mem (w64 P) nb)
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem GhReady.call {P : BitVec 32} {nb : Nat} {s : State} (h : VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo P nb s) :
    GhCall s (Ctx + BitVec.ofNat 32 240) (St + BitVec.ofNat 32 yo) P (W + BitVec.ofNat 32 512) nb := by
  have eH := L.aC (o := 240) (by decide)
  have eY := L.aS (o := yo) (by omega)
  have eS := L.aW (o := 512) (by decide)
  have k24 := L.k24
  have hsp : below (s.gpr .esp) 24 = below SP 24 := by rw [h.esp]
  have bsub : Region.Sub (below (s.gpr .esp) 24) (below SP K) := by rw [hsp]; exact L.below_sub k24
  refine ⟨h.eax, h.edx, h.ebx, h.edi, h.ebp, by rw [h.esp]; have := L.sp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eH, eY]; exact L.ctx_st (by decide) (by omega)
  · rw [eH, eS]; exact L.ctx_w (by decide) (by decide)
  · rw [eY]; exact h.py
  · rw [eY, eS]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eS]; exact h.pw
  · rw [eH]; exact (L.stk_ctx (by decide)).sub_left bsub
  · rw [eY]; exact (L.stk_st (by omega)).sub_left bsub
  · exact h.pk.sub_left bsub
  · rw [eS]; exact (L.stk_w (by decide)).sub_left bsub
  · rw [L.nC (by decide)]; have := L.fc; omega
  · rw [L.nS (by omega)]; have := L.fs; omega
  · exact h.fP
  · rw [L.nW (by decide)]; have := L.fw; omega
  · rw [eH]
    exact VG.Proof.AesGcm.X86.covers_cons (VG.Proof.AesGcm.X86.covers_off h.ctxR (by decide) (by decide)) (VG.Proof.AesGcm.X86.covers_cons h.rP VG.Proof.AesGcm.X86.covers_nil)
  · rw [eY, eS]
    exact VG.Proof.AesGcm.X86.covers_cons (VG.Proof.AesGcm.X86.covers_off h.stW (by omega) (by decide)) (VG.Proof.AesGcm.X86.covers_cons (VG.Proof.AesGcm.X86.covers_off h.wW (by decide)
      (by decide)) VG.Proof.AesGcm.X86.covers_nil)

theorem ghW_ok {P : BitVec 32} {nb : Nat} {s : State} (h : VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo P nb s) :
    WP isa (VG.Proof.AesGcm.X86.ghW vg) s (VG.Proof.AesGcm.X86.GhOut Ctx St W SP K yo P nb s) := by
  have eH := L.aC (o := 240) (by decide)
  have eY := L.aS (o := yo) (by omega)
  have eS := L.aW (o := 512) (by decide)
  refine WP.seq (WP.mono (gh_call vg (h.call L hyo)) fun s₁ g => ?_)
  have gf := g.frame
  have go := g.out
  rw [eY, eS] at gf
  rw [eH, eY] at go
  have hsp : below (s.gpr .esp) 24 = below SP 24 := by rw [h.esp]
  rw [hsp] at gf
  have fr : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s₁.mem :=
    gf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, by simp, L.below_sub L.k24⟩
  have bp₁ : s₁.gpr .ebp = W + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.ebp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fr, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, bp₁]; exact BitVec.add_sub_cancel _ _
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esi (by decide), h.esi]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esp (by decide), h.esp]
  · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, g.rd, g.wr]; exact h.ctxR
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.stW
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.wW
  · simp only [mem_setReg, mem_arithFlags]
    rw [VG.Proof.AesGcm.X86.slot_frame fr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm), h.ctx]
  · simp only [mem_setReg, mem_arithFlags]; exact go
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .ebx (by decide)]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .edi (by decide)]
  · mems [g.rd]
  · mems [g.wr]

theorem ghW_ct {P : BitVec 32} {nb : Nat} : CT (VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo P nb) (VG.Proof.AesGcm.X86.ghW vg) := by
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 512)
    (gh_ct vg (E := SP) fun s h => ⟨h.call L hyo, h.esp⟩) (fun s h => WP.mono (gh_call vg (h.call L hyo))
      fun s₁ g => by rw [g.saved .ebp (by decide), h.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

omit hyo in
/-- `ghArgs yo`, from a state with an environment and the data in `ebx`, `edi`. -/
theorem ghArgs_ok {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) :
    ∃ s', runBlock isa (ghArgs yo) s = some s' ∧ s'.gpr .eax = Ctx + BitVec.ofNat 32 240 ∧
      s'.gpr .edx = St + BitVec.ofNat 32 yo ∧ s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by xrun [ghArgs, he.ebp, he.esi, L.aW, he.wIn'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.ctx]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.esi]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.ebp]
  · intro r h₁ h₂ h₃; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

end

/-! ## `ghash1` -/

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit hyo in
/-- `ghash1 yo b o`'s block, for the block at `P = b + o`. -/
theorem ghash1Pre_ok {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .esi ∨ b = .ebp)
    {P : BitVec 32} (hP : s.gpr b + BitVec.ofNat 32 o = P) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr))
    (py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (pw : (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩)
    (pk : (below SP K).Disjoint ⟨w64 P, 16⟩) :
    WP isa (.block (([.mov .ebx (.reg b), .alu .add .ebx (imm o), .mov .edi (imm 1)] : List Instr) ++ ghArgs yo)) s
      fun s' => VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo P 1 s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, bx, di, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ebx (.reg b), .alu .add .ebx (imm o), .mov .edi (imm 1)] s = some s₁ ∧
      s₁.gpr .ebx = P ∧ s₁.gpr .edi = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .ebx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rcases hb with rfl | rfl
    all_goals
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hP]
      · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
      · intro r h₁ h₂; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
      all_goals rfl
  have he₁ : VG.Proof.AesGcm.X86.Env Ctx St W SP s₁ := he.keep (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide))
    (g₁ _ (by decide) (by decide)) rd₁ wr₁ (by rw [m₁])
  obtain ⟨s₂, run₂, ax, dx, bp, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesGcm.X86.ghArgs_ok L (yo := yo) he₁
  refine WP.of_runBlock ⟨s₂, VG.Proof.AesGcm.X86.runBlock_app_of run₁ run₂, ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  have e₂ : ∀ {r}, r ≠ .eax → r ≠ .edx → r ≠ .ebp → s₂.gpr r = s₁.gpr r := fun h₁ h₂ h₃ => g₂ _ h₁ h₂ h₃
  refine ⟨ax, dx, by rw [e₂ (by decide) (by decide) (by decide), bx], by rw [e₂ (by decide) (by decide) (by decide), di],
    bp, by rw [e₂ (by decide) (by decide) (by decide)]; exact he₁.esi,
    by rw [e₂ (by decide) (by decide) (by decide)]; exact he₁.esp, ?_, ?_, ?_, ?_, fP, ?_, py, pw, pk⟩
  · rw [rd₂, wr₂]; exact he₁.ctxR
  · rw [wr₂]; exact he₁.stW
  · rw [wr₂]; exact he₁.wW
  · rw [m₂]; exact he₁.ctx
  · rw [rd₂, wr₂, rd₁, wr₁]; exact rP

/-- What `ghash1 yo b o` leaves, from `s`, for the block at `P`. -/
structure G1Out (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (s s' : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s'
  frame : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s'.mem
  out : blockAt s'.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (blockAt s.mem (w64 Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (w64 St + BitVec.ofNat 64 yo))
      [blockAt s.mem (w64 P)]
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem ghash1_ok {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .esi ∨ b = .ebp)
    {P : BitVec 32} (hP : s.gpr b + BitVec.ofNat 32 o = P) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr))
    (py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (pw : (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩)
    (pk : (below SP K).Disjoint ⟨w64 P, 16⟩) :
    WP isa (ghash1 vg.callees yo b o) s (VG.Proof.AesGcm.X86.G1Out Ctx St W SP K yo P s) :=
  WP.seq (WP.mono (VG.Proof.AesGcm.X86.ghash1Pre_ok L (yo := yo) he b o hb hP fP rP py pw pk) fun s₁ ⟨h, m, rd, wr⟩ =>
    WP.mono (VG.Proof.AesGcm.X86.ghW_ok L hyo h) fun s' g => ⟨g.env, m ▸ g.frame, by
      have := g.out; rw [m] at this; rw [this, VG.Proof.AesGcm.X86.blocksAt_one], by rw [g.rd, rd], by rw [g.wr, wr]⟩)

theorem ghash1_ct {I : State → Prop} (b : Reg) (o : Nat) (hbo : (b = .esi ∧ o = 32) ∨ (b = .ebp ∧ o = 96))
    {P : BitVec 32}
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ s.gpr b + BitVec.ofNat 32 o = P ∧ P.toNat + 16 ≤ 2 ^ 32 ∧
      Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩ ∧
      (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧ (below SP K).Disjoint ⟨w64 P, 16⟩) :
    CT I (ghash1 vg.callees yo b o) := by
  have hb : b = .esi ∨ b = .ebp := by rcases hbo with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  refine CT.seq (J := VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo P 1) ?_ (fun s hs => by
    obtain ⟨he, hP, fP, rP, py, pw, pk⟩ := h s hs
    exact WP.mono (VG.Proof.AesGcm.X86.ghash1Pre_ok L (yo := yo) he b o hb hP fP rP py pw pk) fun _ h => h.1) (VG.Proof.AesGcm.X86.ghW_ct L hyo)
  have hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp, .esi], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
    have e₁ := (h s₁ h₁).1; have e₂ := (h s₂ h₂).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [e₁.ebp, e₂.ebp]
    · rw [e₁.esi, e₂.esi]
  rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hyo with rfl | rfl <;>
    exact CT.taint [.ebp, .esi] hr (by taint_decide)

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Common`. -/
section

/-!
# AES-GCM on x86: pieces shared by GHASH and counter mode

Untrusted: everything here is checked by Lean. The arguments of a piece,
kept in `W` (`dO`, `nO`, `bO`: `PSlots`) and the frame their writes stay in
(`pslotR`); the data a piece reads (`DataOk`); `minLen` (`ecx := min (16 -
b, n)`) and `splitWhole` (the whole blocks and the rest), with their
constant-time proofs; and `CT.seqEx`, which strings pieces together whose
pre- and postconditions are indexed by what they started from.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- `CT.seq` for preconditions indexed by what a piece started from. -/
theorem CT.seqEx {α : Sort _} {P Q : α → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun s => ∃ a, P a s) c₁) (hw : ∀ a s, P a s → WP isa c₁ s (Q a))
    (h₂ : CT (fun s => ∃ a, Q a s) c₂) : CT (fun s => ∃ a, P a s) (.seq c₁ c₂) :=
  CT.seq h₁ (fun _ ⟨a, h⟩ => WP.mono (hw a _ h) fun _ h => ⟨a, h⟩) h₂

/-- The word at `W + o`. -/
abbrev slotv (m : Mem) (W : BitVec 32) (o : Nat) : BitVec 32 := m.readW (w64 W + BitVec.ofNat 64 o) 32

theorem slotv_eq (m : Mem) (W : BitVec 32) (o : Nat) : VG.Proof.AesGcm.X86.slotv m W o = m.readW (w64 W + BitVec.ofNat 64 o) 32 := rfl

/-- The arguments of the piece running: the pointer, length and offset at
`W + dO`, `W + nO`, `W + bO`. -/
abbrev pslotR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 dO, 12⟩

/-- The working space, from `W + 240`: the compared tags, the arguments of
the pieces and the callees' working space. -/
abbrev wsR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 240, 2320⟩

theorem pslot_ws (W : BitVec 32) : Region.Sub (VG.Proof.AesGcm.X86.pslotR W) (VG.Proof.AesGcm.X86.wsR W) := Offset.sub _ (by decide) (by decide)

/-- A word written to one of the pieces' slots. -/
theorem pslot_write {m m' : Mem} {W : BitVec 32} (h : Frame [VG.Proof.AesGcm.X86.pslotR W] m m') {o : Nat} (h₁ : dO ≤ o)
    (h₂ : o + 4 ≤ dO + 12) (v : BitVec 32) : Frame [VG.Proof.AesGcm.X86.pslotR W] m (m'.writeW (w64 W + BitVec.ofNat 64 o) v) :=
  h.writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ h₂ (by decide))

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
state, `W` and the stack. -/
structure DataOk (St W SP : BitVec 32) (K : Nat) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  st : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 St, 80⟩
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk : (below SP K).Disjoint ⟨w64 D, n⟩

namespace DataOk

variable {St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.X86.DataOk St W SP K s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.DataOk St W SP K s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem n_lt : n < 2 ^ 64 := by have := h.fit; omega

/-- The bytes `[j, j + k)`. -/
theorem part {j k : Nat} (hk : j + k ≤ n) :
    Covers [⟨w64 D + BitVec.ofNat 64 j, k⟩] (s.rd ++ s.wr) ∧
      (⟨w64 D + BitVec.ofNat 64 j, k⟩ : Region).Disjoint ⟨w64 St, 80⟩ ∧
      (⟨w64 D + BitVec.ofNat 64 j, k⟩ : Region).Disjoint ⟨w64 W, 2560⟩ ∧
      (below SP K).Disjoint ⟨w64 D + BitVec.ofNat 64 j, k⟩ := by
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 j, k⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hk
  exact ⟨VG.Proof.AesGcm.X86.covers_off h.rd hk h.n_lt, h.st.sub_left hs, h.w.sub_left hs, h.stk.sub_right hs⟩

/-- The pointer to byte `j < n`. -/
theorem ptr {j : Nat} (hj : j < n) : w64 (D + BitVec.ofNat 32 j) = w64 D + BitVec.ofNat 64 j :=
  w64_add (by have := h.fit; omega)

theorem ptrN {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j :=
  toNat_add32 (by have := h.fit; omega)

end DataOk

/-! ## `minLen` -/

theorem ofNat16_sub {b : Nat} (hb : b ≤ 16) : BitVec.ofNat 32 16 - BitVec.ofNat 32 b = BitVec.ofNat 32 (16 - b) :=
  VG.Proof.AesGcm.X86.ofNat_sub32 hb (by decide)

/-- `minLen`'s block: `ecx := 16 - b`, `CF := n < 16 - b`. -/
theorem minLen1_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {s : State}
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) {n b : Nat} (hn : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 n)
    (hb : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16) (hnlt : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (imm 16), .alu .sub .ecx (slot bO), .mov .eax (slot nO), .alu .cmp .eax (.reg .ecx)] s =
      some s' ∧ s'.gpr .ecx = BitVec.ofNat 32 (16 - b) ∧ s'.gpr .eax = BitVec.ofNat 32 n ∧
      s'.cf = some (decide (n < 16 - b)) ∧ (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 := VG.Proof.AesGcm.X86.ofNat16_sub hb16
  refine ⟨_, by xrun [he.ebp, L.aW, he.wIn', hn, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e16]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [VG.Proof.AesGcm.X86.cf_setMem, VG.Proof.AesGcm.X86.gpr_setMem, cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e16,
      toNat_ofNat32 hnlt, toNat_ofNat32 (show 16 - b < 2 ^ 32 by omega)]
  · intro r h₁ h₂; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

/-- What `minLen` leaves. -/
structure MinOut (k : Nat) (s s' : State) : Prop where
  ecx : s'.gpr .ecx = BitVec.ofNat 32 k
  other : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem minLen_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {s : State}
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) {n b : Nat} (hn : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 n)
    (hb : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16) (hnlt : n < 2 ^ 32) :
    WP isa minLen s (VG.Proof.AesGcm.X86.MinOut (min (16 - b) n) s) := by
  obtain ⟨s₁, run₁, cx, ax, cf, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesGcm.X86.minLen1_ok L he hn hb hb16 hnlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - b)) cf (fun ht => ?_) (fun hf => ?_)
  · have hlt : n < 16 - b := by simpa using ht
    refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, ite_true, ax]; congr 1; omega
    · intro r h₁ h₂; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, h₂, ite_false]; exact g₁ r h₁ h₂
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hle : ¬ n < 16 - b := by simpa using hf
    refine WP.block_nil ⟨by rw [cx]; congr 1; omega, g₁, m₁, rd₁, wr₁⟩

theorem minLen_ct {I : State → Prop} {W : BitVec 32} {n b : Nat}
    (hp : ∀ s, I s → s.gpr .ebp = W ∧ ∃ Ctx St SP : BitVec 32, ∃ K, VG.Proof.AesGcm.X86.Lay Ctx St W SP K ∧ VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧
      VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 n ∧ VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b ∧ b ≤ 16 ∧ n < 2 ^ 32) :
    CT I minLen := by
  refine CT.seq (J := fun s => s.cf = some (decide (n < 16 - b))) ?_ (fun s hs => ?_) ?_
  · exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hp _ h₁).1, (hp _ h₂).1]) (by taint_decide)
  · obtain ⟨-, Ctx, St, SP, K, L, he, hn, hb, hb16, hnlt⟩ := hp s hs
    obtain ⟨s₁, run₁, -, -, cf, -⟩ := VG.Proof.AesGcm.X86.minLen1_ok L he hn hb hb16 hnlt
    exact WP.of_runBlock ⟨s₁, run₁, cf⟩
  · refine CT.ite (decide (n < 16 - b)) (fun s h => h) (fun _ => ?_) (fun _ => CT.nil)
    exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)

/-! ## `splitWhole` -/

/-- `splitWhole`, from the slots `dO = D + j` and `nO = n - j`: `ebx = D + j`,
`edi = nb` whole blocks, and the slots the rest; ZF is set if `nb = 0`. -/
theorem splitWhole_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {s : State}
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) {P : BitVec 32} {r : Nat} (hd : VG.Proof.AesGcm.X86.slotv s.mem W dO = P)
    (hn : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 r) (hr : r < 2 ^ 32) :
    ∃ s', runBlock isa splitWhole s = some s' ∧ s'.gpr .ebx = P ∧ s'.gpr .edi = BitVec.ofNat 32 (r / 16) ∧
      s'.zf = some (decide (r / 16 = 0)) ∧
      (∀ q, q ≠ .eax → q ≠ .ebx → q ≠ .edx → q ≠ .edi → s'.gpr q = s.gpr q) ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (r % 16))).writeW
        (w64 W + BitVec.ofNat 64 dO) (P + BitVec.ofNat 32 (16 * (r / 16))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := VG.Proof.AesGcm.X86.shr4 hr
  have hand := VG.Proof.AesGcm.X86.and15 (BitVec.ofNat 32 r)
  rw [toNat_ofNat32 hr] at hand
  have h16 : BitVec.ofNat 32 r - BitVec.ofNat 32 (r % 16) = BitVec.ofNat 32 (16 * (r / 16)) := by
    rw [VG.Proof.AesGcm.X86.ofNat_sub32 (Nat.mod_le _ _) hr]; congr 1; omega
  refine ⟨_, by xrun [splitWhole, he.ebp, L.aW, he.wIn, he.wIn', hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
  · simp only [VG.Proof.AesGcm.X86.zf_setMem, VG.Proof.AesGcm.X86.gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
    rw [VG.Proof.AesGcm.X86.and_self_beq32 (by omega)]
  · intro q h₁ h₂ h₃ h₄; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄, ite_false]
  · simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, hsh, hand, h16]
    rw [BitVec.add_comm (BitVec.ofNat 32 (16 * (r / 16)))]
  all_goals rfl

theorem splitWhole_ct {I : State → Prop} {W : BitVec 32}
    (hp : ∀ s, I s → s.gpr .ebp = W) : CT I (.block splitWhole) :=
  CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hp _ h₁, hp _ h₂]) (by taint_decide)


/-! ## Testing a kept value -/

/-- `mov r, [W + o]; test r, r`: ZF says whether the value kept there is 0. -/
theorem test_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {s : State}
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (r : Reg) (o : Nat) (ho : o + 4 ≤ 2560) {v : Nat}
    (hv : VG.Proof.AesGcm.X86.slotv s.mem W o = BitVec.ofNat 32 v) (hvl : v < 2 ^ 32) :
    WP isa (.block [.mov r (slot o), .alu .test r (.reg r)]) s fun s' =>
      s'.zf = some (decide (v = 0)) ∧ s'.gpr r = BitVec.ofNat 32 v ∧ (∀ q, q ≠ r → s'.gpr q = s.gpr q) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a := L.aW (o := o) (by omega)
  have i := he.wIn' (d := o) (n := 4) ho
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, a, i, hv], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems []; rw [VG.Proof.AesGcm.X86.and_self_beq32 hvl]
  · regs []
  · intro q hq; regs []; exact gpr_setReg_of_ne _ _ hq
  all_goals rfl

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Absorb`. -/
section

/-!
# AES-GCM on x86: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`nO` bytes at `dO` into GHASH, with the accumulator at `St + yo` and the
`bO` buffered bytes at `St + 32` (`absorb_pc`): it fills the buffer
(`head_pc`), absorbs whole blocks (`whole_pc`) and buffers the rest
(`tail_pc`), by the steps of `Proof/Gcm/Stream.lean`. Each is a `Pc`:
correct and constant time, indexed by the memory it started from.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (St W SP : BitVec 32) (K yo : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 St + BitVec.ofNat 64 32, 16⟩, VG.Proof.AesGcm.X86.wsR W, below SP K]

/-- The hash subkey in the context. -/
abbrev Hk (m : Mem) (Ctx : BitVec 32) : Block := blockAt m (w64 Ctx + BitVec.ofNat 64 240)

/-- Before `absorb yo`: the `n` bytes at `D` and `b` bytes buffered. -/
structure AbsIn (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n b : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 n
  bO : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b
  b16 : b < 16
  nlt : n < 2 ^ 32
  data : VG.Proof.AesGcm.X86.DataOk St W SP K s D n

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : BitVec 32) (K yo : Nat) (D : BitVec 32) (n b : Nat) (m₀ : Mem) (j : Nat)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - j)
  data : VG.Proof.AesGcm.X86.DataOk St W SP K s D n
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) j)
  whole : n - j = 0 ∨ (b + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m₀ s.mem

/-- After: everything absorbed, from `m₀`. -/
structure AbsOut (Ctx St W SP : BitVec 32) (K yo : Nat) (D : BitVec 32) (n b : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) n)
  frame : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataOk St W SP K s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86.absFrame St W SP K yo, (⟨w64 D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ VG.Proof.AesGcm.X86.absFrame St W SP K yo, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- The context's slot is apart from what `absorb` writes. -/
theorem slot_absFrame {o : Nat} (h₁ : 96 ≤ o) (h₂ : o + 4 ≤ 240) :
    ∀ r ∈ VG.Proof.AesGcm.X86.absFrame St W SP K yo, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨h₁, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨h₁, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem hk_frame {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m m') : VG.Proof.AesGcm.X86.Hk m' Ctx = VG.Proof.AesGcm.X86.Hk m Ctx :=
  blockAt_frame h (VG.Proof.AesGcm.X86.ctx_absFrame L hyo)

/-- An environment survives `absorb`'s writes, if the registers do. -/
theorem env_absFrame {s s' : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (hf : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (VG.Proof.AesGcm.X86.slot_frame hf (VG.Proof.AesGcm.X86.slot_absFrame L hyo (by decide) (by decide)))

end

theorem pslot_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem} (h : Frame [VG.Proof.AesGcm.X86.pslotR W] m m') :
    Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, VG.Proof.AesGcm.X86.pslot_ws W⟩

theorem buf_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem} {o k : Nat}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 (32 + o), k⟩] m m') (hk : o + k ≤ 16) :
    Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

theorem gh_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] m m') :
    Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨VG.Proof.AesGcm.X86.wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_ofNat_assoc32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

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
  rw [VG.Proof.AesGcm.X86.bytesAt_add]
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
  have := VG.Proof.AesGcm.X86.bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- The bytes `[j, n)` of the data, from those `[0, n)`. -/
theorem bytesAt_drop (m : Mem) (D : Addr) {j n : Nat} (h : j ≤ n) :
    (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := by
  rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.X86.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.X86.length_bytesAt _ _ _), Nat.add_sub_cancel_left]

theorem bytesAt_take (m : Mem) (D : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m D n).take k = bytesAt m D k := by
  rw [show n = k + (n - k) by omega, VG.Proof.AesGcm.X86.bytesAt_add, List.take_left' (VG.Proof.AesGcm.X86.length_bytesAt _ _ _)]

/-- The bytes `[j, j + k)` of the data in `m` are as in `m₀` if all of them are. -/
theorem bytesAt_part {m m₀ : Mem} {D : Addr} {n j k : Nat} (h : bytesAt m D n = bytesAt m₀ D n)
    (hk : j + k ≤ n) : bytesAt m (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := by
  have e := congrArg (fun l => (l.drop j).take k) h
  rwa [VG.Proof.AesGcm.X86.bytesAt_drop _ _ (by omega), VG.Proof.AesGcm.X86.bytesAt_drop _ _ (by omega), VG.Proof.AesGcm.X86.bytesAt_take _ _ (by omega),
    VG.Proof.AesGcm.X86.bytesAt_take _ _ (by omega)] at e

/-! ## Filling the buffer -/

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {yo : Nat}
  {D : BitVec 32} {n b : Nat}
include L

/-- After the block that sets up the copy into the buffer. -/
structure Head2 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  edi : s.gpr .edi = D
  edx : s.gpr .edx = St + BitVec.ofNat 32 (32 + b)
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  bO : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 (b + k)
  fr : Frame [VG.Proof.AesGcm.X86.pslotR W] m₀ s.mem
  data : VG.Proof.AesGcm.X86.DataOk St W SP K s D n

/-- After the copy. -/
structure Head3 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  bO : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 (b + k)
  data : VG.Proof.AesGcm.X86.DataOk St W SP K s D n
  buf : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) (b + k) =
    bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b ++ bytesAt m₀ (w64 D) k
  fr : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m₀ s.mem
  fbuf : Frame [VG.Proof.AesGcm.X86.pslotR W, ⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩] m₀ s.mem

theorem head2_ok (k : Nat) (hk : k ≤ n) (m₀ : Mem) {s : State} (h : VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s)
    (hm : s.mem = m₀) {s₁ : State} (hs₁ : VG.Proof.AesGcm.X86.MinOut k s s₁) :
    WP isa (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 32), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (slot bO), .alu .add .eax (.reg .ecx), .store (at_ .ebp bO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax]) s₁
      (VG.Proof.AesGcm.X86.Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k m₀) := by
  have he := h.env
  have he₁ : VG.Proof.AesGcm.X86.Env Ctx St W SP s₁ := he.keep (hs₁.other _ (by decide) (by decide))
    (hs₁.other _ (by decide) (by decide)) (hs₁.other _ (by decide) (by decide)) hs₁.rd hs₁.wr (by rw [hs₁.mem])
  have hd : VG.Proof.AesGcm.X86.slotv s₁.mem W dO = D := by rw [hs₁.mem]; exact h.dO
  have hn : VG.Proof.AesGcm.X86.slotv s₁.mem W nO = BitVec.ofNat 32 n := by rw [hs₁.mem]; exact h.nO
  have hb : VG.Proof.AesGcm.X86.slotv s₁.mem W bO = BitVec.ofNat 32 b := by rw [hs₁.mem]; exact h.bO
  have hc := hs₁.ecx
  have esub : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := VG.Proof.AesGcm.X86.ofNat_sub32 hk h.nlt
  refine WP.of_runBlock ⟨_, by xrun [he₁.ebp, he₁.esi, L.aW, he₁.wIn, he₁.wIn', hd, hn, hb, hc], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he₁.keep (by regs []) (by regs []) (by regs []) rfl rfl (by mems [])
  · regs [hd]
  · regs [he₁.esi, VG.Proof.AesGcm.X86.add_ofNat_assoc32]
  · regs [hc]
  · mems [VG.Proof.AesGcm.X86.slotv_eq, hd, hc]
  · mems [VG.Proof.AesGcm.X86.slotv_eq, hn, hc, esub]
  · mems [VG.Proof.AesGcm.X86.slotv_eq, hb, hc, VG.Proof.AesGcm.X86.ofNat_add_ofNat32]
  · simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg, mem_arithFlags, ← hs₁.mem, ← hm]
    exact VG.Proof.AesGcm.X86.pslot_write (VG.Proof.AesGcm.X86.pslot_write (VG.Proof.AesGcm.X86.pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · exact h.data.of_eq (by mems [hs₁.rd]) (by mems [hs₁.wr])


omit L in
theorem DataOk.take {St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n k : Nat}
    (h : VG.Proof.AesGcm.X86.DataOk St W SP K s D n) (hk : k ≤ n) : VG.Proof.AesGcm.X86.DataOk St W SP K s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  fit := by have := h.fit; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The copy into the buffer. -/
theorem head3_ok (hyo : yo = 0 ∨ yo = 16) (k : Nat) (hk : k ≤ n) (hk1 : 1 ≤ k) (hbk : b + k ≤ 16) (m₀ : Mem) {s : State}
    (h : VG.Proof.AesGcm.X86.Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k m₀ s) :
    WP isa copyLoop s (VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) k m₀) := by
  have he := h.env
  have eS := L.aS (o := 32 + b) (by omega)
  have dk := h.data.take hk
  have lp : VG.Proof.AesGcm.X86.LoopPre s D (St + BitVec.ofNat 32 (32 + b)) k := by
    refine ⟨h.edi, h.edx, h.ecx, hk1, by have := h.data.fit; have := D.isLt; omega, dk.fit, ?_, dk.rd, ?_, ?_⟩
    · rw [L.nS (by omega)]; have := L.fs; omega
    · rw [eS]; exact he.stC (by omega)
    · rw [eS]; exact dk.st.sub_right (Lay.stSub (by omega))
  refine WP.mono (VG.Proof.AesGcm.X86.copyLoop_ok s lp) fun s' c => ?_
  have cm := c.mem
  rw [eS] at cm
  have hlen := VG.Proof.AesGcm.X86.length_bytesAt s.mem (w64 D) k
  have fw : Frame [⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩] s.mem s'.mem := by
    rw [cm]; exact VG.Proof.AesGcm.X86.writeBytes_frame' _ hlen
  have pw : ∀ o, 272 ≤ o → o + 4 ≤ 284 →
      ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩ : Region)], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r :=
    fun o h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.st_w (by omega) (.inr ⟨by omega, by omega⟩)).symm
  have keepS : ∀ {o}, 272 ≤ o → o + 4 ≤ 284 → VG.Proof.AesGcm.X86.slotv s'.mem W o = VG.Proof.AesGcm.X86.slotv s.mem W o :=
    fun h₁ h₂ => VG.Proof.AesGcm.X86.slot_frame fw (pw _ h₁ h₂)
  -- The data and the buffer before the copy are as in `m₀`.
  have dpart : ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 D, k⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dk.w.sub_right (Lay.wSub (by decide))
  have bpart : ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 St + BitVec.ofNat 64 32, b⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have eD : bytesAt s.mem (w64 D) k = bytesAt m₀ (w64 D) k := VG.Proof.AesGcm.X86.bytesAt_frame h.fr dpart (by omega)
  have eB : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b = bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b :=
    VG.Proof.AesGcm.X86.bytesAt_frame h.fr bpart (by omega)
  refine ⟨VG.Proof.AesGcm.X86.env_absFrame L hyo he (VG.Proof.AesGcm.X86.buf_absFrame fw hbk) (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
    (by decide)) c.rd c.wr, by rw [keepS (by decide) (by decide)]; exact h.dO,
    by rw [keepS (by decide) (by decide)]; exact h.nO, by rw [keepS (by decide) (by decide)]; exact h.bO,
    h.data.of_eq c.rd c.wr, ?_, ?_, ?_⟩
  · rw [cm, show w64 St + BitVec.ofNat 64 (32 + b) = w64 St + BitVec.ofNat 64 32 + BitVec.ofNat 64 b from
      (VG.Proof.AesGcm.X86.add_ofNat_assoc _ _ _).symm]
    have := VG.Proof.AesGcm.X86.bytesAt_writeBytes s.mem (w64 St + BitVec.ofNat 64 32) b (bytesAt s.mem (w64 D) k) (by rw [hlen]; omega)
    rw [hlen] at this
    rw [this, eB, eD]
  · exact (VG.Proof.AesGcm.X86.pslot_absFrame h.fr).trans (VG.Proof.AesGcm.X86.buf_absFrame fw hbk)
  · exact (h.fr.mono (by simp)).trans (fw.mono (by simp))


omit L in
theorem Head3.keep {k : Nat} {m₀ : Mem} {s s' : State}
    (h : VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    by rw [hm]; exact h.bO, h.data.of_eq hrd hwr, by rw [hm]; exact h.buf, by rw [hm]; exact h.fr,
    by rw [hm]; exact h.fbuf⟩

theorem head4_ok {k : Nat} (hk : b + k < 2 ^ 32) {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s) :
    WP isa (.block [.mov .eax (slot bO), .alu .cmp .eax (imm 16)]) s fun s' =>
      VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s' ∧
      s'.zf = some (decide (b + k = 16)) := by
  have he := h.env
  have hb := h.bO
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hb], ?_, ?_⟩
  · exact h.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
  · mems []
    rw [VG.Proof.AesGcm.X86.sub_beq32 hk (by decide)]

/-- The buffer at `St + 32`, as a block `ghash1` absorbs. -/
theorem buf_gh (hyo : yo = 0 ∨ yo = 16) {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) :
    VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ s.gpr .esi + BitVec.ofNat 32 32 = St + BitVec.ofNat 32 32 ∧
      (St + BitVec.ofNat 32 32).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (St + BitVec.ofNat 32 32), 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (St + BitVec.ofNat 32 32), 16⟩ ∧
      (⟨w64 (St + BitVec.ofNat 32 32), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
      (below SP K).Disjoint ⟨w64 (St + BitVec.ofNat 32 32), 16⟩ := by
  rw [L.aS (by decide)]
  refine ⟨he, by rw [he.esi], by rw [L.nS (by decide)]; have := L.fs; omega, VG.Proof.AesGcm.X86.covers_left (he.stC (by decide)),
    Lay.st_st (.inl (by omega)) (by omega) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    L.stk_st (by decide)⟩

/-- The pieces' slots are apart from what `ghash1` writes. -/
theorem pslot_gh (hyo : yo = 0 ∨ yo = 16) {o : Nat} (h₁ : 96 ≤ o) (h₂ : o + 4 ≤ 512) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region), ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K],
      (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨h₁, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem head_pc (hyo : yo = 0 ∨ yo = 16) (hn0 : n ≠ 0) (hb0 : b ≠ 0) (hb16 : b < 16) (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) (absorbHead vg.callees yo)
      (VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b · (min (16 - b) n)) := by
  generalize hk : min (16 - b) n = k
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hbk : b + k ≤ 16 := by omega
  refine Pc.seq (Q := fun m₀ s₁ => ∃ s, (VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ VG.Proof.AesGcm.X86.MinOut k s s₁)
    (hk ▸ Pc.of (I := VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b) (R := VG.Proof.AesGcm.X86.MinOut (min (16 - b) n))
      (fun s h => VG.Proof.AesGcm.X86.minLen_ok L h.env h.nO h.bO (by omega) h.nlt)
      (VG.Proof.AesGcm.X86.minLen_ct fun s h => ⟨h.env.ebp, Ctx, St, SP, K, L, h.env, h.nO, h.bO, by omega, h.nlt⟩)
      _ fun _ _ h => h.1) ?_
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k)
    (Pc.taint [.ebp, .esi] (fun m₀ s₁ ⟨s, ⟨h, hm⟩, hs₁⟩ => VG.Proof.AesGcm.X86.head2_ok L k hkn m₀ h hm hs₁)
      (fun _ _ s₁ s₂ ⟨t₁, ⟨h₁, _⟩, g₁⟩ ⟨t₂, ⟨h₂, _⟩, g₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.ebp, h₂.env.ebp]
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.esi, h₂.env.esi])
      (by taint_decide)) ?_
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) k)
    (Pc.taint [.edi, .edx, .ecx] (fun m₀ s h => VG.Proof.AesGcm.X86.head3_ok L hyo k hkn hk1 hbk m₀ h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.edi, h₂.edi]
        · rw [h₁.edx, h₂.edx]
        · rw [h₁.ecx, h₂.ecx])
      (by taint_decide)) ?_
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) k m₀ s ∧ s.zf = some (decide (b + k = 16)))
    (Pc.taint [.ebp] (fun m₀ s h => VG.Proof.AesGcm.X86.head4_ok L (by omega) h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp])
      (by taint_decide)) ?_
  refine Pc.ite (decide (b + k = 16)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h16 : b + k = 16 := by simpa using ht
    refine Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.Env Ctx St W SP) (fun s he => VG.Proof.AesGcm.X86.ghash1_ok L hyo he .esi 32 (.inl rfl)
        (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.1 (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.2.1 (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.2.2.1 (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.2.2.2.1
        (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.2.2.2.2.1 (VG.Proof.AesGcm.X86.buf_gh L hyo he).2.2.2.2.2.2)
      (VG.Proof.AesGcm.X86.ghash1_ct L hyo .esi 32 (.inl ⟨rfl, rfl⟩) fun s he => VG.Proof.AesGcm.X86.buf_gh L hyo he) _ fun _ _ h => h.1.env)
      (fun _ _ h => h) fun m₀ s₅ ⟨s₄, ⟨h, _⟩, g⟩ => ?_
    have eB := L.aS (o := 32) (by decide)
    have go := g.out
    have gf := g.frame
    rw [eB] at go
    have hY : blockAt s₄.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
      blockAt_frame h.fbuf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
        · exact Lay.st_st (.inl (by omega)) (by omega) (by omega)
    have hH : VG.Proof.AesGcm.X86.Hk s₄.mem Ctx = VG.Proof.AesGcm.X86.Hk m₀ Ctx := VG.Proof.AesGcm.X86.hk_frame L hyo h.fr
    refine ⟨g.env, hkn, hnlt, ?_, ?_, h.data.of_eq g.rd g.wr, ?_, .inr (by omega), h.fr.trans (VG.Proof.AesGcm.X86.gh_absFrame gf)⟩
    · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.pslot_gh L hyo (by decide) (by decide))]; exact h.dO
    · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.pslot_gh L hyo (by decide) (by decide))]; exact h.nO
    · intro x hx ha
      refine Proof.Gcm.absorb_complete ha (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; omega)
        (B := bytesAt s₄.mem (w64 St + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ← hx, ha.2]
      · rw [go, hY, show blockAt s₄.mem (w64 Ctx + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86.Hk m₀ Ctx from hH]; rfl
  · have h16 : ¬ b + k = 16 := by simpa using hf
    have hkn' : k = n := by omega
    subst hkn'
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨h, _⟩ => ?_
    refine ⟨h.env, Nat.le_refl _, hnlt, h.dO, h.nO, h.data, fun x hx ha => ?_, .inl (by omega), h.fr⟩
    refine Proof.Gcm.absorb_fill ha (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; omega) ?_ (by rw [VG.Proof.AesGcm.X86.length_bytesAt, hx]; exact h.buf)
    exact blockAt_frame h.fbuf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
      · exact Lay.st_st (.inl (by omega)) (by omega) (by omega)

/-! ## Whole blocks -/

/-- After `splitWhole`, `nb` whole blocks from byte `j`. -/
structure Whole1 (j nb : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 j
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  zf : s.zf = some (decide (nb = 0))
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 (j + 16 * nb)
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 ((n - j) % 16)
  data : VG.Proof.AesGcm.X86.DataOk St W SP K s D n
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) j)
  whole : n - j = 0 ∨ (b + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) m₀ s.mem

omit L in
/-- `Absorbed` outside a frame of the slots. -/
theorem absorbed_pslot {m m' : Mem} {H : Block} {x : List Byte} (hf : Frame [VG.Proof.AesGcm.X86.pslotR W] m m')
    (h : Absorbed m (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) H x) (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
    (hyo : yo = 0 ∨ yo = 16) :
    Absorbed m' (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) H x := by
  refine h.congr (blockAt_frame hf fun r hr => ?_) (VG.Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => ?_) (by omega))
  · simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
  · simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
      (.inr ⟨by decide, by decide⟩))

theorem whole1_ok (hyo : yo = 0 ∨ yo = 16) {j : Nat} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b m₀ j s) :
    WP isa (.block splitWhole) s (VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j ((n - j) / 16) m₀) := by
  have he := h.env
  obtain ⟨s₁, run, bx, di, zf, g, m, rd, wr⟩ := VG.Proof.AesGcm.X86.splitWhole_ok L he h.dO h.nO (r := n - j) (by have := h.nlt; omega)
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  have fr : Frame [VG.Proof.AesGcm.X86.pslotR W] s.mem s₁.mem := by
    rw [m]; exact VG.Proof.AesGcm.X86.pslot_write (VG.Proof.AesGcm.X86.pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  refine ⟨VG.Proof.AesGcm.X86.env_absFrame L hyo he (VG.Proof.AesGcm.X86.pslot_absFrame fr) (g _ (by decide) (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide) (by decide)) rd wr,
    bx, di, zf, ?_, ?_, h.data.of_eq rd wr, fun x hx ha => VG.Proof.AesGcm.X86.absorbed_pslot fr (h.abs x hx ha) L hyo, h.whole,
    h.frame.trans (VG.Proof.AesGcm.X86.pslot_absFrame fr)⟩
  · rw [VG.Proof.AesGcm.X86.slotv_eq, m]; mems [VG.Proof.AesGcm.X86.add_ofNat_assoc32]
  · rw [VG.Proof.AesGcm.X86.slotv_eq, m]; mems []

theorem ghArgs_ok' (hyo : yo = 0 ∨ yo = 16) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb m₀ s) :
    WP isa (.block (ghArgs yo)) s fun s' => VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have he := h.env
  obtain ⟨s', run, ax, dx, bp, g, m, rd, wr⟩ := VG.Proof.AesGcm.X86.ghArgs_ok L (yo := yo) he
  refine WP.of_runBlock ⟨s', run, ?_, m, rd, wr⟩
  have hjn : j < n := by omega
  have eP := h.data.ptr hjn
  obtain ⟨dr, dst, dw, dk⟩ := h.data.part (j := j) (k := 16 * nb) hj
  refine ⟨ax, dx, by rw [g _ (by decide) (by decide) (by decide), h.ebx], by rw [g _ (by decide) (by decide) (by decide),
    h.edi], bp, by rw [g _ (by decide) (by decide) (by decide), he.esi], by rw [g _ (by decide) (by decide) (by decide),
    he.esp], by rw [rd, wr]; exact he.ctxR, by rw [wr]; exact he.stW, by rw [wr]; exact he.wW, by rw [m]; exact he.ctx,
    by rw [h.data.ptrN hjn]; have := h.data.fit; omega, by rw [rd, wr, eP]; exact dr,
    by rw [eP]; exact (dst.sub_right (Lay.stSub (by omega))).symm, by rw [eP]; exact dw.sub_right (Lay.wSub (by decide)),
    by rw [eP]; exact dk⟩

theorem ghArgs_pc (hyo : yo = 0 ∨ yo = 16) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) :
    Pc (VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb)
      (.block (ghArgs yo)) (fun m₀ s => ∃ s₁, VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo)
        (D := D) (n := n) (b := b) j nb m₀ s₁ ∧ VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s ∧
        s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr) := by
  have hw : ∀ (m₀ : Mem) s, VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) j nb m₀ s → WP isa (.block (ghArgs yo)) s (fun s' => ∃ s₁, VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W)
        (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb m₀ s₁ ∧
        VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s' ∧ s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr) :=
    fun m₀ s h => WP.mono (VG.Proof.AesGcm.X86.ghArgs_ok' L hyo hnb hj h) fun s' ⟨g, m, rd, wr⟩ => ⟨s, h, g, m, rd, wr⟩
  have hr : ∀ (a b' : Mem) s₁ s₂, VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j nb a s₁ → VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j nb b' s₂ → ∀ r ∈ [Reg.ebp, .esi], s₁.gpr r = s₂.gpr r := fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.env.ebp, h₂.env.ebp]
    · rw [h₁.env.esi, h₂.env.esi]
  rcases hyo with rfl | rfl
  · exact Pc.taint [.ebp, .esi] hw hr (by taint_decide)
  · exact Pc.taint [.ebp, .esi] hw hr (by taint_decide)

theorem whole_pc (hyo : yo = 0 ∨ yo = 16) {j : Nat} (hj : j ≤ n) (hnlt : n < 2 ^ 32) :
    Pc (VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b · j) (absorbWhole vg.callees yo)
      (VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b · (j + 16 * ((n - j) / 16))) := by
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) j nb)
    (hnb ▸ Pc.taint [.ebp] (fun m₀ s h => VG.Proof.AesGcm.X86.whole1_ok L hyo h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (nb = 0)) (fun _ _ h => h.zf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s h => ?_
    refine ⟨h.env, by omega, hnlt, by rw [h.dO], by rw [h.nO]; congr 1; omega, h.data, h.abs, h.whole,
      h.frame⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hjn : j + 16 * nb ≤ n := by omega
    refine Pc.seq (VG.Proof.AesGcm.X86.ghArgs_pc L hyo h0 hjn) ?_
    refine Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb) (fun _ h => VG.Proof.AesGcm.X86.ghW_ok L hyo h) (VG.Proof.AesGcm.X86.ghW_ct L hyo) _
      fun _ _ ⟨_, _, g, _⟩ => g) (fun _ _ h => h) fun m₀ s₃ ⟨s₂, ⟨s₁, h₁, g₂, m₂, rd₂, wr₂⟩, g₃⟩ => ?_
    have eP := h₁.data.ptr (j := j) (by omega)
    have go := g₃.out
    have gf := g₃.frame
    rw [eP, m₂] at go
    rw [m₂] at gf
    have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86.Hk m₀ Ctx := VG.Proof.AesGcm.X86.hk_frame L hyo h₁.frame
    have hD : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 j) (16 * nb) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) :=
      VG.Proof.AesGcm.X86.bytesAt_part (VG.Proof.AesGcm.X86.bytesAt_frame h₁.frame (VG.Proof.AesGcm.X86.data_absFrame hyo h₁.data) (by have := h₁.data.fit; omega)) hjn
    refine ⟨g₃.env, hjn, hnlt, ?_, ?_, h₁.data.of_eq (g₃.rd.trans rd₂) (g₃.wr.trans wr₂), fun x hx ha => ?_,
      .inr ?_, h₁.frame.trans (VG.Proof.AesGcm.X86.gh_absFrame gf)⟩
    · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame g₃.frame (VG.Proof.AesGcm.X86.pslot_gh L hyo (by decide) (by decide)), m₂]; exact h₁.dO
    · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame g₃.frame (VG.Proof.AesGcm.X86.pslot_gh L hyo (by decide) (by decide)), m₂]
      have := h₁.nO; rw [VG.Proof.AesGcm.X86.slotv_eq] at this; rw [this]; congr 1; omega
    · have hw : (b + j) % 16 = 0 := h₁.whole.resolve_left (by omega)
      have ex : x ++ bytesAt m₀ (w64 D) (j + 16 * nb) =
          (x ++ bytesAt m₀ (w64 D) j) ++ bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [VG.Proof.AesGcm.X86.bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h₁.abs x hx ha) (by rw [List.length_append, VG.Proof.AesGcm.X86.length_bytesAt]; omega)
        (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; omega) ?_
      rw [go, hH, Proof.Gcm.blocksAt_eq, hD]
    · have hw : (b + j) % 16 = 0 := h₁.whole.resolve_left (by omega)
      omega


/-! ## The tail, and the whole of `absorb` -/

omit L in
theorem AbsMid.keep {j : Nat} {m₀ : Mem} {s s' : State} (h : VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b m₀ j s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b m₀ j s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), h.le, h.nlt, by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    h.data.of_eq hrd hwr, by rw [hm]; exact h.abs, h.whole, by rw [hm]; exact h.frame⟩

theorem tail_pc (hyo : yo = 0 ∨ yo = 16) {j : Nat} (hj : j ≤ n) (hr : n - j < 16) :
    Pc (VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b · j) absorbTail (VG.Proof.AesGcm.X86.AbsOut Ctx St W SP K yo D n b ·) := by
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b m₀ j s ∧ s.zf = some (decide (n - j = 0)) ∧
      s.gpr .ecx = BitVec.ofNat 32 (n - j))
    (Pc.taint [.ebp] (fun m₀ s h => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .ecx nO (by decide) h.nO (by have := h.nlt; omega))
        fun s' ⟨zf, cx, g, m, rd, wr⟩ => ⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr, zf, cx⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n - j = 0)) (fun _ _ h => h.2.1) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by simp at ht; omega
    subst h0
    exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ h => ⟨h.1.env, h.1.abs, h.1.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b m₀ j s ∧ s.gpr .edi = D + BitVec.ofNat 32 j ∧
        s.gpr .edx = St + BitVec.ofNat 32 32 ∧ s.gpr .ecx = BitVec.ofNat 32 (n - j))
      (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, _, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.1.env.ebp, h₂.1.env.ebp]
          · rw [h₁.1.env.esi, h₂.1.env.esi]) (by taint_decide)) ?_
    · have he := h.env
      have hd := h.dO
      refine WP.of_runBlock ⟨_, by xrun [he.ebp, he.esi, L.aW, he.wIn', hd], ?_, ?_, ?_, ?_⟩
      · exact h.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
      · regs []
      · regs [he.esi]
      · regs [cx]
    refine Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨h, di, dx, cx⟩ => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)
    have he := h.env
    have hjn : j < n := by omega
    have eP := h.data.ptr hjn
    have eB := L.aS (o := 32) (by decide)
    obtain ⟨dr, dst, dw, dk⟩ := h.data.part (j := j) (k := n - j) (by omega)
    have lp : VG.Proof.AesGcm.X86.LoopPre s (D + BitVec.ofNat 32 j) (St + BitVec.ofNat 32 32) (n - j) := by
      refine ⟨di, dx, cx, by omega, by have := h.nlt; omega, by rw [h.data.ptrN hjn]; have := h.data.fit; omega,
        by rw [L.nS (by decide)]; have := L.fs; omega, by rw [eP]; exact dr, by rw [eB]; exact he.stC (by omega),
        by rw [eP, eB]; exact dst.sub_right (Lay.stSub (by omega))⟩
    refine WP.mono (VG.Proof.AesGcm.X86.copyLoop_ok s lp) fun s' c => ?_
    have cm := c.mem
    rw [eP, eB] at cm
    have hlen := VG.Proof.AesGcm.X86.length_bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨w64 St + BitVec.ofNat 64 32, n - j⟩] s.mem s'.mem := by
      rw [cm]; exact VG.Proof.AesGcm.X86.writeBytes_frame' _ hlen
    have fw' : Frame (VG.Proof.AesGcm.X86.absFrame St W SP K yo) s.mem s'.mem := VG.Proof.AesGcm.X86.buf_absFrame (o := 0) (by simpa using fw) (by omega)
    refine ⟨VG.Proof.AesGcm.X86.env_absFrame L hyo he fw' (c.other _ (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
      (by decide)) c.rd c.wr, fun x hx ha => ?_, h.frame.trans fw'⟩
    have ex : x ++ bytesAt m₀ (w64 D) n = (x ++ bytesAt m₀ (w64 D) j) ++ bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j) := by
      rw [List.append_assoc, ← VG.Proof.AesGcm.X86.bytesAt_add, Nat.add_sub_cancel' hj]
    have ed : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j) :=
      VG.Proof.AesGcm.X86.bytesAt_part (VG.Proof.AesGcm.X86.bytesAt_frame h.frame (VG.Proof.AesGcm.X86.data_absFrame hyo h.data) (by have := h.data.fit; omega)) (by omega)
    rw [ex, ← ed]
    have hw : (b + j) % 16 = 0 := h.whole.resolve_left h0
    refine Proof.Gcm.absorb_tail (h.abs x hx ha) (by rw [List.length_append, VG.Proof.AesGcm.X86.length_bytesAt]; omega)
      (by rw [hlen]; omega) ?_ ?_
    · exact blockAt_frame fw fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)
    · have := VG.Proof.AesGcm.X86.bytesAt_writeBytes_self s.mem (w64 St + BitVec.ofNat 64 32)
        (bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j)) (by rw [hlen]; omega)
      rw [hlen] at this
      rw [cm, hlen]; exact this

theorem absorb_pc (hyo : yo = 0 ∨ yo = 16) (hb16 : b < 16) (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) (absorb vg.callees yo)
      (VG.Proof.AesGcm.X86.AbsOut Ctx St W SP K yo D n b ·) := by
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .eax nO (by decide) h.nO hnlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨⟨h.env.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact h.dO, by rw [m]; exact h.nO, by rw [m]; exact h.bO, h.b16, h.nlt,
          h.data.of_eq rd wr⟩, by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, fun x _ ha => ?_, by rw [hm]; exact Frame.refl _ _⟩
    rw [hm]; simpa [bytesAt] using ha
  have hn0 : n ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ s.zf = some (decide (b = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .eax bO (by decide) h.bO (by omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨⟨h.env.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact h.dO, by rw [m]; exact h.nO, by rw [m]; exact h.bO, h.b16, h.nlt,
          h.data.of_eq rd wr⟩, by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  generalize hj₀ : (if b = 0 then 0 else min (16 - b) n) = j₀
  have hj₀n : j₀ ≤ n := by rw [← hj₀]; split <;> omega
  refine Pc.seq (Q := (VG.Proof.AesGcm.X86.AbsMid Ctx St W SP K yo D n b · j₀)) ?_
    (Pc.seq (VG.Proof.AesGcm.X86.whole_pc L (D := D) (b := b) hyo hj₀n hnlt) (VG.Proof.AesGcm.X86.tail_pc L (D := D) (b := b) hyo (by omega) (by omega)))
  refine Pc.ite (decide (b = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : b = 0 := by simpa using ht
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, Nat.zero_le _, hnlt, by rw [h.dO]; exact (BitVec.add_zero D).symm,
      by rw [h.nO, Nat.sub_zero], h.data, fun x _ ha => ?_, .inr (by omega), by rw [hm]; exact Frame.refl _ _⟩
    rw [hm]; simpa [bytesAt] using ha
  · have h0 : b ≠ 0 := by simpa using hf
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    exact Pc.mono (VG.Proof.AesGcm.X86.head_pc L hyo hn0 h0 hb16 hnlt) (fun _ _ h => h.1) fun _ _ h => h

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Flush`. -/
section

/-!
# AES-GCM on x86: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `bO`
buffered bytes with zeros in `T` and absorbs them (`flush_pc`); `lens yo`
stores the lengths block of the 64-bit lengths kept in `W` in `T` and
absorbs it (`lens_pc`). Both are correct and constant time.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W SP : BitVec 32) (K yo : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, VG.Proof.AesGcm.X86.wsR W, below SP K]

theorem gh_tFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] m m') :
    Frame (VG.Proof.AesGcm.X86.tFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨VG.Proof.AesGcm.X86.wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

theorem t_tFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m m') : Frame (VG.Proof.AesGcm.X86.tFrame St W SP K yo) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, VG.Proof.AesGcm.X86.bytesAt_add, VG.Proof.AesGcm.X86.bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬xs.length + i < xs.length by omega]

theorem zeros_eq (n : Nat) : Spec.Cmac.zeros n = zeros n := rfl

theorem zero4_bytes' (m : Mem) (p : Addr) : bytesAt (Cmac.zero4 m p) p 16 = zeros 16 := Cmac.zero4_bytes m p

theorem store4_eq (m : Mem) (W : BitVec 32) (o : Nat) (a b c d : BitVec 32) :
    (((m.writeW (w64 W + BitVec.ofNat 64 o) a).writeW (w64 W + BitVec.ofNat 64 (o + 4)) b).writeW
      (w64 W + BitVec.ofNat 64 (o + 8)) c).writeW (w64 W + BitVec.ofNat 64 (o + 12)) d =
      Cmac.store4 m (w64 W + BitVec.ofNat 64 o) a b c d := by
  simp only [Cmac.store4, VG.Proof.AesGcm.X86.add_ofNat_assoc]

/-! ## `flush` -/

/-- After `flush yo`: GHASH has absorbed the padding too, from `m₀`. -/
structure FlOut (Ctx St W SP : BitVec 32) (K yo b : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (VG.Proof.AesGcm.X86.Hk m₀ Ctx)
      (x ++ zeros (padLen x.length))
  frame : Frame (VG.Proof.AesGcm.X86.tFrame St W SP K yo) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {yo : Nat}
include L

theorem ctx_tFrame (hyo : yo = 0 ∨ yo = 16) :
    ∀ r ∈ VG.Proof.AesGcm.X86.tFrame St W SP K yo, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

theorem slot_tFrame (hyo : yo = 0 ∨ yo = 16) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    ∀ r ∈ VG.Proof.AesGcm.X86.tFrame St W SP K yo, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by omega, by omega⟩)).symm
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem env_tFrame (hyo : yo = 0 ∨ yo = 16) {s s' : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s)
    (hf : Frame (VG.Proof.AesGcm.X86.tFrame St W SP K yo) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (VG.Proof.AesGcm.X86.slot_frame hf (VG.Proof.AesGcm.X86.slot_tFrame L hyo (by decide) (by decide)))

/-- `T` zeroed, and the pointers of the copy into it. -/
theorem zeroT_ok {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) :
    ∃ s', runBlock isa (zero4 tO ++ ([.mov .edi (.reg .esi), .alu .add .edi (imm 32), .mov .edx (.reg .ebp),
        .alu .add .edx (imm tO)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 96) ∧ s'.gpr .edi = St + BitVec.ofNat 32 32 ∧
      s'.gpr .edx = W + BitVec.ofNat 32 96 ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [zero4, he.ebp, he.esi, L.aW, he.wIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems []; simp only [Proof.Cmac.zero4, Proof.Cmac.store4, VG.Proof.AesGcm.X86.add_ofNat_assoc]; rfl
  · regs [he.esi]
  · regs [he.ebp]
  · intro r h₁ h₂ h₃
    simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
      gpr_setReg_of_ne _ _ h₃]
  all_goals rfl

theorem flush_pc (hyo : yo = 0 ∨ yo = 16) {b : Nat} (hb : b < 16) :
    Pc (fun (m₀ : Mem) s => (VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b) ∧ s.mem = m₀) (flush vg.callees yo)
      (VG.Proof.AesGcm.X86.FlOut Ctx St W SP K yo b ·) := by
  refine Pc.seq (Q := fun m₀ s => ((VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 b) ∧ s.mem = m₀) ∧
      s.zf = some (decide (b = 0)) ∧ s.gpr .ecx = BitVec.ofNat 32 b)
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨he, hb'⟩, hm⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L he .ecx bO (by decide) hb' (by omega))
        fun s' ⟨zf, cx, g, m, rd, wr⟩ => ⟨⟨⟨he.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact hb'⟩, by rw [m, hm]⟩, zf, cx⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.ebp, h₂.1.1.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (b = 0)) (fun _ _ h => h.2.1) (fun ht => ?_) (fun hf => ?_)
  · have h0 : b = 0 := by simpa using ht
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨⟨he, _⟩, hm⟩, _⟩ => ⟨he, fun x hx ha => ?_, by rw [hm]; exact Frame.refl _ _⟩
    rw [Proof.Gcm.padLen_of_mod (by omega), hm]; simpa [zeros] using ha
  · have h0 : b ≠ 0 := by simpa using hf
    -- `T` zeroed.
    refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ s.mem = Cmac.zero4 m₀ (w64 W + BitVec.ofNat 64 96) ∧
        s.gpr .edi = St + BitVec.ofNat 32 32 ∧ s.gpr .edx = W + BitVec.ofNat 32 96 ∧
        s.gpr .ecx = BitVec.ofNat 32 b)
      (Pc.taint [.ebp, .esi] (fun m₀ s ⟨⟨⟨he, _⟩, hm⟩, _, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.1.1.1.ebp, h₂.1.1.1.ebp]
          · rw [h₁.1.1.1.esi, h₂.1.1.1.esi]) (by taint_decide)) ?_
    · obtain ⟨s', run, m, di, dx, g, rd, wr⟩ := VG.Proof.AesGcm.X86.zeroT_ok L he
      have fz : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
      refine WP.of_runBlock ⟨s', run, VG.Proof.AesGcm.X86.env_tFrame L hyo he (VG.Proof.AesGcm.X86.t_tFrame fz) (g _ (by decide) (by decide) (by decide))
        (g _ (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide)) rd wr, by rw [m, hm], di, dx,
        by rw [g _ (by decide) (by decide) (by decide), cx]⟩
    -- The copy.
    refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧
        s.mem = writeBytes (Cmac.zero4 m₀ (w64 W + BitVec.ofNat 64 96)) (w64 W + BitVec.ofNat 64 96)
          (bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b))
      (Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨he, hm, di, dx, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [h₁.2.2.1, h₂.2.2.1]
          · rw [h₁.2.2.2.1, h₂.2.2.2.1]
          · rw [h₁.2.2.2.2, h₂.2.2.2.2]) (by taint_decide)) ?_
    · have eS := L.aS (o := 32) (by decide)
      have eT := L.aW (o := 96) (by decide)
      have lp : VG.Proof.AesGcm.X86.LoopPre s (St + BitVec.ofNat 32 32) (W + BitVec.ofNat 32 96) b := by
        refine ⟨di, dx, cx, by omega, by omega, by rw [L.nS (by decide)]; have := L.fs; omega,
          by rw [L.nW (by decide)]; have := L.fw; omega, by rw [eS]; exact VG.Proof.AesGcm.X86.covers_left (he.stC (by omega)),
          by rw [eT]; exact he.wC (by omega), by rw [eS, eT]; exact L.st_w (a := 32) (n := b) (d := 96) (k := b) (by omega) (.inr ⟨by decide, by omega⟩)⟩
      refine WP.mono (VG.Proof.AesGcm.X86.copyLoop_ok s lp) fun s' c => ?_
      have cm := c.mem
      rw [eS, eT] at cm
      have hS : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b = bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b := by
        rw [hm]; exact bytesAt_frame (Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
          (by omega)
      have hlen := VG.Proof.AesGcm.X86.length_bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b
      have fw : Frame [⟨w64 W + BitVec.ofNat 64 96, b⟩] s.mem s'.mem := by
        rw [cm]; exact VG.Proof.AesGcm.X86.writeBytes_frame' _ hlen
      refine ⟨VG.Proof.AesGcm.X86.env_tFrame L hyo he (VG.Proof.AesGcm.X86.t_tFrame (fw.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩))
        (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
        (by decide)) (c.other _ (by decide) (by decide) (by decide) (by decide)) c.rd c.wr, ?_⟩
      rw [cm, hS, hm]
    -- The block absorbed.
    have hP : ∀ s, VG.Proof.AesGcm.X86.Env Ctx St W SP s → s.gpr .ebp + BitVec.ofNat 32 96 = W + BitVec.ofNat 32 96 ∧
        (W + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (W + BitVec.ofNat 32 96), 16⟩] (s.rd ++ s.wr) ∧
        (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ ∧
        (⟨w64 (W + BitVec.ofNat 32 96), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
        (below SP K).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ := fun s he => by
      rw [L.aW (by decide)]
      exact ⟨by rw [he.ebp], by rw [L.nW (by decide)]; have := L.fw; omega, VG.Proof.AesGcm.X86.covers_left (he.wC (by decide)),
        L.st_w (by omega) (.inr ⟨by decide, by decide⟩), Lay.w_w (.inl (by decide)) (by decide) (by decide),
        L.stk_w (by decide)⟩
    refine Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.Env Ctx St W SP) (fun s he => VG.Proof.AesGcm.X86.ghash1_ok L hyo he .ebp 96 (.inr rfl)
        (hP s he).1 (hP s he).2.1 (hP s he).2.2.1 (hP s he).2.2.2.1 (hP s he).2.2.2.2.1 (hP s he).2.2.2.2.2)
      (VG.Proof.AesGcm.X86.ghash1_ct L hyo .ebp 96 (.inr ⟨rfl, rfl⟩) fun s he => ⟨he, hP s he⟩) _ fun _ _ h => h.1)
      (fun _ _ h => h) fun m₀ s₂ ⟨s₁, ⟨_, hm⟩, g⟩ => ?_
    have go := g.out
    rw [L.aW (by decide)] at go
    have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m₀ s₁.mem := by
      rw [hm]
      exact (Cmac.frame_store4 _ _ _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [VG.Proof.AesGcm.X86.length_bytesAt]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))
    have hT : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 96) 16 =
        bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b ++ zeros (16 - b) := by
      rw [hm, VG.Proof.AesGcm.X86.bytesAt_writeBytes_prefix _ _ _ (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; omega) (by decide), VG.Proof.AesGcm.X86.length_bytesAt]
      congr 1
      have z := VG.Proof.AesGcm.X86.zero4_bytes' m₀ (w64 W + BitVec.ofNat 64 96)
      rw [show (16 : Nat) = b + (16 - b) by omega, VG.Proof.AesGcm.X86.bytesAt_add] at z
      have := congrArg (List.drop b) z
      rwa [List.drop_left' (VG.Proof.AesGcm.X86.length_bytesAt _ _ _), show b + (16 - b) = 16 by omega, zeros, List.drop_replicate,
        show 16 - b = 16 - b from rfl] at this
    have hY : blockAt s₁.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
      blockAt_frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86.Hk m₀ Ctx :=
      blockAt_frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
    refine ⟨g.env, fun x hx ha => ?_, (VG.Proof.AesGcm.X86.t_tFrame fT).trans (VG.Proof.AesGcm.X86.gh_tFrame g.frame)⟩
    refine Proof.Gcm.absorb_pad ha (by omega) (B := bytesAt s₁.mem (w64 W + BitVec.ofNat 64 96) 16) ?_ ?_
    · rw [hT, hx]
    · rw [go, hY, hH]; rfl

end

/-! ## The lengths block -/

section
open VG.Spec.Gcm (be64)

theorem ext32 (w : BitVec 32) (k : Nat) : w.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (w.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bswap_eq : VG.X86.bswap = byteRev32 := rfl

theorem le4_bswap (w : BitVec 32) : Proof.Cmac.le4 (VG.X86.bswap w) =
    [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] := by
  rw [VG.Proof.AesGcm.X86.bswap_eq, Proof.Cmac.le4, byteRev32_extract]

/-- Two byte-reversed words, stored: the big-endian bytes of the 64-bit value. -/
theorem le4_be (u v : BitVec 32) :
    Proof.Cmac.le4 (VG.X86.bswap u) ++ Proof.Cmac.le4 (VG.X86.bswap v) = be64 (u.toNat * 2 ^ 32 + v.toNat) := by
  have hu := u.isLt
  have hv := v.isLt
  rw [VG.Proof.AesGcm.X86.le4_bswap, VG.Proof.AesGcm.X86.le4_bswap]
  simp only [be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true]
  rw [show (24 : Nat) = 8 * 3 from rfl, show (16 : Nat) = 8 * 2 from rfl, show (8 : Nat) = 8 * 1 from rfl,
    show (0 : Nat) = 8 * 0 from rfl, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32, VG.Proof.AesGcm.X86.ext32]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;>
    omega

theorem dbl3 (x : BitVec 32) : (x + x + (x + x) + (x + x + (x + x))).toNat = 8 * x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_add]; omega

/-- The two words `be64w` computes: `8 x` modulo 2⁶⁴. -/
theorem be64w_val (hi lo : BitVec 32) :
    (hi + hi + (hi + hi) + (hi + hi + (hi + hi)) + lo >>> 29).toNat * 2 ^ 32 +
      (lo + lo + (lo + lo) + (lo + lo + (lo + lo))).toNat = 8 * (hi.toNat * 2 ^ 32 + lo.toNat) % 2 ^ 64 := by
  have hl := lo.isLt
  rw [BitVec.toNat_add, VG.Proof.AesGcm.X86.dbl3, VG.Proof.AesGcm.X86.dbl3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- The 64-bit value of the words `lo`, `hi`. -/
abbrev val64 (lo hi : BitVec 32) : Nat := hi.toNat * 2 ^ 32 + lo.toNat

theorem lens_bytes (alo ahi tlo thi : BitVec 32) :
    Proof.Cmac.le4 (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29)) ++
        Proof.Cmac.le4 (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo)))) ++
        Proof.Cmac.le4 (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29)) ++
        Proof.Cmac.le4 (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))) =
      lensBlock (VG.Proof.AesGcm.X86.val64 alo ahi) (VG.Proof.AesGcm.X86.val64 tlo thi) := by
  rw [List.append_assoc, VG.Proof.AesGcm.X86.le4_be, VG.Proof.AesGcm.X86.le4_be, VG.Proof.AesGcm.X86.be64w_val, VG.Proof.AesGcm.X86.be64w_val, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl

end

/-- After `lens yo`: the lengths block absorbed, from `m₀`. -/
structure LensOut (Ctx St W SP : BitVec 32) (K yo : Nat) (aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  out : blockAt s.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (VG.Proof.AesGcm.X86.Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 yo)) [Spec.Gcm.ofBytes (lensBlock aN tN)]
  frame : Frame (VG.Proof.AesGcm.X86.tFrame St W SP K yo) m₀ s.mem

/-- The slots of the lengths. -/
abbrev LensSlots (W : BitVec 32) (al ah tl th : Nat) (alo ahi tlo thi : BitVec 32) (m : Mem) : Prop :=
  VG.Proof.AesGcm.X86.slotv m W al = alo ∧ VG.Proof.AesGcm.X86.slotv m W ah = ahi ∧ VG.Proof.AesGcm.X86.slotv m W tl = tlo ∧ VG.Proof.AesGcm.X86.slotv m W th = thi

/-- Where `lens` finds the lengths, in the three uses. -/
abbrev LensAt (yo al ah tl th : Nat) : Prop :=
  (yo = 0 ∧ al = zO ∧ ah = zO ∧ tl = nlO ∧ th = zO) ∨ (yo = 16 ∧ al = alO ∧ ah = ahO ∧ tl = xlO ∧ th = xhO) ∨
    (yo = 16 ∧ al = alO ∧ ah = zO ∧ tl = lenO ∧ th = zO)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
include L

/-- One `be64w`: the words at `W + lo`, `W + hi` shifted and byte-reversed into `W + o`. -/
theorem be64w_ok {lo hi o : Nat} (hlo : lo + 4 ≤ 2560) (hhi : hi + 4 ≤ 2560) (ho : o + 8 ≤ 2560)
    {vlo vhi : BitVec 32} {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (h1 : VG.Proof.AesGcm.X86.slotv s.mem W lo = vlo)
    (h2 : VG.Proof.AesGcm.X86.slotv s.mem W hi = vhi) :
    ∃ s', runBlock isa (be64w lo hi o) s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 o)
        (VG.X86.bswap (vhi + vhi + (vhi + vhi) + (vhi + vhi + (vhi + vhi)) + vlo >>> 29))).writeW
        (w64 W + BitVec.ofNat 64 o + BitVec.ofNat 64 4)
        (VG.X86.bswap (vlo + vlo + (vlo + vlo) + (vlo + vlo + (vlo + vlo)))) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [VG.Proof.AesGcm.X86.slotv_eq] at h1 h2
  have a1 := L.aW (o := lo) (by omega)
  have a2 := L.aW (o := hi) (by omega)
  have a3 := L.aW (o := o) (by omega)
  have a4 := L.aW (o := o + 4) (by omega)
  have i1 := he.wIn' (d := lo) (n := 4) hlo
  have i2 := he.wIn' (d := hi) (n := 4) hhi
  have i3 := he.wIn (d := o) (n := 4) (by omega)
  have i4 := he.wIn (d := o + 4) (n := 4) (by omega)
  refine ⟨_, by xrun [be64w, he.ebp, a1, a2, a3, a4, i1, i2, i3, i4, h1, h2], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [VG.Proof.AesGcm.X86.add_ofNat_assoc]
  · regs []
  · regs []
  · regs []
  all_goals rfl

theorem lensT_ok {yo al ah tl th : Nat} (hc : VG.Proof.AesGcm.X86.LensAt yo al ah tl th) {alo ahi tlo thi : BitVec 32} {s : State}
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (hs : VG.Proof.AesGcm.X86.LensSlots W al ah tl th alo ahi tlo thi s.mem) :
    ∃ s', runBlock isa (be64w al ah tO ++ be64w tl th (tO + 8)) s = some s' ∧
      s'.mem = Cmac.store4 s.mem (w64 W + BitVec.ofNat 64 96)
        (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29))
        (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo))))
        (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29))
        (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hb : 144 ≤ al ∧ al + 4 ≤ 240 ∧ 144 ≤ ah ∧ ah + 4 ≤ 240 ∧ 144 ≤ tl ∧ tl + 4 ≤ 240 ∧ 144 ≤ th ∧
      th + 4 ≤ 240 := by
    rcases hc with ⟨_, rfl, rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl, rfl⟩ <;> decide
  obtain ⟨s₁, run₁, m₁, bp₁, si₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcm.X86.be64w_ok L (o := 96) (by omega) (by omega) (by decide) he h1 h2
  have he₁ : VG.Proof.AesGcm.X86.Env Ctx St W SP s₁ := he.keep bp₁ si₁ sp₁ rd₁ wr₁ (by
    rw [m₁, VG.Proof.AesGcm.X86.add_ofNat_assoc, VG.Proof.AesGcm.X86.readW_writeW_off (b := 100) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.AesGcm.X86.readW_writeW_off (b := 96) _ _ _ (by decide) (by decide) (by decide)])
  have k : ∀ {o}, 144 ≤ o → o + 4 ≤ 240 → VG.Proof.AesGcm.X86.slotv s₁.mem W o = VG.Proof.AesGcm.X86.slotv s.mem W o := fun h₁ h₂ => by
    rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slotv_eq, m₁, VG.Proof.AesGcm.X86.add_ofNat_assoc, VG.Proof.AesGcm.X86.readW_writeW_off (b := 100) _ _ _ (by omega) (by omega) (by omega),
      VG.Proof.AesGcm.X86.readW_writeW_off (b := 96) _ _ _ (by omega) (by omega) (by omega)]
  obtain ⟨s₂, run₂, m₂, bp₂, si₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesGcm.X86.be64w_ok L (lo := tl) (hi := th) (o := 104) (by omega) (by omega) (by decide) he₁
    (k hb.2.2.2.2.1 hb.2.2.2.2.2.1) (k hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2)
  refine ⟨s₂, VG.Proof.AesGcm.X86.runBlock_app_of run₁ run₂, ?_, by rw [bp₂, bp₁], by rw [si₂, si₁], by rw [sp₂, sp₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [m₂, m₁]
  simp only [Proof.Cmac.store4, VG.Proof.AesGcm.X86.add_ofNat_assoc, Nat.reduceAdd, h3, h4]


/-- The block at `W + 96`, as a block `ghash1` absorbs. -/
theorem t_gh {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) :
    VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ s.gpr .ebp + BitVec.ofNat 32 96 = W + BitVec.ofNat 32 96 ∧
      (W + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (W + BitVec.ofNat 32 96), 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ ∧
      (⟨w64 (W + BitVec.ofNat 32 96), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
      (below SP K).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ := by
  rw [L.aW (by decide)]
  exact ⟨he, by rw [he.ebp], by rw [L.nW (by decide)]; have := L.fw; omega, VG.Proof.AesGcm.X86.covers_left (he.wC (by decide)),
    L.st_w (by omega) (.inr ⟨by decide, by decide⟩), Lay.w_w (.inl (by decide)) (by decide) (by decide),
    L.stk_w (by decide)⟩

theorem lens_pc_aux {yo al ah tl th : Nat} (hyo : yo = 0 ∨ yo = 16) (hc : VG.Proof.AesGcm.X86.LensAt yo al ah tl th)
    {alo ahi tlo thi : BitVec 32} {hh : Taint.Hint VG.X86.taint.T}
    (ht : (VG.X86.taint.check (τr [.ebp]) (.block (be64w al ah tO ++ be64w tl th (tO + 8))) hh).isSome = true) :
    Pc (fun (m₀ : Mem) s => (VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86.LensSlots W al ah tl th alo ahi tlo thi s.mem) ∧ s.mem = m₀)
      (lens vg.callees yo al ah tl th) (VG.Proof.AesGcm.X86.LensOut Ctx St W SP K yo (VG.Proof.AesGcm.X86.val64 alo ahi) (VG.Proof.AesGcm.X86.val64 tlo thi) ·) := by
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ s.mem = Cmac.store4 m₀ (w64 W + BitVec.ofNat 64 96)
      (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29))
      (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo))))
      (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29))
      (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨he, hs⟩, hm⟩ => by
        obtain ⟨s', run, m, bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.lensT_ok L hc he hs
        have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
        exact WP.of_runBlock ⟨s', run, VG.Proof.AesGcm.X86.env_tFrame L hyo he (VG.Proof.AesGcm.X86.t_tFrame fT) bp si sp rd wr, by rw [m, hm]⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.ebp, h₂.1.1.ebp]) ht) ?_
  refine Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.Env Ctx St W SP) (fun s he => VG.Proof.AesGcm.X86.ghash1_ok L hyo he .ebp 96 (.inr rfl)
      (VG.Proof.AesGcm.X86.t_gh L hyo he).2.1 (VG.Proof.AesGcm.X86.t_gh L hyo he).2.2.1 (VG.Proof.AesGcm.X86.t_gh L hyo he).2.2.2.1 (VG.Proof.AesGcm.X86.t_gh L hyo he).2.2.2.2.1
      (VG.Proof.AesGcm.X86.t_gh L hyo he).2.2.2.2.2.1 (VG.Proof.AesGcm.X86.t_gh L hyo he).2.2.2.2.2.2)
    (VG.Proof.AesGcm.X86.ghash1_ct L hyo .ebp 96 (.inr ⟨rfl, rfl⟩) fun s he => VG.Proof.AesGcm.X86.t_gh L hyo he) _ fun _ _ h => h.1)
    (fun _ _ h => h) fun m₀ s₂ ⟨s₁, ⟨_, hm⟩, g⟩ => ?_
  have go := g.out
  rw [L.aW (by decide)] at go
  have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m₀ s₁.mem := by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _
  have hY : blockAt s₁.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86.Hk m₀ Ctx :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hT : blockAt s₁.mem (w64 W + BitVec.ofNat 64 96) =
      Spec.Gcm.ofBytes (lensBlock (VG.Proof.AesGcm.X86.val64 alo ahi) (VG.Proof.AesGcm.X86.val64 tlo thi)) := by
    rw [blockAt, hm, Cmac.bytesAt_store4, VG.Proof.AesGcm.X86.lens_bytes]
  refine ⟨g.env, ?_, (VG.Proof.AesGcm.X86.t_tFrame fT).trans (VG.Proof.AesGcm.X86.gh_tFrame g.frame)⟩
  rw [go, hY, hH, hT]

theorem lens_pc {yo al ah tl th : Nat} (hc : VG.Proof.AesGcm.X86.LensAt yo al ah tl th) {alo ahi tlo thi : BitVec 32} :
    Pc (fun (m₀ : Mem) s => (VG.Proof.AesGcm.X86.Env Ctx St W SP s ∧ VG.Proof.AesGcm.X86.LensSlots W al ah tl th alo ahi tlo thi s.mem) ∧ s.mem = m₀)
      (lens vg.callees yo al ah tl th) (VG.Proof.AesGcm.X86.LensOut Ctx St W SP K yo (VG.Proof.AesGcm.X86.val64 alo ahi) (VG.Proof.AesGcm.X86.val64 tlo thi) ·) := by
  have hc' := hc
  rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact VG.Proof.AesGcm.X86.lens_pc_aux L (.inl rfl) hc' (by taint_decide)
  · exact VG.Proof.AesGcm.X86.lens_pc_aux L (.inr rfl) hc' (by taint_decide)
  · exact VG.Proof.AesGcm.X86.lens_pc_aux L (.inr rfl) hc' (by taint_decide)

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.CtrCall`. -/
section

/-!
# AES-GCM on x86: calling `vg_aes_ctr32` from the pieces

Untrusted: everything here is checked by Lean. The arguments of
`vg_aes_ctr32` in their registers (`CtrReady`): the key schedule at the
context, the rounds, a counter block `C`, `nb` blocks at `Dp` and the
working space `W + 512`; the call and `ebp` back to `W` (`ctrW_ok`,
`CtrOut`) and its constant time (`ctrW_ct`). The number of rounds is kept
at `W + roundsO` (`RoundsAt`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32)

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : BitVec 32) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m (w64 Ctx) (16 * (R + 1)))

/-- The number of rounds, kept at `W + roundsO`. -/
def RoundsAt (m : Mem) (W : BitVec 32) (R : Nat) : Prop :=
  VG.Proof.AesGcm.X86.slotv m W roundsO = BitVec.ofNat 32 R ∧ (R = 10 ∨ R = 12 ∨ R = 14)

/-- The kept values (and our caller's registers): `W + 128` to `W + 240`. -/
abbrev keptR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 128, 112⟩

theorem rounds_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32}
    (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86.keptR W).Disjoint r) {R : Nat} (h : VG.Proof.AesGcm.X86.RoundsAt m W R) : VG.Proof.AesGcm.X86.RoundsAt m' W R :=
  ⟨by rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))];
      exact h.1, h.2⟩

theorem ctx_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32}
    (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86.keptR W).Disjoint r) :
    m'.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = m.readW (w64 W + BitVec.ofNat 64 ctxO) 32 :=
  VG.Proof.AesGcm.X86.slot_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))

theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Ctx : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 Ctx, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.X86.ciphOf m' Ctx R = VG.Proof.AesGcm.X86.ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [VG.Proof.AesGcm.X86.ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem covers_pre {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p, n⟩] rs := by
  have := VG.Proof.AesGcm.X86.covers_off (d := 0) (n := n) h (by omega) hk
  rwa [BitVec.add_zero] at this

/-- The call of `vg_aes_ctr32` and `ebp` back to `W`. -/
abbrev ctrW (vg : GcmImpl) : Prog isa := .seq (ctrCall vg.callees) (.block unscr)

/-- Ready for `ctrW`: the arguments of `vg_aes_ctr32` in their registers. -/
structure CtrReady (Ctx St W SP : BitVec 32) (R : Nat) (C Dp : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = Dp
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W + BitVec.ofNat 32 512
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  rounds : VG.Proof.AesGcm.X86.RoundsAt s.mem W R
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * nb ≤ 2 ^ 32
  wC : Covers [⟨w64 C, 16⟩] s.wr
  wD : Covers [⟨w64 Dp, 16 * nb⟩] s.wr
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  kC : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kD : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  sC : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 2048⟩
  sD : (⟨w64 Dp, 16 * nb⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 2048⟩
  bC : (below SP 28).Disjoint ⟨w64 C, 16⟩
  bD : (below SP 28).Disjoint ⟨w64 Dp, 16 * nb⟩
  pC : (VG.Proof.AesGcm.X86.keptR W).Disjoint ⟨w64 C, 16⟩
  pD : (VG.Proof.AesGcm.X86.keptR W).Disjoint ⟨w64 Dp, 16 * nb⟩

/-- What `ctrW` leaves. -/
structure CtrOut (Ctx St W SP : BitVec 32) (R : Nat) (C Dp : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s'
  rounds : VG.Proof.AesGcm.X86.RoundsAt s'.mem W R
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 Dp, 16 * nb⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28] s.mem s'.mem
  out : blocksAt s'.mem (w64 Dp) nb = ctr32 (VG.Proof.AesGcm.X86.ciphOf s.mem Ctx R) (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 Dp) nb)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 nb (blockAt s.mem (w64 C))
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) (hK : K = 28)
include L hK

theorem CtrReady.call {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R C Dp nb s) :
    CtrCall s Ctx C Dp (W + BitVec.ofNat 32 512) R nb := by
  have eS := L.aW (o := 512) (by decide)
  have hsp : below (s.gpr .esp) 28 = below SP 28 := by rw [h.esp]
  refine ⟨h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp, h.rounds.2, by rw [h.esp]; have := L.sp; omega,
    h.kC.sub_left (Region.sub_prefix (by decide)), h.kD.sub_left (Region.sub_prefix (by decide)), ?_, h.cd,
    by rw [eS]; exact h.sC, by rw [eS]; exact h.sD, by rw [hsp]; subst hK; exact L.kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact h.bC, by rw [hsp]; exact h.bD, ?_, by have := L.fc; omega, h.fC, h.fD, ?_,
    VG.Proof.AesGcm.X86.covers_pre h.ctxR (by decide) (by decide), ?_⟩
  · rw [eS]; exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · rw [hsp, eS]; subst hK; exact L.kw.sub_right (Lay.wSub (by decide))
  · rw [L.nW (by decide)]; have := L.fw; omega
  · rw [eS]; exact VG.Proof.AesGcm.X86.covers_cons h.wC (VG.Proof.AesGcm.X86.covers_cons h.wD (VG.Proof.AesGcm.X86.covers_cons (VG.Proof.AesGcm.X86.covers_off h.wW (by decide) (by decide))
      VG.Proof.AesGcm.X86.covers_nil))

theorem CtrReady.kept {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R C Dp nb s) :
    ∀ r ∈ [(⟨w64 C, 16⟩ : Region), ⟨w64 Dp, 16 * nb⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28],
      (VG.Proof.AesGcm.X86.keptR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.pC
  · exact h.pD
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · subst hK; exact (L.stk_w (by decide)).symm

theorem ctrW_ok {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R C Dp nb s) :
    WP isa (VG.Proof.AesGcm.X86.ctrW vg) s (VG.Proof.AesGcm.X86.CtrOut Ctx St W SP R C Dp nb s) := by
  have eS := L.aW (o := 512) (by decide)
  refine WP.seq (WP.mono (ctr_call vg (h.call L hK)) fun s₁ g => ?_)
  have gf := g.frame
  have hsp : below (s.gpr .esp) 28 = below SP 28 := by rw [h.esp]
  rw [eS, hsp] at gf
  have hk := h.kept L hK
  have bp₁ : s₁.gpr .ebp = W + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.ebp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, gf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, bp₁]; exact BitVec.add_sub_cancel _ _
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esi (by decide), h.esi]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esp (by decide), h.esp]
  · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, g.rd, g.wr]; exact h.ctxR
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.stW
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.wW
  · simp only [mem_setReg, mem_arithFlags]; rw [VG.Proof.AesGcm.X86.ctx_frame gf hk, h.ctx]
  · simp only [mem_setReg, mem_arithFlags]; exact VG.Proof.AesGcm.X86.rounds_frame gf hk h.rounds
  · simp only [mem_setReg, mem_arithFlags]; exact g.out
  · simp only [mem_setReg, mem_arithFlags]; exact g.ctr
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .ebx (by decide)]
  · simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .edi (by decide)]
  · mems [g.rd]
  · mems [g.wr]

theorem ctrW_ct {R : Nat} {C Dp : BitVec 32} {nb : Nat} : CT (VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R C Dp nb) (VG.Proof.AesGcm.X86.ctrW vg) := by
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 512)
    (ctr_ct vg (E := SP) fun s h => ⟨h.call L hK, h.esp⟩) (fun s h => WP.mono (ctr_call vg (h.call L hK))
      fun s₁ g => by rw [g.saved .ebp (by decide), h.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Crypt`. -/
section

/-!
# AES-GCM on x86: counter mode over a piece (`crypt`), the definitions

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `nO` bytes at `dO`, where `bO` is
`P mod 16` and the state holds the counter block (`St + 48`) and the
keystream block (`St + 64`) for `P` bytes (`Proof.Gcm.Ctr`). What holds
before (`CrIn`), part of the way (`CrMid`, `CrAt`) and after (`CrOut`), and
the regions it writes (`crFrame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- The counter and keystream blocks of the state at `St`, for `P` bytes. -/
abbrev CtrS (m : Mem) (St : BitVec 32) (ciph : Block → Block) (icb : Block) (P : Nat) : Prop :=
  Ctr m (w64 St + BitVec.ofNat 64 48) (w64 St + BitVec.ofNat 64 64) ciph icb P

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `SP`. -/
structure DataW (Ctx St W SP : BitVec 32) (K : Nat) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  ok : VG.Proof.AesGcm.X86.DataOk St W SP K s D n
  wr : Covers [⟨w64 D, n⟩] s.wr
  ctx : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem DataW.of_eq {Ctx St W SP : BitVec 32} {K : Nat} {s s' : State} {D : BitVec 32} {n : Nat}
    (h : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.take {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D k :=
  ⟨h.ok.take hk, fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
   h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The bytes `[j, j + k)`, writable and apart from the context. -/
theorem DataW.part {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {j k : Nat} (hk : j + k ≤ n) :
    Covers [⟨w64 D + BitVec.ofNat 64 j, k⟩] s.wr ∧
      (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D + BitVec.ofNat 64 j, k⟩ :=
  ⟨VG.Proof.AesGcm.X86.covers_off h.wr hk h.ok.n_lt, h.ctx.sub_right (Offset.sub_base _ hk)⟩

/-- `[D, D + j)` and `[D + j, D + j + l)` are apart. -/
theorem split_disj {D : Addr} {j l : Nat} (hn : j + l < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, l⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := l) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [VG.Proof.AesGcm.X86.bytesAt_add, VG.Proof.AesGcm.X86.bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, VG.Proof.AesGcm.X86.length_bytesAt]

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Gcm.zeros 16) = 0 := by decide

/-- The regions `crypt` writes. -/
abbrev crFrame (St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 D, n⟩, ⟨w64 St + BitVec.ofNat 64 48, 32⟩, VG.Proof.AesGcm.X86.wsR W, below SP K]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : BitVec 32) (K R : Nat) (D : BitVec 32) (n P : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 n
  bO : VG.Proof.AesGcm.X86.slotv s.mem W bO = BitVec.ofNat 32 (P % 16)
  nlt : n < 2 ^ 32
  data : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n
  rounds : VG.Proof.AesGcm.X86.RoundsAt s.mem W R

/-- What holds part of the way, `j` bytes done, from `m₀`, but the slots. -/
structure CrAt (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  data : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n
  rounds : VG.Proof.AesGcm.X86.RoundsAt s.mem W R
  ctr : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P → VG.Proof.AesGcm.X86.CtrS s.mem St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb (P + j)
  done : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) j = xorKs (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m₀ s.mem

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  at_ : VG.Proof.AesGcm.X86.CrAt Ctx St W SP K R icb D n P m₀ j s
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - j)

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  rounds : VG.Proof.AesGcm.X86.RoundsAt s.mem W R
  ctr : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P → VG.Proof.AesGcm.X86.CtrS s.mem St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb (P + n)
  out : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) n = xorKs (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) n)
  frame : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
include L

theorem ctx_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86.crFrame St W SP K D n, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem kept_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86.crFrame St W SP K D n, (VG.Proof.AesGcm.X86.keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The context's slot is apart from `crFrame`. -/
theorem ctxSlot_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86.crFrame St W SP K D n, (⟨w64 W + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
  fun r hr => (VG.Proof.AesGcm.X86.kept_crFrame L hd r hr).sub_left (Offset.sub _ (by decide) (by decide))

theorem env_crFrame {s s' : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n)
    (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (hf : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (VG.Proof.AesGcm.X86.slot_frame hf (VG.Proof.AesGcm.X86.ctxSlot_crFrame L hd))

theorem ciph_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.X86.ciphOf m' Ctx R = VG.Proof.AesGcm.X86.ciphOf m Ctx R :=
  VG.Proof.AesGcm.X86.ciph_frame hf (VG.Proof.AesGcm.X86.ctx_crFrame L hd) hR

omit L in
/-- The pieces' slots are within `crFrame`. -/
theorem pslot_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [VG.Proof.AesGcm.X86.pslotR W] m m') :
    Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, VG.Proof.AesGcm.X86.pslot_ws W⟩

omit L in
/-- `[D + j, D + j + k)` is within `crFrame`. -/
theorem part_crFrame {D : BitVec 32} {n j k : Nat} (hk : j + k ≤ n) {m m' : Mem}
    (h : Frame [⟨w64 D + BitVec.ofNat 64 j, k⟩] m m') : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hk⟩

/-- `CrAt` after code that writes only the slots. -/
theorem CrAt.pslot {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat} {m₀ : Mem} {j : Nat} {s s' : State}
    (h : VG.Proof.AesGcm.X86.CrAt Ctx St W SP K R icb D n P m₀ j s) (hf : Frame [VG.Proof.AesGcm.X86.pslotR W] s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.CrAt Ctx St W SP K R icb D n P m₀ j s' := by
  have pS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hak (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a k : Nat}, a + k ≤ n → ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 D + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hak)).sub_right (Lay.wSub (by decide))
  refine ⟨VG.Proof.AesGcm.X86.env_crFrame L h.data h.env (VG.Proof.AesGcm.X86.pslot_crFrame hf) hbp hsi hsp hrd hwr, h.le, h.nlt, h.data.of_eq hrd hwr,
    VG.Proof.AesGcm.X86.rounds_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) h.rounds,
    fun hc => (h.ctr hc).congr (blockAt_frame hf (pS (by decide))) (blockAt_frame hf (pS (by decide))),
    fun hc => ?_, ?_, h.whole, h.frame.trans (VG.Proof.AesGcm.X86.pslot_crFrame hf)⟩
  · have := pD (a := 0) (k := j) (by have := h.le; omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame hf this (by have := h.le; have := h.nlt; omega)]; exact h.done hc
  · rw [bytesAt_frame hf (pD (by have := h.le; omega)) (by have := h.nlt; omega)]; exact h.rest

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.CryptHead`. -/
section

/-!
# AES-GCM on x86: the rest of the keystream block (`cryptHead`)

Untrusted: everything here is checked by Lean. With `P mod 16 ≠ 0` bytes of
the keystream block used, `cryptHead` XORs the next `min (16 - P mod 16, n)`
into the data (`cryptHead_pc`), by `Proof.Gcm.ctr_head`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K) {R : Nat} {icb : Block}
  {D : BitVec 32} {n P : Nat}
include L

/-- After the block that sets up the XOR. -/
structure CHead2 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  edi : s.gpr .edi = D
  edx : s.gpr .edx = St + BitVec.ofNat 32 (64 + P % 16)
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  fr : Frame [VG.Proof.AesGcm.X86.pslotR W] m₀ s.mem
  data : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n
  nlt : n < 2 ^ 32
  r0 : VG.Proof.AesGcm.X86.RoundsAt m₀ W R

theorem cHead2_ok (k : Nat) (hk : k ≤ n) (m₀ : Mem) {s : State} (h : VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s)
    (hm : s.mem = m₀) {s₁ : State} (hs₁ : VG.Proof.AesGcm.X86.MinOut k s s₁) :
    WP isa (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax]) s₁
      (VG.Proof.AesGcm.X86.CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n) (P := P) k m₀) := by
  have he := h.env
  have he₁ : VG.Proof.AesGcm.X86.Env Ctx St W SP s₁ := he.keep (hs₁.other _ (by decide) (by decide))
    (hs₁.other _ (by decide) (by decide)) (hs₁.other _ (by decide) (by decide)) hs₁.rd hs₁.wr (by rw [hs₁.mem])
  have hd : VG.Proof.AesGcm.X86.slotv s₁.mem W dO = D := by rw [hs₁.mem]; exact h.dO
  have hn : VG.Proof.AesGcm.X86.slotv s₁.mem W nO = BitVec.ofNat 32 n := by rw [hs₁.mem]; exact h.nO
  have hb : VG.Proof.AesGcm.X86.slotv s₁.mem W bO = BitVec.ofNat 32 (P % 16) := by rw [hs₁.mem]; exact h.bO
  have hc := hs₁.ecx
  have esub : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := VG.Proof.AesGcm.X86.ofNat_sub32 hk h.nlt
  refine WP.of_runBlock ⟨_, by xrun [he₁.ebp, he₁.esi, L.aW, he₁.wIn, he₁.wIn', hd, hn, hb, hc], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.nlt, by rw [← hm]; exact h.rounds⟩
  · exact he₁.keep (by regs []) (by regs []) (by regs []) rfl rfl (by mems [])
  · regs [hd]
  · regs [he₁.esi, VG.Proof.AesGcm.X86.add_ofNat_assoc32]
  · regs [hc]
  · mems [VG.Proof.AesGcm.X86.slotv_eq, hd, hc]
  · mems [VG.Proof.AesGcm.X86.slotv_eq, hn, hc, esub]
  · simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg, mem_arithFlags, ← hs₁.mem, ← hm]
    exact VG.Proof.AesGcm.X86.pslot_write (VG.Proof.AesGcm.X86.pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  · exact h.data.of_eq (by mems [hs₁.rd]) (by mems [hs₁.wr])

/-- The XOR with the rest of the keystream block. -/
theorem cHead3_ok (k : Nat) (hkn : k ≤ n) (hk1 : 1 ≤ k) (hbk : P % 16 + k ≤ 16) (hw : k = n ∨ P % 16 + k = 16)
    (hP : P % 16 ≠ 0) (m₀ : Mem) {s : State}
    (h : VG.Proof.AesGcm.X86.CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n) (P := P) k m₀ s) :
    WP isa xorLoop s (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ k) := by
  have he := h.env
  have eS := L.aS (o := 64 + P % 16) (by omega)
  have dk := h.data.take hkn
  have xp : VG.Proof.AesGcm.X86.XorPre s (St + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h.edx, h.edi, h.ecx, hk1, by have := h.nlt; omega, ?_, dk.ok.fit, ?_, dk.wr, ?_⟩
    · rw [L.nS (by omega)]; have := L.fs; omega
    · rw [eS]; exact VG.Proof.AesGcm.X86.covers_left (he.stC (by omega))
    · rw [eS]; exact (dk.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (VG.Proof.AesGcm.X86.xorLoop_ok s xp) fun s' c => ?_
  have cm := c.mem
  rw [eS] at cm
  have hxl := VG.Proof.AesGcm.X86.length_xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨w64 D, k⟩] s.mem s'.mem := by rw [cm]; exact VG.Proof.AesGcm.X86.writeBytes_frame' _ hxl
  have fw' : Frame [⟨w64 D + BitVec.ofNat 64 0, k⟩] s.mem s'.mem := by simpa using fw
  have hf₁ : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) s.mem s'.mem := VG.Proof.AesGcm.X86.part_crFrame (j := 0) (by omega) fw'
  have hf : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m₀ s'.mem := (VG.Proof.AesGcm.X86.pslot_crFrame h.fr).trans hf₁
  have hlt := h.nlt
  -- What the XOR writes is apart from the state and the slots.
  have dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.st.sub_right (Lay.stSub hal)).symm
  have dW : ∀ {o : Nat}, o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r :=
    fun ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.w.sub_right (Lay.wSub ho)).symm
  have pS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hal (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hal)).sub_right (Lay.wSub (by decide))
  have pD0 : ∀ r ∈ [VG.Proof.AesGcm.X86.pslotR W], (⟨w64 D, k⟩ : Region).Disjoint r := by
    have := pD (a := 0) (l := k) (by omega); simpa using this
  refine ⟨⟨VG.Proof.AesGcm.X86.env_crFrame L h.data he hf₁ (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) c.rd c.wr, hkn, hlt,
    h.data.of_eq c.rd c.wr, VG.Proof.AesGcm.X86.rounds_frame hf (VG.Proof.AesGcm.X86.kept_crFrame L h.data) h.r0, fun hc => ?_, fun hc => ?_, ?_, ?_, hf⟩,
    ?_, ?_⟩
  · refine (hc.head hP hbk).congr ?_ ?_
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
  · have e := VG.Proof.AesGcm.X86.bytesAt_writeBytes_self s.mem (w64 D) (VG.Proof.AesGcm.X86.xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega)
    rw [hxl] at e
    rw [cm, e, VG.Proof.AesGcm.X86.xorBytes, bytesAt_frame h.fr pD0 (by omega), bytesAt_frame h.fr (pS (by omega)) (by omega)]
    have := Proof.Gcm.ctr_head hc hP (d := bytesAt m₀ (w64 D) k) (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; exact hbk)
    rw [VG.Proof.AesGcm.X86.length_bytesAt, VG.Proof.AesGcm.X86.add_ofNat_assoc] at this
    exact this
  · rw [bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesGcm.X86.split_disj (by omega)).symm) (by omega),
      bytesAt_frame h.fr (pD (by omega)) (by omega)]
  · rcases hw with hw | hw
    · left; omega
    · right; omega
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame fw (dW (by decide))]; exact h.dO
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame fw (dW (by decide))]; exact h.nO

theorem cryptHead_pc (hn0 : n ≠ 0) (hP : P % 16 ≠ 0) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) cryptHead
      (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P · (min (16 - P % 16) n)) := by
  have hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize hk : min (16 - P % 16) n = k
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hbk : P % 16 + k ≤ 16 := by omega
  have hw : k = n ∨ P % 16 + k = 16 := by omega
  refine Pc.seq (Q := fun m₀ s₁ => ∃ s, (VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ VG.Proof.AesGcm.X86.MinOut k s s₁)
    (hk ▸ Pc.of (I := VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P) (R := VG.Proof.AesGcm.X86.MinOut (min (16 - P % 16) n))
      (fun s h => VG.Proof.AesGcm.X86.minLen_ok L h.env h.nO h.bO (by omega) h.nlt)
      (VG.Proof.AesGcm.X86.minLen_ct fun s h => ⟨h.env.ebp, Ctx, St, SP, K, L, h.env, h.nO, h.bO, by omega, h.nlt⟩)
      _ fun _ _ h => h.1) ?_
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n)
      (P := P) k)
    (Pc.taint [.ebp, .esi] (fun m₀ s₁ ⟨s, ⟨h, hm⟩, hs₁⟩ => VG.Proof.AesGcm.X86.cHead2_ok L k hkn m₀ h hm hs₁)
      (fun _ _ s₁ s₂ ⟨t₁, ⟨h₁, _⟩, g₁⟩ ⟨t₂, ⟨h₂, _⟩, g₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.ebp, h₂.env.ebp]
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.esi, h₂.env.esi])
      (by taint_decide)) ?_
  exact Pc.taint [.edi, .edx, .ecx] (fun m₀ s h => VG.Proof.AesGcm.X86.cHead3_ok L k hkn hk1 hbk hw hP m₀ h)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.edi, h₂.edi]
      · rw [h₁.edx, h₂.edx]
      · rw [h₁.ecx, h₂.ecx])
    (by taint_decide)

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.CryptWhole`. -/
section

/-!
# AES-GCM on x86: whole blocks of the text (`cryptWhole`)

Untrusted: everything here is checked by Lean. From a block boundary,
`cryptWhole` encrypts the whole blocks left at `dO` with `vg_aes_ctr32`
(`cryptWhole_pc`), by `Proof.Gcm.ctr_whole`. `ctrArgs_ok` sets up the
arguments of the call, here and in `cryptTail`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
include L

/-- `ctrArgs`: the context, the rounds, the counter block and the working space. -/
theorem ctrArgs_ok {R : Nat} {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (hR : VG.Proof.AesGcm.X86.RoundsAt s.mem W R) :
    ∃ s', runBlock isa ctrArgs s = some s' ∧ s'.gpr .eax = Ctx ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = St + BitVec.ofNat 32 48 ∧ s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r₁ := hR.1
  rw [VG.Proof.AesGcm.X86.slotv_eq] at r₁
  refine ⟨_, by xrun [ctrArgs, he.ebp, he.esi, L.aW, he.wIn'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [he.ctx]
  · regs [r₁]
  · regs [he.esi]
  · regs [he.ebp]
  · intro r h₁ h₂ h₃ h₄
    simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
      gpr_setReg_of_ne _ _ h₃, gpr_setReg_of_ne _ _ h₄]
  all_goals rfl

variable {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat}

/-- After `splitWhole`, `nb` whole blocks from byte `j`. -/
structure CWhole1 (j nb : Nat) (m₀ : Mem) (s : State) : Prop where
  at_ : VG.Proof.AesGcm.X86.CrAt Ctx St W SP K R icb D n P m₀ j s
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 j
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  zf : s.zf = some (decide (nb = 0))
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 (j + 16 * nb)
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 ((n - j) % 16)

theorem cWhole1_ok {j : Nat} {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ j s) :
    WP isa (.block splitWhole) s (VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R)
      (icb := icb) (D := D) (n := n) (P := P) j ((n - j) / 16) m₀) := by
  have he := h.at_.env
  obtain ⟨s₁, run, bx, di, zf, g, m, rd, wr⟩ := VG.Proof.AesGcm.X86.splitWhole_ok L he h.dO h.nO (r := n - j)
    (by have := h.at_.nlt; omega)
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  have fr : Frame [VG.Proof.AesGcm.X86.pslotR W] s.mem s₁.mem := by
    rw [m]; exact VG.Proof.AesGcm.X86.pslot_write (VG.Proof.AesGcm.X86.pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  refine ⟨h.at_.pslot L fr (g _ (by decide) (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide) (by decide)) rd wr,
    bx, di, zf, ?_, ?_⟩
  · rw [VG.Proof.AesGcm.X86.slotv_eq, m]; mems [VG.Proof.AesGcm.X86.add_ofNat_assoc32]
  · rw [VG.Proof.AesGcm.X86.slotv_eq, m]; mems []

theorem cArgs_ok (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s) :
    WP isa (.block ctrArgs) s fun s' => VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hK
  have he := h.at_.env
  have hd := h.at_.data
  obtain ⟨s', run, ax, cx, dx, bp, g, m, rd, wr⟩ := VG.Proof.AesGcm.X86.ctrArgs_ok L he h.at_.rounds
  refine WP.of_runBlock ⟨s', run, ?_, m, rd, wr⟩
  have hjn : j < n := by omega
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  obtain ⟨dr, dst, dw, dk⟩ := hd.ok.part (j := j) (k := 16 * nb) hj
  obtain ⟨dwr, dctx⟩ := hd.part (j := j) (k := 16 * nb) hj
  refine ⟨ax, cx, dx, by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ebx],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi], bp,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), he.esi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), he.esp], by rw [rd, wr]; exact he.ctxR,
    by rw [wr]; exact he.stW, by rw [wr]; exact he.wW, by rw [m]; exact he.ctx, by rw [m]; exact h.at_.rounds,
    by rw [L.nS (by decide)]; have := L.fs; omega, by rw [hd.ok.ptrN hjn]; have := hd.ok.fit; omega,
    by rw [wr, eC]; exact he.stC (by decide), by rw [wr, eP]; exact dwr,
    by rw [eC, eP]; exact (dst.sub_right (Lay.stSub (by decide))).symm,
    by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eP]; exact dctx,
    by rw [eC]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    by rw [eP]; exact dw.sub_right (Lay.wSub (by decide)),
    by rw [eC]; exact L.stk_st (by decide), by rw [eP]; exact dk,
    by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
    by rw [eP]; exact (dw.sub_right (Lay.wSub (by decide))).symm⟩

theorem cArgs_pc (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) :
    Pc (VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
        (P := P) j nb) (.block ctrArgs)
      (fun m₀ s => ∃ s₁, VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb)
        (D := D) (n := n) (P := P) j nb m₀ s₁ ∧
        VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s ∧
        s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr) :=
  Pc.taint [.ebp, .esi] (fun m₀ s h => WP.mono (VG.Proof.AesGcm.X86.cArgs_ok L hK hnb hj h) fun s' ⟨g, m, rd, wr⟩ => ⟨s, h, g, m, rd, wr⟩)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.at_.env.ebp, h₂.at_.env.ebp]
      · rw [h₁.at_.env.esi, h₂.at_.env.esi]) (by taint_decide)

/-- What `vg_aes_ctr32` writes on the data from `D + j` is apart from the
rest of the data. -/
theorem ctrFr_disj (hK : K = 28) {s : State} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {j nb a l : Nat}
    (hal : a + l ≤ n) (hsep : a + l ≤ j ∨ j + 16 * nb ≤ a) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  have hn := hd.ok.n_lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact (hd.ok.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.ok.stk.sub_right hs).symm

/-- The slots are apart from what `vg_aes_ctr32` writes. -/
theorem ctrFr_slot (hK : K = 28) {s : State} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {j nb o : Nat}
    (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact ((hd.ok.w.sub_left (Offset.sub_base _ hj)).sub_right (Lay.wSub (by omega))).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem ctrFr_crFrame (hK : K = 28) {j nb : Nat} (hj : j + 16 * nb ≤ n) {m m' : Mem}
    (h : Frame [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28] m m') : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hj⟩
    · exact ⟨VG.Proof.AesGcm.X86.wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

theorem cWhole3 (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hnbd : nb = (n - j) / 16) {m₀ : Mem} {s₁ s₂ s' : State}
    (h : VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s₁)
    (m₂ : s₂.mem = s₁.mem) (rd₂ : s₂.rd = s₁.rd) (wr₂ : s₂.wr = s₁.wr)
    (g : VG.Proof.AesGcm.X86.CtrOut Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s₂ s') :
    VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ (j + 16 * nb) s' := by
  have ha := h.at_
  have hd := ha.data
  have hj : j + 16 * nb ≤ n := by omega
  have hjn : j < n := by omega
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eP, m₂] at gf
  rw [eC, eP, m₂] at go
  rw [eC, m₂] at gc
  have hn := hd.ok.n_lt
  have crs := VG.Proof.AesGcm.X86.ctrFr_crFrame L (D := D) (n := n) hK hj gf
  have hcm : VG.Proof.AesGcm.X86.ciphOf s₁.mem Ctx R = VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R := VG.Proof.AesGcm.X86.ciph_crFrame L hd ha.frame ha.rounds.2
  rw [hcm] at go
  have hw : (P + j) % 16 = 0 := ha.whole.resolve_left (by omega)
  have hrest16 : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 j) (16 * nb) =
      bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) := by
    have e := congrArg (List.take (16 * nb)) ha.rest
    rwa [VG.Proof.AesGcm.X86.bytesAt_take _ _ (by omega), VG.Proof.AesGcm.X86.bytesAt_take _ _ (by omega)] at e
  refine ⟨⟨g.env, hj, ha.nlt, hd.of_eq (g.rd.trans rd₂) (g.wr.trans wr₂), g.rounds, fun hc₀ => ?_, fun hc₀ => ?_,
    ?_, .inr (by omega), ha.frame.trans crs⟩, ?_, ?_⟩
  · have := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).2
    rwa [Nat.add_assoc] at this
  · have w := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).1
    rw [hrest16] at w
    refine VG.Proof.AesGcm.X86.done_append ?_ w
    have := VG.Proof.AesGcm.X86.ctrFr_disj L hK hd (a := 0) (l := j) (j := j) (nb := nb) (by omega) (.inl (by omega)) hj
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame gf this (by omega)]; exact ha.done hc₀
  · rw [bytesAt_frame gf (VG.Proof.AesGcm.X86.ctrFr_disj L hK hd (by omega) (.inr (Nat.le_refl _)) hj) (by omega)]
    have e := congrArg (List.drop (16 * nb)) ha.rest
    rw [VG.Proof.AesGcm.X86.bytesAt_drop _ _ (by omega), VG.Proof.AesGcm.X86.bytesAt_drop _ _ (by omega), VG.Proof.AesGcm.X86.add_ofNat_assoc,
      show n - j - 16 * nb = n - (j + 16 * nb) by omega] at e
    exact e
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.ctrFr_slot L hK hd (by decide) (by decide) hj)]; exact h.dO
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.ctrFr_slot L hK hd (by decide) (by decide) hj)]
    have := h.nO; rw [VG.Proof.AesGcm.X86.slotv_eq] at this; rw [this]; congr 1; omega

theorem cryptWhole_pc (hK : K = 28) {j : Nat} :
    Pc (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P · j) (cryptWhole vg.callees)
      (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P · (j + 16 * ((n - j) / 16))) := by
  generalize hnb : (n - j) / 16 = nb
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D)
      (n := n) (P := P) j nb)
    (hnb ▸ Pc.taint [.ebp] (fun m₀ s h => VG.Proof.AesGcm.X86.cWhole1_ok L h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (nb = 0)) (fun _ _ h => h.zf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s h => ?_
    rw [show j + 16 * 0 = j by omega]
    refine ⟨h.at_, by rw [h.dO, show j + 16 * 0 = j by omega], by rw [h.nO]; congr 1; omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hjn : j + 16 * nb ≤ n := by omega
    refine Pc.seq (VG.Proof.AesGcm.X86.cArgs_pc L hK h0 hjn) ?_
    exact Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb)
        (fun _ h => VG.Proof.AesGcm.X86.ctrW_ok L hK h) (VG.Proof.AesGcm.X86.ctrW_ct L hK) _ fun _ _ ⟨_, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₃ ⟨s₂, ⟨s₁, h₁, _, m₂, rd₂, wr₂⟩, g₃⟩ => VG.Proof.AesGcm.X86.cWhole3 L hK h0 hnb.symm h₁ m₂ rd₂ wr₂ g₃

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.CryptTail`. -/
section

/-!
# AES-GCM on x86: the last bytes of the text (`cryptTail`), and `crypt`

Untrusted: everything here is checked by Lean. From a block boundary with
fewer than 16 bytes left, `cryptTail` makes the next keystream block (the
counter block encrypted onto zeros, by `vg_aes_ctr32`) and XORs it into
them (`cryptTail_pc`), by `Proof.Gcm.ctr_tail`. `crypt_pc`: the three
pieces.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- The regions `vg_aes_ctr32` writes for the keystream block. -/
abbrev ksFrame (St W SP : BitVec 32) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 48, 16⟩, ⟨w64 St + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩,
    below SP 28]

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : VG.Proof.AesGcm.X86.Lay Ctx St W SP K)
include L

theorem ksFrame_crFrame (hK : K = 28) {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86.ksFrame St W SP) m m') :
    Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨VG.Proof.AesGcm.X86.wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

omit L in
theorem ks_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] m m') :
    Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩

theorem data_ksFrame (hK : K = 28) {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n) {a l : Nat}
    (hal : a + l ≤ n) : ∀ r ∈ VG.Proof.AesGcm.X86.ksFrame St W SP, (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.ok.stk.sub_right hs).symm

theorem slot_ksFrame (hK : K = 28) {o : Nat} (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) :
    ∀ r ∈ VG.Proof.AesGcm.X86.ksFrame St W SP, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

variable {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat}

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` for it. -/
theorem tail1_ok {s : State} (he : VG.Proof.AesGcm.X86.Env Ctx St W SP s) (hR : VG.Proof.AesGcm.X86.RoundsAt s.mem W R) :
    WP isa (.block (([.mov .eax (imm 0), .store (at_ .esi 64) .eax, .store (at_ .esi 68) .eax,
          .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi), .alu .add .ebx (imm 64),
          .mov .edi (imm 1)] : List Instr) ++ ctrArgs)) s fun s' =>
      s'.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s'.gpr .eax = Ctx ∧
      s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = St + BitVec.ofNat 32 48 ∧
      s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧ s'.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s'.gpr .edi = BitVec.ofNat 32 1 ∧ s'.gpr .esi = St ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, bx, di, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (imm 0), .store (at_ .esi 64) .eax,
      .store (at_ .esi 68) .eax, .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi),
      .alu .add .ebx (imm 64), .mov .edi (imm 1)] s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s₁.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s₁.gpr .edi = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.esi, L.aS, he.stIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mems []; simp only [Proof.Cmac.zero4, Proof.Cmac.store4, VG.Proof.AesGcm.X86.add_ofNat_assoc]; rfl
    · regs [he.esi]
    · regs []
    · intro r h₁ h₂ h₃
      simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
        gpr_setReg_of_ne _ _ h₃]
    all_goals rfl
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have he₁ : VG.Proof.AesGcm.X86.Env Ctx St W SP s₁ := he.keep (g₁ _ (by decide) (by decide) (by decide))
    (g₁ _ (by decide) (by decide) (by decide)) (g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
    (VG.Proof.AesGcm.X86.slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm)
  have hR₁ : VG.Proof.AesGcm.X86.RoundsAt s₁.mem W R := VG.Proof.AesGcm.X86.rounds_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm) hR
  obtain ⟨s₂, run₂, ax, cx, dx, bp, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesGcm.X86.ctrArgs_ok L he₁ hR₁
  refine WP.of_runBlock ⟨s₂, VG.Proof.AesGcm.X86.runBlock_app_of run₁ run₂, by rw [m₂, m₁], ax, cx, dx, bp,
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bx],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), he₁.esi],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), he₁.esp], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- After the call: the keystream block for the last bytes, and the counter block after it. -/
structure CTail (j : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.X86.Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  hlt : n - j < 16
  nz : n - j ≠ 0
  data : VG.Proof.AesGcm.X86.DataW Ctx St W SP K s D n
  rounds : VG.Proof.AesGcm.X86.RoundsAt s.mem W R
  dO : VG.Proof.AesGcm.X86.slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : VG.Proof.AesGcm.X86.slotv s.mem W nO = BitVec.ofNat 32 (n - j)
  ks : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P → ∃ m, VG.Proof.AesGcm.X86.CtrS m St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb (P + j) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 64) = VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R (blockAt m (w64 St + BitVec.ofNat 64 48)) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt m (w64 St + BitVec.ofNat 64 48))
  done : VG.Proof.AesGcm.X86.CtrS m₀ St (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) j = xorKs (VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) m₀ s.mem

theorem tail2 (hK : K = 28) {j : Nat} (hlt : n - j < 16) (hnz : n - j ≠ 0) {m₀ : Mem} {s₀ s₁ s₂ : State}
    (h : VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ j s₀) (m₁ : s₁.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64))
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr)
    (g : VG.Proof.AesGcm.X86.CtrOut Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s₁ s₂) :
    VG.Proof.AesGcm.X86.CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s₂ := by
  have ha := h.at_
  have hd := ha.data
  have eC := L.aS (o := 48) (by decide)
  have eK := L.aS (o := 64) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eK] at gf go
  rw [eC] at gc
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s₀.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have zS : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have zD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ hal)).sub_right (Lay.stSub (by decide))
  have zW : ∀ {o : Nat}, 96 ≤ o → o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  have hn := hd.ok.n_lt
  have hcm : VG.Proof.AesGcm.X86.ciphOf s₁.mem Ctx R = VG.Proof.AesGcm.X86.ciphOf m₀ Ctx R := by
    rw [VG.Proof.AesGcm.X86.ciph_crFrame L hd (VG.Proof.AesGcm.X86.ks_crFrame fz) ha.rounds.2, VG.Proof.AesGcm.X86.ciph_crFrame L hd ha.frame ha.rounds.2]
  rw [hcm] at go
  have hb0 : blockAt s₁.mem (w64 St + BitVec.ofNat 64 64) = 0 := by
    rw [Spec.Gcm.blockAt, m₁, VG.Proof.AesGcm.X86.zero4_bytes', VG.Proof.AesGcm.X86.ofBytes_zeros]
  rw [VG.Proof.AesGcm.X86.blocksAt_one, VG.Proof.AesGcm.X86.blocksAt_one, hb0] at go
  have hks := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hks
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hks
  simp only [List.getD_cons_zero, BitVec.zero_xor] at hks
  have hcb : blockAt s₁.mem (w64 St + BitVec.ofNat 64 48) = blockAt s₀.mem (w64 St + BitVec.ofNat 64 48) :=
    blockAt_frame fz zS
  refine ⟨g.env, ha.le, ha.nlt, hlt, hnz, hd.of_eq (g.rd.trans rd₁) (g.wr.trans wr₁), g.rounds, ?_, ?_,
    fun hc₀ => ⟨s₀.mem, ha.ctr hc₀, ?_, ?_⟩, fun hc₀ => ?_, ?_, ha.whole.resolve_left hnz,
    (ha.frame.trans (VG.Proof.AesGcm.X86.ks_crFrame fz)).trans (VG.Proof.AesGcm.X86.ksFrame_crFrame L hK gf)⟩
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.slot_ksFrame L hK (by decide) (by decide)),
      VG.Proof.AesGcm.X86.slot_frame fz (zW (by decide) (by decide))]; exact h.dO
  · rw [VG.Proof.AesGcm.X86.slotv_eq, VG.Proof.AesGcm.X86.slot_frame gf (VG.Proof.AesGcm.X86.slot_ksFrame L hK (by decide) (by decide)),
      VG.Proof.AesGcm.X86.slot_frame fz (zW (by decide) (by decide))]; exact h.nO
  · rw [hks, hcb]; simp [Nat.repeat]
  · rw [gc, hcb]; rfl
  · have := VG.Proof.AesGcm.X86.data_ksFrame L hK hd (a := 0) (l := j) (by have := ha.le; omega)
    have z := zD (a := 0) (l := j) (by have := ha.le; omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this z
    rw [bytesAt_frame gf this (by omega), bytesAt_frame fz z (by omega)]; exact ha.done hc₀
  · rw [bytesAt_frame gf (VG.Proof.AesGcm.X86.data_ksFrame L hK hd (by omega)) (by omega), bytesAt_frame fz (zD (by omega)) (by omega)]
    exact ha.rest

theorem tail3 {j : Nat} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.X86.CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s) {s' : State}
    (hx : VG.Proof.AesGcm.X86.XorPost s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) s') :
    VG.Proof.AesGcm.X86.CrOut Ctx St W SP K R icb D n P m₀ s' := by
  have hd := h.data
  have hjn : j < n := by have := h.nz; omega
  have eP := hd.ok.ptr hjn
  have eK := L.aS (o := 64) (by decide)
  have cm := hx.mem
  rw [eP, eK] at cm
  have hn := hd.ok.n_lt
  have hxl := VG.Proof.AesGcm.X86.length_xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨w64 D + BitVec.ofNat 64 j, n - j⟩] s.mem s'.mem := by rw [cm]; exact VG.Proof.AesGcm.X86.writeBytes_frame' _ hxl
  have hf₁ : Frame (VG.Proof.AesGcm.X86.crFrame St W SP K D n) s.mem s'.mem := VG.Proof.AesGcm.X86.part_crFrame (by omega) fw
  have dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D + BitVec.ofNat 64 j, n - j⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.stSub hal) |>.symm
  have e := VG.Proof.AesGcm.X86.bytesAt_writeBytes_self s.mem (w64 D + BitVec.ofNat 64 j)
    (VG.Proof.AesGcm.X86.xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega)
  rw [hxl] at e
  refine ⟨VG.Proof.AesGcm.X86.env_crFrame L hd h.env hf₁ (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) hx.rd hx.wr,
    VG.Proof.AesGcm.X86.rounds_frame hf₁ (VG.Proof.AesGcm.X86.kept_crFrame L hd) h.rounds, fun hc₀ => ?_, fun hc₀ => ?_, h.frame.trans hf₁⟩
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    have t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; exact h.hlt) (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; exact h.nz)).2
    rw [VG.Proof.AesGcm.X86.length_bytesAt, show P + j + (n - j) = P + n by omega] at t
    exact t.congr (blockAt_frame fw (dS (by decide))) (blockAt_frame fw (dS (by decide)))
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    have t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; exact h.hlt) (by rw [VG.Proof.AesGcm.X86.length_bytesAt]; exact h.nz)).1
    rw [VG.Proof.AesGcm.X86.length_bytesAt, h.rest] at t
    rw [show n = j + (n - j) by omega]
    refine VG.Proof.AesGcm.X86.done_append ?_ ?_
    · have := VG.Proof.AesGcm.X86.split_disj (D := w64 D) (j := j) (l := n - j) (by omega)
      rw [bytesAt_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact this) (by omega)]
      exact h.done hc₀
    · rw [cm, e, VG.Proof.AesGcm.X86.xorBytes, h.rest]; exact t

theorem cryptTail_pc (hK : K = 28) {j : Nat} (hlt : n - j < 16) :
    Pc (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P · j) (cryptTail vg.callees) (VG.Proof.AesGcm.X86.CrOut Ctx St W SP K R icb D n P ·) := by
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ j s ∧ s.zf = some (decide (n - j = 0)))
    (Pc.taint [.ebp] (fun m₀ s h => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.at_.env .eax nO (by decide) h.nO
        (by have := h.at_.nlt; omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.at_.pslot L (by rw [m]; exact Frame.refl _ _) (g _ (by decide))
          (g _ (by decide)) (g _ (by decide)) rd wr, by rw [m]; exact h.dO, by rw [m]; exact h.nO⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n - j = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨h, _⟩ => ?_
    have ha := h.at_
    have e : j = n := by have := ha.le; omega
    subst e
    exact ⟨ha.env, ha.rounds, ha.ctr, ha.done, ha.frame⟩
  have hnz : n - j ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => ∃ s₀, VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P m₀ j s₀ ∧
      s.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64) ∧
      VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, _⟩ => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.at_.env.ebp, h₂.1.at_.env.ebp]
        · rw [h₁.1.at_.env.esi, h₂.1.at_.env.esi]) (by taint_decide)) ?_
  · subst hK
    have he := h.at_.env
    refine WP.mono (VG.Proof.AesGcm.X86.tail1_ok L he h.at_.rounds) fun s' ⟨m, ax, cx, dx, bp, bx, di, si, sp, rd, wr⟩ => ⟨s, h, m, ?_, rd, wr⟩
    have eC := L.aS (o := 48) (by decide)
    have eK := L.aS (o := 64) (by decide)
    have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
    refine ⟨ax, cx, dx, bx, di, bp, si, sp, by rw [rd, wr]; exact he.ctxR, by rw [wr]; exact he.stW,
      by rw [wr]; exact he.wW, ?_, ?_, by rw [L.nS (by decide)]; have := L.fs; omega,
      by rw [L.nS (by decide)]; have := L.fs; omega, by rw [wr, eC]; exact he.stC (by decide),
      by rw [wr, eK]; exact he.stC (by decide), by rw [eC, eK]; exact Lay.st_st (.inl (by decide)) (by decide) (by decide),
      by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eK]; exact L.cs.sub_right (Lay.stSub (by decide)),
      by rw [eC]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      by rw [eK]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      by rw [eC]; exact L.stk_st (by decide), by rw [eK]; exact L.stk_st (by decide),
      by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
      by rw [eK]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm⟩
    · rw [VG.Proof.AesGcm.X86.slot_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm]
      exact he.ctx
    · exact VG.Proof.AesGcm.X86.rounds_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm)
        h.at_.rounds
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D)
      (n := n) (P := P) j)
    (Pc.mono (Pc.of (I := VG.Proof.AesGcm.X86.CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1)
        (fun _ h => VG.Proof.AesGcm.X86.ctrW_ok L hK h) (VG.Proof.AesGcm.X86.ctrW_ct L hK) _ fun _ _ ⟨_, _, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₂ ⟨s₁, ⟨s₀, h₀, m₁, _, rd₁, wr₁⟩, g⟩ => VG.Proof.AesGcm.X86.tail2 L hK hlt hnz h₀ m₁ rd₁ wr₁ g) ?_
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb)
      (D := D) (n := n) (P := P) j m₀ s ∧ s.gpr .edi = D + BitVec.ofNat 32 j ∧ s.gpr .edx = St + BitVec.ofNat 32 64 ∧
      s.gpr .ecx = BitVec.ofNat 32 (n - j))
    (Pc.taint [.ebp, .esi] (fun m₀ s h => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.env.ebp, h₂.env.ebp]
        · rw [h₁.env.esi, h₂.env.esi]) (by taint_decide)) ?_
  · have he := h.env
    have hd := h.dO
    have hn := h.nO
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, he.esi, L.aW, he.wIn', hd, hn], ?_, ?_, ?_, ?_⟩
    · refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), h.le, h.nlt,
        h.hlt, h.nz, h.data.of_eq (by mems []) (by mems []), by mems []; exact h.rounds, by mems []; exact h.dO,
        by mems []; exact h.nO, by mems []; exact h.ks, by mems []; exact h.done, by mems []; exact h.rest, h.whole,
        by mems []; exact h.frame⟩
    · regs []
    · regs [he.esi]
    · regs []
  refine Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨h, di, dx, cx⟩ => ?_)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)
  have he := h.env
  have hdd := h.data
  have hjn : j < n := by have := h.nz; omega
  have eP := hdd.ok.ptr hjn
  have eK := L.aS (o := 64) (by decide)
  obtain ⟨dwr, -⟩ := hdd.part (j := j) (k := n - j) (by omega)
  obtain ⟨-, dst, -, -⟩ := hdd.ok.part (j := j) (k := n - j) (by omega)
  have xp : VG.Proof.AesGcm.X86.XorPre s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨dx, di, cx, by omega, by have := h.nlt; omega, by rw [L.nS (by decide)]; have := L.fs; omega,
      by rw [hdd.ok.ptrN hjn]; have := hdd.ok.fit; omega, by rw [eK]; exact VG.Proof.AesGcm.X86.covers_left (he.stC (by omega)),
      by rw [eP]; exact dwr, by rw [eK, eP]; exact (dst.sub_right (Lay.stSub (by omega))).symm⟩
  exact WP.mono (VG.Proof.AesGcm.X86.xorLoop_ok s xp) fun s' x => VG.Proof.AesGcm.X86.tail3 L h x

omit L in
theorem CrIn.keep {s s' : State} (h : VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    by rw [hm]; exact h.bO, h.nlt, h.data.of_eq hrd hwr, by rw [hm]; exact h.rounds⟩

theorem crypt_pc (hK : K = 28) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) (crypt vg.callees)
      (VG.Proof.AesGcm.X86.CrOut Ctx St W SP K R icb D n P ·) := by
  have hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .eax nO (by decide) h.nO h.nlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, h.rounds, fun hc => ?_, fun _ => ?_,
      by rw [hm]; exact Frame.refl _ _⟩
    · rw [hm]; exact hc
    · rw [hm]; rfl
  have hn0 : n ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (P % 16 = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .eax bO (by decide) h.bO (by omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  generalize hj₀ : (if P % 16 = 0 then 0 else min (16 - P % 16) n) = j₀
  have hj₀n : j₀ ≤ n := by rw [← hj₀]; split <;> omega
  refine Pc.seq (Q := (VG.Proof.AesGcm.X86.CrMid Ctx St W SP K R icb D n P · j₀)) ?_
    (Pc.seq (VG.Proof.AesGcm.X86.cryptWhole_pc L hK) (VG.Proof.AesGcm.X86.cryptTail_pc L hK (by omega)))
  refine Pc.ite (decide (P % 16 = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨⟨h.env, Nat.zero_le _, h.nlt, h.data, h.rounds,
      fun hc => by rw [hm]; exact hc, fun _ => by rw [hm]; rfl, by rw [hm], .inr (by omega),
      by rw [hm]; exact Frame.refl _ _⟩, by rw [h.dO]; exact (BitVec.add_zero D).symm, by rw [h.nO, Nat.sub_zero]⟩
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    exact Pc.mono (VG.Proof.AesGcm.X86.cryptHead_pc L hn0 h0) (fun _ _ h => h.1) fun _ _ h => h

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Fn`. -/
section

/-!
# AES-GCM on x86: what every function does

Untrusted: everything here is checked by Lean. Each function takes `W`
from its stack arguments, saves our caller's `ebx, esi, edi, ebp` at
`W + 128` (`save_ok`), copies arguments to their slots in `W` (`keeps_ok`)
and in the end restores the registers (`exit_ok`); the pieces it runs in
between never write `W + 128` to `W + 240` (`keptR`).

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
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

/-- The address of the stack argument `i` on entry, with `esp = SP`. -/
abbrev argA (SP : BitVec 32) (i : Nat) : Addr := w64 (SP + BitVec.ofNat 32 (4 + 4 * i))

/-- The `n` stack arguments on entry. -/
abbrev argsR (SP : BitVec 32) (n : Nat) : Region := ⟨w64 (SP + BitVec.ofNat 32 4), 4 * n⟩

theorem argA_eq {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    VG.Proof.AesGcm.X86.argA SP i = w64 (SP + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * i) := by
  rw [VG.Proof.AesGcm.X86.argA, ← VG.Proof.AesGcm.X86.add_ofNat_assoc32]
  exact w64_add (by rw [toNat_add32 (by omega)]; omega)

theorem argA_sub {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    Region.Sub ⟨VG.Proof.AesGcm.X86.argA SP i, 4⟩ (VG.Proof.AesGcm.X86.argsR SP n) := by
  rw [VG.Proof.AesGcm.X86.argA_eq hi hf]; exact Offset.sub_base _ (by omega)

theorem argA_contains {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (VG.Proof.AesGcm.X86.argsR SP n).Contains (VG.Proof.AesGcm.X86.argA SP i) 4 := by
  rw [VG.Proof.AesGcm.X86.argA_eq hi hf]; exact Offset.contains_base _ (by omega) (by omega)

/-- Where `saveAt` puts our caller's registers. -/
def SavedAt (m : Mem) (W : BitVec 32) (s₀ : State) : Prop :=
  VG.Proof.AesGcm.X86.slotv m W 128 = s₀.gpr .ebx ∧ VG.Proof.AesGcm.X86.slotv m W 132 = s₀.gpr .esi ∧ VG.Proof.AesGcm.X86.slotv m W 136 = s₀.gpr .edi ∧
    VG.Proof.AesGcm.X86.slotv m W 140 = s₀.gpr .ebp

/-- The saved registers' slots. -/
abbrev savedR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 128, 16⟩

theorem SavedAt.frame {m m' : Mem} {W : BitVec 32} {s₀ : State} (h : VG.Proof.AesGcm.X86.SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86.savedR W).Disjoint r) : VG.Proof.AesGcm.X86.SavedAt m' W s₀ := by
  have k : ∀ {o}, 128 ≤ o → o + 4 ≤ 144 → VG.Proof.AesGcm.X86.slotv m' W o = VG.Proof.AesGcm.X86.slotv m W o := fun h₁ h₂ =>
    VG.Proof.AesGcm.X86.slot_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))
  exact ⟨by rw [k (by decide) (by decide)]; exact h.1, by rw [k (by decide) (by decide)]; exact h.2.1,
    by rw [k (by decide) (by decide)]; exact h.2.2.1, by rw [k (by decide) (by decide)]; exact h.2.2.2⟩

theorem SavedAt.frameK {m m' : Mem} {W : BitVec 32} {s₀ : State} (h : VG.Proof.AesGcm.X86.SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86.keptR W).Disjoint r) : VG.Proof.AesGcm.X86.SavedAt m' W s₀ :=
  h.frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide))

/-- The registers saved, and `ebp := W`. -/
theorem save_ok (s : State) {W : BitVec 32} (ha : s.gpr .eax = W) (hw : Covers [⟨w64 W, 2560⟩] s.wr)
    (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    ∃ s', runBlock isa saveAt s = some s' ∧ s'.gpr .ebp = W ∧ (∀ r, r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.AesGcm.X86.SavedAt s'.mem W s ∧
      Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s'.mem := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 :=
    fun ho => VG.Proof.AesGcm.X86.in_off hw ho (by decide)
  refine ⟨_, by xrun [saveAt, ha, aW, wIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [ha]
  · intro r hr; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg_of_ne _ _ hr]
  · simp only [VG.Proof.AesGcm.X86.rd_setMem, rd_setReg]
  · simp only [VG.Proof.AesGcm.X86.wr_setMem, wr_setReg]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [VG.Proof.AesGcm.X86.slotv_eq]; mems [])
  · have c : ∀ d, 128 ≤ d → d + 4 ≤ 144 →
        (⟨w64 W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) 4 :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.gpr_setMem, mem_setReg]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 132 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 140 (by decide) (by decide))

/-- What the copies of stack arguments into `W` need. -/
structure KeepEnv (W SP : BitVec 32) (n : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  rA : Covers [VG.Proof.AesGcm.X86.argsR SP n] (s.rd ++ s.wr)
  aw : (VG.Proof.AesGcm.X86.argsR SP n).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * n ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32

theorem KeepEnv.keep {W SP : BitVec 32} {n : Nat} {s s' : State} (h : VG.Proof.AesGcm.X86.KeepEnv W SP n s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86.KeepEnv W SP n s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], by rw [hwr]; exact h.wW, by rw [hrd, hwr]; exact h.rA, h.aw, h.fa, h.fw⟩

theorem KeepEnv.argIn {W SP : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86.KeepEnv W SP n s) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (VG.Proof.AesGcm.X86.argA SP i) 4 :=
  h.rA _ _ ⟨_, List.mem_singleton_self _, VG.Proof.AesGcm.X86.argA_contains hi h.fa⟩

theorem KeepEnv.argW {W SP : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86.KeepEnv W SP n s) {i : Nat} (hi : i < n)
    {o : Nat} (ho : o + 4 ≤ 2560) : (⟨VG.Proof.AesGcm.X86.argA SP i, 4⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 o, 4⟩ :=
  (h.aw.sub_left (VG.Proof.AesGcm.X86.argA_sub hi h.fa)).sub_right (Lay.wSub ho)

/-- `keep i o`. -/
theorem keep_ok {W SP : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86.KeepEnv W SP n s) {i o : Nat} (hi : i < n)
    (ho : o + 4 ≤ 2560) :
    ∃ s', runBlock isa (VG.Impl.AesGcm.X86.keep i o) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 o) (s.mem.readW (VG.Proof.AesGcm.X86.argA SP i) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := w64_add (by have := h.fw; omega)
  have wIn : InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := VG.Proof.AesGcm.X86.in_off h.wW ho (by decide)
  have rIn := h.argIn hi
  refine ⟨_, by xrun [VG.Impl.AesGcm.X86.keep, h.esp, h.ebp, aW, wIn, rIn], ?_, ?_, ?_, ?_⟩
  · mems []
  · intro r hr; simp only [VG.Proof.AesGcm.X86.gpr_setMem, gpr_setReg_of_ne _ _ hr]
  all_goals rfl

/-- The slot of `p`'s copy. -/
abbrev keepR (W : BitVec 32) (p : Nat × Nat) : Region := ⟨w64 W + BitVec.ofNat 64 p.2, 4⟩

/-- The copies of the arguments `ps` (argument, offset): each slot holds its argument. -/
theorem keeps_ok {W SP : BitVec 32} {n : Nat} (ps : List (Nat × Nat))
    (hps : ∀ p ∈ ps, p.1 < n ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    {s : State} (h : VG.Proof.AesGcm.X86.KeepEnv W SP n s) :
    ∃ s', runBlock isa (ps.flatMap fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) s = some s' ∧
      (∀ p ∈ ps, VG.Proof.AesGcm.X86.slotv s'.mem W p.2 = s.mem.readW (VG.Proof.AesGcm.X86.argA SP p.1) 32) ∧
      Frame (ps.map (VG.Proof.AesGcm.X86.keepR W)) s.mem s'.mem ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ps generalizing s with
  | nil => exact ⟨s, rfl, fun _ h => by simp at h, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨hp1, hp2, hp4⟩ := hps p (List.mem_cons_self ..)
    obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesGcm.X86.keep_ok h hp1 hp2
    have h₁ : VG.Proof.AesGcm.X86.KeepEnv W SP n s₁ := h.keep (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨s', run', sl, fr, g', rd', wr'⟩ :=
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd'.2 h₁
    have fw : Frame [VG.Proof.AesGcm.X86.keepR W p] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have argS : ∀ q ∈ ps, s₁.mem.readW (VG.Proof.AesGcm.X86.argA SP q.1) 32 = s.mem.readW (VG.Proof.AesGcm.X86.argA SP q.1) 32 := fun q hq => by
      have := hps q (List.mem_cons_of_mem _ hq)
      exact fw.readW (r := ⟨VG.Proof.AesGcm.X86.argA SP q.1, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.argW this.1 hp2) (by decide)
    refine ⟨s', VG.Proof.AesGcm.X86.runBlock_app_of run₁ run', fun q hq => ?_, ?_, fun r hr => by rw [g' r hr, g₁ r hr],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [VG.Proof.AesGcm.X86.slotv_eq, fr.readW (r := VG.Proof.AesGcm.X86.keepR W q) (Region.contains_self _ _) (fun r hr => ?_) (by decide), m₁,
          Mem.readW_writeW_self32]
        simp only [List.mem_map] at hr
        obtain ⟨q', hq', rfl⟩ := hr
        have ne : q'.2 ≠ q.2 := fun e => hnd'.1 (List.mem_map.mpr ⟨q', hq', e⟩)
        have := hps q' (List.mem_cons_of_mem _ hq')
        exact Lay.w_w (by omega) (by omega) (by omega)
      · rw [sl q hq, argS q hq]
    · exact (fw.mono (by simp)).trans (fr.mono (fun r hr => List.mem_cons_of_mem _ hr))

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : BitVec 32} (hbp : s.gpr .ebp = W) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : Covers [⟨w64 W, 2560⟩] (s.rd ++ s.wr)) (fw : W.toNat + 2560 ≤ 2 ^ 32) (hs : VG.Proof.AesGcm.X86.SavedAt s.mem W s₀)
    (hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 :=
    fun ho => VG.Proof.AesGcm.X86.in_off hr ho (by decide)
  obtain ⟨e₁, e₂, e₃, e₄⟩ := hs
  simp only [VG.Proof.AesGcm.X86.slotv_eq] at e₁ e₂ e₃ e₄
  refine WP.of_runBlock ⟨_, by xrun [restore, hbp, aW, rIn], ⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · regs [e₁]
    · regs [e₂]
    · regs [e₃]
    · regs [e₄]
    · regs [hsp]
  · simp only [mem_setReg]; exact hret
  · mems []
  · regs []
  · mems []
  · mems []

/-- After the entry's copies: what the rest of the entry block starts from. -/
structure Entered (s : State) (W St : BitVec 32) (nA : Nat) (ps : List (Nat × Nat)) (s₂ : State) : Prop where
  ebp : s₂.gpr .ebp = W
  esi : s₂.gpr .esi = St
  esp : s₂.gpr .esp = s.gpr .esp
  ebx : s₂.gpr .ebx = s.gpr .ebx
  edi : s₂.gpr .edi = s.gpr .edi
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  saved : VG.Proof.AesGcm.X86.SavedAt s₂.mem W s
  slots : ∀ p ∈ ps, VG.Proof.AesGcm.X86.slotv s₂.mem W p.2 = arg s p.1
  args : ∀ i < nA, s₂.mem.readW (VG.Proof.AesGcm.X86.argA (s.gpr .esp) i) 32 = arg s i
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₂.mem

/-- The entry: `W` from the stack argument `w`, the registers saved, the
state pointer into `esi` (by `pre`), the arguments `ps` copied, then `tail`. -/
theorem entry_gen {s : State} {w nA : Nat} (pre : List Instr) (ps : List (Nat × Nat)) (tail : List Instr)
    {W St : BitVec 32} (hw : w < nA)
    (hps : ∀ p ∈ ps, p.1 < nA ∧ 144 ≤ p.2 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    (hW : arg s w = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [VG.Proof.AesGcm.X86.argsR (s.gpr .esp) nA] (s.rd ++ s.wr)) (aw : (VG.Proof.AesGcm.X86.argsR (s.gpr .esp) nA).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32)
    (hpre : ∀ s₁ : State, s₁.gpr .ebp = W → s₁.gpr .esp = s.gpr .esp → s₁.rd = s.rd → s₁.wr = s.wr →
      (∀ i < nA, s₁.mem.readW (VG.Proof.AesGcm.X86.argA (s.gpr .esp) i) 32 = arg s i) →
      ∃ s₂, runBlock isa pre s₁ = some s₂ ∧ s₂.gpr .esi = St ∧ (∀ r, r ≠ .esi → s₂.gpr r = s₁.gpr r) ∧
        s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    {Q : State → Prop} (ht : ∀ s₂, VG.Proof.AesGcm.X86.Entered s W St nA ps s₂ → ∃ s₃, runBlock isa tail s₂ = some s₃ ∧ Q s₃) :
    WP isa (entry w (pre ++ (ps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ tail))) s Q := by
  generalize hSP : s.gpr .esp = SP at rA aw fa hpre
  have argIn : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {i}, i < nA → InRegions (t.rd ++ t.wr) (VG.Proof.AesGcm.X86.argA SP i) 4 :=
    fun hrd hwr _ hi => by rw [hrd, hwr]; exact rA _ _ ⟨_, List.mem_singleton_self _, VG.Proof.AesGcm.X86.argA_contains hi fa⟩
  have i₀ := argIn rfl rfl hw
  have aW : (VG.Proof.AesGcm.X86.argsR SP nA).Disjoint ⟨w64 W, 2560⟩ := aw
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (VG.Proof.AesGcm.X86.argA SP w) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  set s₀ := s.setReg .eax (s.mem.readW (VG.Proof.AesGcm.X86.argA SP w) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := VG.Proof.AesGcm.X86.save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  have hA₁ : ∀ i < nA, s₁.mem.readW (VG.Proof.AesGcm.X86.argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨VG.Proof.AesGcm.X86.argA SP i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aW.sub_left (VG.Proof.AesGcm.X86.argA_sub hi fa)).sub_right (Lay.wSub (by decide))) (by decide)]
    rw [arg, argAddr, hSP]
  obtain ⟨s₂, run₂, si₂, g₂, m₂, rd₂, wr₂⟩ := hpre s₁ bp₁ sp₁ rd₁ wr₁ hA₁
  have ke : VG.Proof.AesGcm.X86.KeepEnv W SP nA s₂ := ⟨by rw [g₂ _ (by decide), bp₁], by rw [g₂ _ (by decide), sp₁],
    by rw [wr₂, wr₁]; exact wW, by rw [rd₂, wr₂, rd₁, wr₁]; exact rA, aW, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesGcm.X86.keeps_ok ps (fun p hp => ⟨(hps p hp).1, (hps p hp).2.2⟩) hnd ke
  -- The arguments are apart from `W`, so the stores keep them.
  have argW : ∀ {i}, i < nA → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨VG.Proof.AesGcm.X86.argA SP i, 4⟩ : Region).Disjoint r := fun hi r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aW.sub_left (VG.Proof.AesGcm.X86.argA_sub hi fa)).sub_right (Lay.wSub (by decide))
  have f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans ((m₂ ▸ f₃).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      have := hps p hp
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  have hargs : ∀ i < nA, s₃.mem.readW (VG.Proof.AesGcm.X86.argA SP i) 32 = arg s i := fun i hi =>
    (f₃'.readW (r := ⟨VG.Proof.AesGcm.X86.argA SP i, 4⟩) (Region.contains_self _ _) (argW hi) (by decide)).trans (by
      rw [arg, argAddr, hSP])
  have hsv : VG.Proof.AesGcm.X86.SavedAt s₃.mem W s := by
    have := sv₁.frame (m₂ ▸ f₃) fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      have := hps p hp
      exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  obtain ⟨s₄, run₄, q⟩ := ht s₃ ⟨by rw [g₃ _ (by decide), g₂ _ (by decide), bp₁],
    by rw [g₃ _ (by decide), si₂],
    by rw [g₃ _ (by decide), g₂ _ (by decide), sp₁, hSP],
    by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide)],
    by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide)],
    by rw [rd₃, rd₂, rd₁]; rfl, by rw [wr₃, wr₂, wr₁]; rfl, hsv,
    fun p hp => by rw [sl₃ p hp, m₂]; exact hA₁ p.1 (hps p hp).1, by rw [hSP]; exact hargs, f₃'⟩
  exact WP.of_runBlock ⟨s₄, VG.Proof.AesGcm.X86.runBlock_app_of run₁ (VG.Proof.AesGcm.X86.runBlock_app_of run₂ (VG.Proof.AesGcm.X86.runBlock_app_of run₃ run₄)), q⟩

/-- The entry with the state pointer the stack argument `k`. -/
theorem entry_ok {s : State} {w k nA : Nat} (ps : List (Nat × Nat)) (tail : List Instr) {W St : BitVec 32}
    (hw : w < nA) (hk : k < nA)
    (hps : ∀ p ∈ ps, p.1 < nA ∧ 144 ≤ p.2 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    (hW : arg s w = W) (hSt : arg s k = St) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [VG.Proof.AesGcm.X86.argsR (s.gpr .esp) nA] (s.rd ++ s.wr)) (aw : (VG.Proof.AesGcm.X86.argsR (s.gpr .esp) nA).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) {Q : State → Prop}
    (ht : ∀ s₂, VG.Proof.AesGcm.X86.Entered s W St nA ps s₂ → ∃ s₃, runBlock isa tail s₂ = some s₃ ∧ Q s₃) :
    WP isa (entry w (([.mov .esi (argOp k)] : List Instr) ++ (ps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ tail))) s Q := by
  refine VG.Proof.AesGcm.X86.entry_gen _ ps tail hw hps hnd hW wW rA aw fa fw (fun s₁ bp sp rd wr ha => ?_) ht
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (VG.Proof.AesGcm.X86.argA (s.gpr .esp) k) 4 := by
    rw [rd, wr]; exact rA _ _ ⟨_, List.mem_singleton_self _, VG.Proof.AesGcm.X86.argA_contains hk fa⟩
  have v := ha k hk
  refine ⟨_, by xrun [sp, i₁, v], ?_, ?_, ?_, ?_, ?_⟩
  · regs [hSt]
  · intro r hr; simp only [gpr_setReg_of_ne _ _ hr]
  all_goals rfl

end VG.Proof.AesGcm.X86

end
