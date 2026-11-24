module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# AES-GCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`), the working space (`N`
bytes at `W`, 2560 unless `vg_aes_ctr32_to` needs fewer than 2048) and the `K` bytes of stack below `SP` used by the calls
(`Lay`): the state is disjoint from the parts of `W` other than `[16, 96)`
(where `seal` and `open` keep it), and the context from both. `Env` says
which registers hold `W`, the state and `SP`, that the context may be read
and the state and `W` written, and that `W + ctxO` holds `Ctx`. `xrun`
runs a straight-line block symbolically.
-/

@[expose] public section

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
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd, hk]),
    Nat.mod_eq_of_lt (by omega_using [hd, hk, hc])]
  omega_using [hd, hc]

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

/-! ## The layout -/

/-- The regions: the context, the state and `W`, of `N` bytes, and the `K`
bytes of stack below `SP` that the calls use (24 for `vg_ghash`, 32 for
`vg_aes_ctr32_to`). `W` holds at least the 512 bytes the functions use
themselves and the 256 of `vg_ghash` after them (`big`): it is of 2560 bytes,
2048 of them for `vg_aes_ctr32_to`, but over an implementation of it that
uses fewer (`Ctr32Impl.scr`, `WSize`), whose callers then have a smaller
frame to wipe. -/
structure Lay (N : Nat) (Ctx St W SP : BitVec 32) (K : Nat) : Prop where
  fc : Ctx.toNat + 256 ≤ 2 ^ 32
  fs : St.toNat + 80 ≤ 2 ^ 32
  fw : W.toNat + N ≤ 2 ^ 32
  k24 : 24 ≤ K
  k32 : K ≤ 32
  sp : K ≤ SP.toNat
  cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩
  cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, N⟩
  sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩
  sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, N - 96⟩
  kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩
  ks : (below SP K).Disjoint ⟨w64 St, 80⟩
  kw : (below SP K).Disjoint ⟨w64 W, N⟩
  big : 768 ≤ N

/-- The registers holding `W`, the state and the stack pointer, what may be
accessed, and the context kept at `W + ctxO`. -/
structure Env (N : Nat) (Ctx St W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, N⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx

/-- The working space, of `N` bytes, of the functions over an implementation
of `vg_aes_ctr32_to` that uses `B` bytes of its own (`Ctr32Impl.scr`) is big
enough: for the layout (`Lay.big`), and for those `B` bytes after the 512 the
functions use themselves (`hB`). It is a fact of the function (its frame's
size, and the implementation it calls), not of a state: the pieces that call
`vg_aes_ctr32_to` take it as an instance, and the others need not carry it. -/
class WSize (N B : Nat) : Prop where
  big : 768 ≤ N
  hB : 512 + B ≤ N

/-- The 2560 bytes are enough for every implementation. -/
instance WSize.full (c : Proof.Aes.X86.Ctr32Impl) : WSize 2560 c.scr :=
  ⟨by decide, by have := c.scr_le; omega_using [this]⟩

/-- 768 bytes are enough for an implementation that uses 256 of its own or fewer. -/
theorem WSize.small {B : Nat} (h : B ≤ 256) : WSize 768 B :=
  ⟨Nat.le_refl _, by omega_using [h]⟩

/-- `N` fits the address space. -/
theorem Lay.nlt {N : Nat} {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K) : N < 2 ^ 64 := by
  have := L.fw; omega_using [this]

/-- `768 ≤ N`, for the size `N` of the working space: from the layout at hand
(`Lay.big`), from the function's (`WSize.big`), or decided for a literal size. The lemmas about offsets into
`W` take it so, and their offsets below 768, which are literals. -/
macro "wbig" : tactic =>
  `(tactic| first | with_reducible assumption | exact Lay.big (by with_reducible assumption) |
    exact @WSize.big _ _ (by with_reducible assumption) | decide)

/-- `k ≤ N` for a literal `k`, at most 768. -/
macro "wle" : tactic => `(tactic| exact Nat.le_trans (by decide) (show 768 ≤ _ by wbig))

/-- A working space that fits the address space is shorter than it. -/
theorem lt_of_fw {N : Nat} {W : BitVec 32} (h : W.toNat + N ≤ 2 ^ 32) : N < 2 ^ 64 := by omega_using [h]

/-- `N < 2 ^ 64`, likewise (`Lay.nlt`, or `lt_of_fw` of a hypothesis at hand). -/
macro "wlt" : tactic =>
  `(tactic| first | with_reducible assumption | exact Lay.nlt (by with_reducible assumption) |
    exact lt_of_fw (by with_reducible assumption) | decide)

namespace Lay

theorem ctxSub {Ctx : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨Ctx + BitVec.ofNat 64 d, n⟩ ⟨Ctx, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {St : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ ⟨St, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {N d n : Nat} (h : d + n ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, N⟩ :=
  Offset.sub_base _ (Nat.le_trans h hN)

/-- The bytes of `W` from `d` on. -/
theorem aboveSub {W : Addr} {N d : Nat} (hd : d ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, N - d⟩ ⟨W, N⟩ :=
  Offset.sub_base _ (by omega_using [hd, hN])

/-- `[W + a, W + a + n)` is within the bytes of `W` from `d` on. -/
theorem aboveIn {W : Addr} {N a n d : Nat} (h₁ : d ≤ a) (h₂ : a + n ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 a, n⟩ ⟨W + BitVec.ofNat 64 d, N - d⟩ :=
  Offset.sub _ h₁ (by omega_using [h₁, h₂, hN])

/-- The bytes of `W` from `a` on are within those from `d` on, before it. -/
theorem above_above {W : Addr} {N a d : Nat} (h : d ≤ a) (ha : a ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 a, N - a⟩ ⟨W + BitVec.ofNat 64 d, N - d⟩ :=
  Offset.sub _ h (by omega_using [h, ha, hN])

/-- `wSub` for any offset, for a function whose working space is of a literal size. -/
theorem wSubN {W : Addr} {N d n : Nat} (h : d + n ≤ N) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, N⟩ :=
  Offset.sub_base _ h

/-- The working space of the functions called, the bytes of `W` from 512 on. -/
theorem hiSub {W : Addr} {N : Nat} (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 512, N - 512⟩ ⟨W, N⟩ :=
  Offset.sub_base _ (by omega_using [hN])

/-- The `g` first bytes of it. -/
theorem hiPre {W : Addr} {N g : Nat} (hg : 512 + g ≤ N) :
    Region.Sub ⟨W + BitVec.ofNat 64 512, g⟩ ⟨W + BitVec.ofNat 64 512, N - 512⟩ :=
  Region.sub_prefix (by omega_using [hg])

/-- The `g` first bytes of it, within `W`. -/
theorem scrSub {W : Addr} {N g : Nat} (hg : 512 + g ≤ N) :
    Region.Sub ⟨W + BitVec.ofNat 64 512, g⟩ ⟨W, N⟩ :=
  Offset.sub_base _ hg

theorem bSub {W : Addr} {N d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, N - 96⟩ :=
  Offset.sub _ h₁ (by omega_using [h₂, hN])

/-- The bytes of `W` from 128 on: what the pieces write. -/
theorem loSub {W : Addr} {N : Nat} (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 128, N - 128⟩ ⟨W, N⟩ :=
  Offset.sub_base _ (by omega_using [hN])

theorem loIn {W : Addr} {N d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 128, N - 128⟩ :=
  Offset.sub _ h₁ (by omega_using [h₂, hN])

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {N : Nat} {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K)
include L

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 768)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂ L.big)

/-- The state and the working space of the functions called. -/
theorem st_hi {a n : Nat} (ha : a + n ≤ 80) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, N - 512⟩ :=
  (L.sb.sub_left (stSub ha)).sub_right (Offset.sub _ (by decide) (by have h₁ := L.big; omega_using [h₁]))

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 768) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw.sub_left (ctxSub ha)).sub_right (wSub hd L.big)

theorem ctx_hi {a n : Nat} (ha : a + n ≤ 256) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, N - 512⟩ :=
  (L.cw.sub_left (ctxSub ha)).sub_right (hiSub L.big)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP K).Disjoint ⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP K).Disjoint ⟨w64 St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 768) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (wSub ha L.big)

theorem stk_hi : (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 512, N - 512⟩ := L.kw.sub_right (hiSub L.big)

omit L in
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega_using [ha]) (by omega_using [hd])

omit L in
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 768) (hd : d + k ≤ 768) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega_using [ha]) (by omega_using [hd])

omit L in
/-- `w_w` for any offsets into a working space of 2560 bytes. -/
theorem w_wN {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega_using [ha]) (by omega_using [hd])

omit L in
/-- What is below `d` in `W` is apart from the bytes of `W` from `d` on. -/
theorem w_above {a n d : Nat} (h : a + n ≤ d) (hd : d ≤ 768) (hN : 768 ≤ N := by wbig)
    (hk : N < 2 ^ 64 := by wlt) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, N - d⟩ :=
  Offset.disjoint _ (.inl h) (by omega_using [h, hd]) (by omega_using [hd, hN, hk])

theorem ctx_above {a n d : Nat} (ha : a + n ≤ 256) (hd : d ≤ 768) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, N - d⟩ :=
  (L.cw.sub_left (ctxSub ha)).sub_right (aboveSub hd L.big)

theorem st_above {a n d : Nat} (ha : a + n ≤ 80) (h₁ : 96 ≤ d) (hd : d ≤ 768) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, N - d⟩ :=
  (L.sb.sub_left (stSub ha)).sub_right (Offset.sub _ h₁ (by have h₂ := L.big; omega_using [h₁, hd, h₂]))

theorem stk_above {d : Nat} (hd : d ≤ 768) : (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 d, N - d⟩ :=
  L.kw.sub_right (aboveSub hd L.big)

/-- What the functions keep in their own 512 bytes of `W`, and the working
space of the functions called. -/
theorem w_hi {a n : Nat} (ha : a + n ≤ 512) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, N - 512⟩ :=
  Offset.disjoint _ (.inl ha) (by omega_using [ha]) (by have h₁ := L.big; have h₂ := L.fw; omega_using [h₁, h₂])

/-! The same for any offsets into a working space of a literal size (`init`,
`open_to`, whose `vg_aes_ctr32_to` takes 2048 bytes whatever the implementation). -/

theorem st_wN {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ N)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (Offset.sub _ h₁ (by omega_using [h₁, h₂]))

theorem ctx_wN {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ N) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw.sub_left (ctxSub ha)).sub_right (wSubN hd)

theorem stk_wN {a n : Nat} (ha : a + n ≤ N) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (wSubN ha)

/-- The stack the calls use, at `esp = SP`. -/
theorem below_sub {k : Nat} (hk : k ≤ K) : Region.Sub (below SP k) (below SP K) :=
  VG.X86.below_sub hk L.sp

/-! ### Pointers into the regions, as the code computes them -/

theorem aW {o : Nat} (ho : o < 768) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have h₁ := L.fw; have h₂ := L.big; omega_using [ho, h₁, h₂])

theorem aWN {o : Nat} (ho : o < N) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have h₁ := L.fw; omega_using [ho, h₁])

theorem nWN {o : Nat} (ho : o < N) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have h₁ := L.fw; omega_using [ho, h₁])

theorem aS {o : Nat} (ho : o < 80) : w64 (St + BitVec.ofNat 32 o) = w64 St + BitVec.ofNat 64 o :=
  w64_add (by have := L.fs; omega_using [ho, this])

theorem aC {o : Nat} (ho : o < 256) : w64 (Ctx + BitVec.ofNat 32 o) = w64 Ctx + BitVec.ofNat 64 o :=
  w64_add (by have := L.fc; omega_using [ho, this])

theorem nW {o : Nat} (ho : o < 768) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have h₁ := L.fw; have h₂ := L.big; omega_using [ho, h₁, h₂])

theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o :=
  toNat_add32 (by have := L.fs; omega_using [ho, this])

theorem nC {o : Nat} (ho : o < 256) : (Ctx + BitVec.ofNat 32 o).toNat = Ctx.toNat + o :=
  toNat_add32 (by have := L.fc; omega_using [ho, this])

end Lay

namespace Env

variable {N : Nat} {Ctx St W SP : BitVec 32} {s : State} (E : Env N Ctx St W SP s)
include E

theorem stIn {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (w64 St + BitVec.ofNat 64 d) n :=
  in_off E.stW h (by decide)

theorem stIn' {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (w64 St + BitVec.ofNat 64 d) n :=
  in_left (E.stIn h)

theorem wIn {d n : Nat} (h : d + n ≤ 768) (hN : 768 ≤ N := by wbig) (hk : N < 2 ^ 64 := by wlt) :
    InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off E.wW (Nat.le_trans h hN) hk

theorem wIn' {d n : Nat} (h : d + n ≤ 768) (hN : 768 ≤ N := by wbig) (hk : N < 2 ^ 64 := by wlt) :
    InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (E.wIn h hN hk)

theorem wInN {d n : Nat} (h : d + n ≤ N) (hk : N < 2 ^ 64 := by wlt) :
    InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off E.wW h hk

theorem wCN {d n : Nat} (h : d + n ≤ N) (hk : N < 2 ^ 64 := by wlt) :
    Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off E.wW h hk

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨w64 St + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off E.stW h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 768) (hN : 768 ≤ N := by wbig) (hk : N < 2 ^ 64 := by wlt) :
    Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off E.wW (Nat.le_trans h hN) hk

end Env

/-- An environment, after code that keeps `ebp`, `esi`, `esp`, the
permissions and the context's slot. -/
theorem Env.keep {N : Nat} {Ctx St W SP : BitVec 32} {s s' : State} (h : Env N Ctx St W SP s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32) :
    Env N Ctx St W SP s' :=
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
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])) (by decide)

/-! ## Arithmetic -/

theorem ofNat_add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega_using [h, ha]), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega_using [ha])]
  omega_using [h, ha]

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
  omega_using []

theorem shr4 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 4 = BitVec.ofNat 32 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hn])]

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
  rw [runBlock_app, h₁]; exact h₂

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Gcm.blocksAt m p 1 = [Spec.Gcm.blockAt m p] := by
  simp [Spec.Gcm.blocksAt]


/-- A state with its memory replaced, kept folded (as `State.setReg` is) so
that a store does not copy the state into every field of a structure. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (setMem s (s.mem.writeW a v)) else none := rfl

theorem store8_eq (s : State) (a : Addr) (v : Byte) :
    s.store8 a v = if InRegions s.wr a 1 then some (setMem s (s.mem.writeW a v)) else none := rfl

theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem rd_setMem (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
theorem wr_setMem (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
theorem cf_setMem (s : State) (m : Mem) : (setMem s m).cf = s.cf := rfl
theorem zf_setMem (s : State) (m : Mem) : (setMem s m).zf = s.zf := rfl

/-- Runs a block of the instructions the AES-GCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
tactic_template "xrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
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
tactic_template "regs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := decide) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
                     $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
tactic_template "mems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
                     rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
                     zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
                     gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, stO, tO, uO,
                     ctxO, roundsO, alO, ahO, xlO, xhO, dataO, lenO, aadO, tglO, auxO, zO, nlO, vO, rO, tpO, dO, nO, bO, scrO,
                     Nat.reduceAdd, $ts,*]))

end VG.Proof.AesGcm.X86
