module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# SM4-GCM on AArch64: where everything is

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Env.lean`, whose tactics and lemmas on lengths and
registers this uses), but with SM4-GCM's key context (256 bytes at `Ctx`: the
schedule, then `H` at 128) and working space (768 bytes at `W`), and the
3264 bytes of stack below `SP` that the callees use (`stk SP`), apart from
them all (`Lay`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)

/-- The regions: the context, the state, the parts of `W`, and the stack
below `SP`. -/
structure Lay (Ctx St W SP : Addr) : Prop where
  cw : Ctx.toNat + 256 ≤ 2 ^ 64
  sw : St.toNat + 80 ≤ 2 ^ 64
  ww : W.toNat + 768 ≤ 2 ^ 64
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩
  cw' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 768⟩
  sa : (⟨St, 80⟩ : Region).Disjoint ⟨W, 16⟩
  sb : (⟨St, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 672⟩
  sp : 3264 ≤ SP.toNat
  kc : (stk SP).Disjoint ⟨Ctx, 256⟩
  ks : (stk SP).Disjoint ⟨St, 80⟩
  kw : (stk SP).Disjoint ⟨W, 768⟩

/-- What a state may access. -/
structure Perm (Ctx St W : Addr) (s : State) : Prop where
  ctx : Covers [⟨Ctx, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨St, 80⟩] s.wr
  w : Covers [⟨W, 768⟩] s.wr

/-- The registers holding the context, the state and `W`, the stack
pointer, and what the state may access. -/
structure Env (Ctx St W SP : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = St
  x21 : s.gpr .x21 = Ctx
  sp : s.sp = SP
  perm : Perm Ctx St W s

theorem Perm.of_eq {Ctx St W : Addr} {s s' : State} (h : Perm Ctx St W s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm Ctx St W s' := by
  obtain ⟨a, b, c⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact c⟩

/-- An environment, after code that keeps `x19`–`x21`, the stack pointer and
the permissions. -/
theorem Env.keep {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

theorem Env.of_regs {Ctx St W SP : Addr} {s s' : State} {rs : List Reg} (h : Env Ctx St W SP s) (hr : Regs rs s s')
    (hd : ∀ r ∈ [Reg.x19, .x20, .x21], r ∉ rs := by decide) : Env Ctx St W SP s' :=
  h.keep (fun r h' => hr.others r (hd r h')) hr.sp hr.rd hr.wr

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {Ctx : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨Ctx + BitVec.ofNat 64 d, n⟩ ⟨Ctx, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {St : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ ⟨St, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 768) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 768⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 768) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 672⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 768)) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 768) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (ctxSub ha)).sub_right (wSub hd)

/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.sw; omega) (by have := L.sw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 768) (hd : d + k ≤ 768) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

/-- The callees' stack is apart from the parts of the context, the state
and `W`. -/
theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) : (stk SP).Disjoint ⟨Ctx + BitVec.ofNat 64 a, n⟩ :=
  L.kc.sub_right (ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) : (stk SP).Disjoint ⟨St + BitVec.ofNat 64 a, n⟩ :=
  L.ks.sub_right (stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 768) : (stk SP).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.kw.sub_right (wSub ha)

end Lay

namespace Perm

variable {Ctx St W : Addr} {s : State} (P : Perm Ctx St W s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
  in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 d) n :=
  in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 768) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 768) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 768) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

end VG.Proof.Sm4Gcm.AArch64
