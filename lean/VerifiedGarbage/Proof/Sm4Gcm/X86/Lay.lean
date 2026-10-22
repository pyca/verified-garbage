module
public import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on x86: the stack the calls use

Untrusted: everything here is checked by Lean. SM4-GCM's functions share
AES-GCM's layout (`Proof/AesGcm/X86/Env.lean`): its pieces that only hash
or compare run with `Lay Ctx St W SP 28`, the 28 bytes below `SP` its
calls use. A call of `vg_sm4_ctr32` uses `K` (1536) bytes below `SP`, apart
from the context, the state and `W` too (`Lay4`); what a piece of AES-GCM
leaves below `SP` is within them (`Lay4.below28`), and data apart from them
is apart from AES-GCM's (`DataOk.mono`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.Proof.AesGcm.X86

/-- AES-GCM's layout, with the `K` bytes below `SP` apart from the context,
the state and `W`. -/
structure Lay4 (Ctx St W SP : BitVec 32) (K : Nat) : Prop where
  lay : Lay Ctx St W SP 28
  k28 : 28 ≤ K
  sp : K ≤ SP.toNat
  kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩
  ks : (below SP K).Disjoint ⟨w64 St, 80⟩
  kw : (below SP K).Disjoint ⟨w64 W, 2560⟩

namespace Lay4

variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K)
include L

theorem fc : Ctx.toNat + 256 ≤ 2 ^ 32 := L.lay.fc
theorem fs : St.toNat + 80 ≤ 2 ^ 32 := L.lay.fs
theorem fw : W.toNat + 2560 ≤ 2 ^ 32 := L.lay.fw
theorem cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩ := L.lay.cs
theorem cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩ := L.lay.cw
theorem sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩ := L.lay.sa
theorem sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩ := L.lay.sb

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.st_w ha hd

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ := L.lay.ctx_st ha hd

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.ctx_w ha hd

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP K).Disjoint ⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (Lay.ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP K).Disjoint ⟨w64 St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (Lay.stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (Lay.wSub ha)

/-- The stack the calls use, at `esp = SP`. -/
theorem below_sub {k : Nat} (hk : k ≤ K) : Region.Sub (below SP k) (below SP K) :=
  VG.X86.below_sub hk L.sp

/-- What AES-GCM's pieces use below `SP` is within it. -/
theorem below28 : Region.Sub (below SP 28) (below SP K) := L.below_sub L.k28

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := L.lay.aW ho
theorem aS {o : Nat} (ho : o < 80) : w64 (St + BitVec.ofNat 32 o) = w64 St + BitVec.ofNat 64 o := L.lay.aS ho
theorem aC {o : Nat} (ho : o < 256) : w64 (Ctx + BitVec.ofNat 32 o) = w64 Ctx + BitVec.ofNat 64 o := L.lay.aC ho
theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o := L.lay.nW ho
theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o := L.lay.nS ho
theorem nC {o : Nat} (ho : o < 256) : (Ctx + BitVec.ofNat 32 o).toNat = Ctx.toNat + o := L.lay.nC ho

end Lay4

/-- The layout, from its regions' bounds and disjointness. -/
theorem Lay4.of {Ctx St W SP : BitVec 32} {K : Nat} (fc : Ctx.toNat + 256 ≤ 2 ^ 32)
    (fs : St.toNat + 80 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) (k28 : 28 ≤ K) (sp : K ≤ SP.toNat)
    (cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩) (cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩)
    (sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩)
    (kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩) (ks : (below SP K).Disjoint ⟨w64 St, 80⟩)
    (kw : (below SP K).Disjoint ⟨w64 W, 2560⟩) : Lay4 Ctx St W SP K :=
  have hb := VG.X86.below_sub (sp := SP) k28 sp
  ⟨⟨fc, fs, fw, by decide, Nat.le_refl _, by omega, cs, cw, sa, sb, kc.sub_left hb, ks.sub_left hb,
    kw.sub_left hb⟩, k28, sp, kc, ks, kw⟩

/-- Data apart from the `K` bytes below `SP` is apart from the `k ≤ K`. -/
theorem DataOk.mono {St W SP : BitVec 32} {K k : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataOk St W SP K s D n) (hk : k ≤ K) (hsp : K ≤ SP.toNat) : DataOk St W SP k s D n :=
  { h with stk := h.stk.sub_left (VG.X86.below_sub hk hsp) }

end VG.Proof.Sm4Gcm.X86
