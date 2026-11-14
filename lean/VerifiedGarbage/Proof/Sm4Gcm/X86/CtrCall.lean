module
public import VerifiedGarbage.Proof.AesGcm.X86.CtrCall
public import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-! ### `Sm4Gcm.X86.Lay`, which only this module used -/

section

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
theorem sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩ := L.lay.sb

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.st_w ha hd

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.ctx_w ha hd

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
theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o := L.lay.nW ho
theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o := L.lay.nS ho
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
  ⟨⟨fc, fs, fw, by decide, by decide, by omega_using [k28, sp], cs, cw, sa, sb, kc.sub_left hb, ks.sub_left hb,
    kw.sub_left hb⟩, k28, sp, kc, ks, kw⟩

/-- Data apart from the `K` bytes below `SP` is apart from the `k ≤ K`. -/
theorem DataOk.mono {St W SP : BitVec 32} {K k : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataOk St W SP K s D n) (hk : k ≤ K) (hsp : K ≤ SP.toNat) : DataOk St W SP k s D n :=
  { h with stk := h.stk.sub_left (VG.X86.below_sub hk hsp) }

end VG.Proof.Sm4Gcm.X86

end

end



/-!
# SM4-GCM on x86: calling `vg_sm4_ctr32` from the pieces

Untrusted: everything here is checked by Lean. The arguments of
`vg_sm4_ctr32` in their registers (`CtrReady`): the key schedule at the
context, a counter block `C` and `nb` blocks at `Dp`; the call (`ctrW_ok`,
`CtrOut`) and its constant time (`ctrW_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)

/-- The cipher of the key schedule in the context. -/
abbrev ciphOf (m : Mem) (Ctx : BitVec 32) : Block → Block :=
  Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt m (w64 Ctx))

theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Ctx : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 Ctx, 256⟩ : Region).Disjoint r) :
    ciphOf m' Ctx = ciphOf m Ctx := by
  simp only [ciphOf]
  rw [scheduleAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))]

/-- The call of `vg_sm4_ctr32`. -/
abbrev ctrW : Prog isa := ctrCall

/-- Ready for `ctrW`: the arguments of `vg_sm4_ctr32` in their registers. -/
structure CtrReady (Ctx St W SP : BitVec 32) (C Dp : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = Dp
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * nb ≤ 2 ^ 32
  wC : Covers [⟨w64 C, 16⟩] s.wr
  wD : Covers [⟨w64 Dp, 16 * nb⟩] s.wr
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  kC : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kD : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  bC : (below SP 1536).Disjoint ⟨w64 C, 16⟩
  bD : (below SP 1536).Disjoint ⟨w64 Dp, 16 * nb⟩
  pC : (keptR W).Disjoint ⟨w64 C, 16⟩
  pD : (keptR W).Disjoint ⟨w64 Dp, 16 * nb⟩

/-- What `ctrW` leaves. -/
structure CtrOut (Ctx St W SP : BitVec 32) (C Dp : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : Env Ctx St W SP s'
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 Dp, 16 * nb⟩, below SP 1536] s.mem s'.mem
  out : blocksAt s'.mem (w64 Dp) nb = ctr32 (ciphOf s.mem Ctx) (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 Dp) nb)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 nb (blockAt s.mem (w64 C))
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) (hK : K = 1536)
include L hK

theorem CtrReady.call {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) : CtrCall s Ctx C Dp nb := by
  have hsp : below (s.gpr .esp) 1536 = below SP 1536 := by rw [h.esp]
  refine ⟨h.eax, h.edx, h.ebx, h.edi, by rw [h.esp]; have := L.sp; omega_using [hK, this],
    h.kC.sub_left (Region.sub_prefix (by decide)), h.kD.sub_left (Region.sub_prefix (by decide)), h.cd,
    by rw [hsp]; subst hK; exact L.kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact h.bC, by rw [hsp]; exact h.bD, by have := L.fc; omega_using [this], h.fC, h.fD,
    covers_pre h.ctxR (by decide) (by decide), covers_cons h.wC (covers_cons h.wD covers_nil)⟩

theorem CtrReady.kept {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) :
    ∀ r ∈ [(⟨w64 C, 16⟩ : Region), ⟨w64 Dp, 16 * nb⟩, below SP 1536], (keptR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.pC
  · exact h.pD
  · subst hK; exact (L.stk_w (by decide)).symm

theorem ctrW_ok {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) :
    WP isa ctrW s (CtrOut Ctx St W SP C Dp nb s) := by
  refine WP.mono (ctr_call (h.call L hK)) fun s₁ g => ?_
  have gf := g.frame
  have hsp : below (s.gpr .esp) 1536 = below SP 1536 := by rw [h.esp]
  rw [hsp] at gf
  have hk := h.kept L hK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, gf, g.out, g.ctr, g.saved .ebx (by decide), g.saved .edi (by decide),
    g.rd, g.wr⟩
  · rw [g.saved .ebp (by decide), h.ebp]
  · rw [g.saved .esi (by decide), h.esi]
  · rw [g.saved .esp (by decide), h.esp]
  · rw [g.rd, g.wr]; exact h.ctxR
  · rw [g.wr]; exact h.stW
  · rw [g.wr]; exact h.wW
  · rw [ctx_frame gf hk, h.ctx]

theorem ctrW_ct {C Dp : BitVec 32} {nb : Nat} : CT (CtrReady Ctx St W SP C Dp nb) ctrW :=
  ctr_ct (E := SP) fun _ h => ⟨h.call L hK, h.esp⟩

end

end VG.Proof.Sm4Gcm.X86
