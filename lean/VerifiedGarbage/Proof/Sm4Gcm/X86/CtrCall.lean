module
public import VerifiedGarbage.Proof.AesGcm.X86.CtrCall
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Lay
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State


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
  refine ⟨h.eax, h.edx, h.ebx, h.edi, by rw [h.esp]; have := L.sp; omega,
    h.kC.sub_left (Region.sub_prefix (by decide)), h.kD.sub_left (Region.sub_prefix (by decide)), h.cd,
    by rw [hsp]; subst hK; exact L.kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact h.bC, by rw [hsp]; exact h.bD, by have := L.fc; omega, h.fC, h.fD,
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
