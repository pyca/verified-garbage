module

public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! IA-32 caller layout for the AES-GCM gather contract. -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub_toNat32 {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) : (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
    show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

theorem w64_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    w64 (x - BitVec.ofNat 32 k) = w64 x - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_w64, sub_toNat32 hk, BitVec.toNat_sub, toNat_w64, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by have := x.isLt; omega_arith)]
  have := x.isLt
  rw [show 2 ^ 64 - k + x.toNat = (x.toNat - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

/-- The bottom of the stack reserved by the public gather contract. -/
abbrev Bs (s : State) : Addr := w64 (s.gpr .esp) - BitVec.ofNat 64 2688

structure Lay (s : State) : Prop where
  rd : s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s
  wr : s.wr = [dR s, tgR s, argR s]
  kd : (kR s).Disjoint (dR s)
  kt : (kR s).Disjoint (tgR s)
  nd : (nR s).Disjoint (dR s)
  nt : (nR s).Disjoint (tgR s)
  ad : (aR s).Disjoint (dR s)
  at_ : (aR s).Disjoint (tgR s)
  dt : (dR s).Disjoint (tgR s)
  dds : (dR s).Disjoint (dsR s)
  dls : ∀ r ∈ lsR s, (dR s).Disjoint r
  ed : (retR s).Disjoint (dR s)
  et : (retR s).Disjoint (tgR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tgR s)
  bds : (stkR s).Disjoint (dsR s)
  bls : ∀ r ∈ lsR s, (stkR s).Disjoint r
  ok : (K s).toNat + 256 ≤ 2 ^ 32
  on : (Nn s).toNat + NL s ≤ 2 ^ 32
  oa : (Ad s).toNat + AL s ≤ 2 ^ 32
  od : (Dst s).toNat + L s ≤ 2 ^ 32
  ot : (Tg s).toNat + 16 ≤ 2 ^ 32
  ods : (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32
  ol : ∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32
  w₁ : 2688 ≤ (s.gpr .esp).toNat
  hR : (arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14
  hgl : gl s (Cnt s) = L s
  hBn : (Bs s).toNat + 2736 ≤ 2 ^ 32
  hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 2688

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  sig_split hs
  rename_i rd wr kd kt hdrop4 nd nt hdrop7 ad at_ hdrop10 dt dds dls hdrop14 hdrop15 hdrop16 hdrop17 hdrop18
    hdrop19 hdrop20 hdrop21 hdrop22 ed et hdrop25 hdrop26 hdrop27 bk bn ba bd bt bds bls hdrop35 ok on oa od
    ot ods ol w₁ w₂ hR
  clear hdrop4 hdrop7 hdrop10 hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop25
    hdrop26 hdrop27 hdrop35
  have hgl := hs
  clear hs
  have hB : Bs s = w64 (s.gpr .esp - BitVec.ofNat 32 2688) := (w64_sub (by omega_arith)).symm
  have hBn : (Bs s).toNat = (s.gpr .esp).toNat - 2688 := by rw [hB, toNat_w64, sub_toNat32 (by omega_arith)]
  have hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 2688 := (BitVec.sub_add_cancel _ _).symm
  refine ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, ed, et, bk, bn, ba, bd, bt, bds, bls, ok, on, oa, od, ot,
    ods, ol, w₁, hR, hgl, by omega_arith, hE⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2688) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2688⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 2692, 44⟩ := by
  show (⟨w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)), 44⟩ : Region) = _
  have hb : (Bs s).toNat=(s.gpr .esp).toNat-2688 := by
    have b : Bs s = w64 (s.gpr .esp - BitVec.ofNat 32 2688) := (w64_sub h.w₁).symm
    rw [b,toNat_w64,sub_toNat32 h.w₁]
  have bound := h.hBn
  rw [hb] at bound
  have low := h.w₁
  rw [w64_add (by omega_arith), h.hE, Offset.add_ofNat_add_ofNat]

end Lay
end VG.Proof.AesGcm.X86.Gather
