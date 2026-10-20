module

import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.Pow
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: public Montgomery precomputation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Initialize the public operands expected by RSA's R² implementation. -/
theorem r2Head_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block r2Head) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.mem = s.mem ∧ Keep [.r12, .r10] s t := by
  have hW := hdr_lt_slot w 8 (show sW < 32 by decide)
  have hN := hdr_lt_slot w 8 (show sArr aN < 32 by decide)
  exact WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.mem = s.mem)
    (by unfold r2Head; xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sW) (by omega),
      h.scr.ld (d := 8 * sArr aN) (by omega), h.hdr.hw, h.hdr.harr aN (by decide)]) rfl)
    fun _ ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- R² for p, using any verified RSA precomputation implementation. -/
theorem r2_ctx (M : Mont) (R : R2Impl M) {s : State} {B : Addr} {Z k : Nat} {mi : BitVec 64}
    {pb : List Byte}
    (hc : SubCtx s B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals s B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k = true) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hZ : 128 * k + 256 ≤ Z) :
    WP isa (.seq (.block r2Head) R.code) s fun t =>
      ModCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      Frm (off B (inner ((k + 7) / 8))) (r2Ranges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨hodd, h1, hlo⟩ := valid_facts hval hk1
  have hroom := room_k hk1 hZ
  have hGn := hc.good.scr.nowrap
  refine WP.seq (WP.mono (r2Head_ok hc.good (Nat.le_refl _)) fun s₁ ⟨h12, h10, hm, k₁⟩ => ?_)
  have hg₁ : Good s₁ (off B (inner ((k + 7) / 8))) (slot ((k + 7) / 8) 8) ((k + 7) / 8) mi :=
    ⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.rdi, by rw [hm]; exact hc.hdr⟩
  refine WP.mono (R.ok hg₁ (Nat.le_refl _) (by omega) (by omega)
    (by rw [hm]; exact hv.n) (by rw [hm]; exact hv.inv) h12 h10 hodd hlo)
    fun t ⟨_, hlt, hr, f, kk⟩ => ?_
  have f' : Frm (off B (inner ((k + 7) / 8))) (r2Ranges ((k + 7) / 8)) s.mem t.mem := by rw [hm] at f; exact f
  have K := (k₁.trans kk).mono (show ∀ r ∈ [.r12, .r10] ++ mmRegs, r ∈ mmRegs by decide)
  have hr' : ∀ r ∈ r2Ranges ((k + 7) / 8), 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := fun r hr' => by
    refine ⟨?_, r2Ranges_le ((k + 7) / 8) r hr'⟩
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, aAcc, aTmp, aR2, sCnt, sFn] <;> omega
  refine ⟨⟨hc.of_frm f' hr' K.2.2 (K.gpr (by decide)),
    hv.of_frmA hGn (by omega) f' (fun r hr'' => ⟨?_, ?_⟩), hlt, hr, hodd, h1,
    by unfold inner at hroom ⊢; omega, by omega, by omega⟩, f', K⟩
  · exact (r2Ranges_arr _ (j := aN) (by decide) (by decide) (by decide) r hr'').symm
  · exact (r2Ranges_arr _ (j := aOne) (by decide) (by decide) (by decide) r hr'').symm

end VG.Proof.Ffdh.X86_64
