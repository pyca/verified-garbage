module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundLoop
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: the complete uniform primality policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

theorem roundInit_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) :
    WP isa (.block roundInit) s fun t => t.mem = s.mem.writeW (off p.O (8 * oIndex)) (0#64) ∧
      Keep [.rax, .rcx] s t := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem.writeW (off p.O (8 * oIndex)) (0#64))
    ?_ rfl) fun t ⟨hm, k⟩ => ⟨hm, k⟩
  xrun [roundInit, State.ea, hdr, h.ready.good.rdi, hdrOff, ws, h.link,
    h.ready.good.scr.ld (d := 8 * sLink) p.space_bounds.2.1, houter.st (d := 8 * oIndex) (by decide)]
  rfl

theorem rounds_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used checks : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hpos : 0 < checks) (hc32 : checks < 2 ^ 31) :
    WP isa (rounds M.mm K.run) s (RoundsPost p rp used bs checks s) := by
  unfold rounds
  refine WP.seq (WP.mono (roundInit_ok h) fun u ⟨hm, k⟩ => ?_)
  have hf : Frm p.O [(8 * oIndex, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have hlo : ∀ r ∈ [(8 * oIndex, 8)], 136 ≤ r.1 := by simp [oIndex]
  have hhi : ∀ r ∈ [(8 * oIndex, 8)], r.1 + r.2 ≤ 256 := by simp [oIndex]
  have hu := h.outer_frame hf hlo hhi k ((k.gpr (by decide)).trans h.ready.good.rdi)
  have hi : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 0 := by
    rw [hm]; exact word_writeW_self _ _ _ _
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by
    rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact hc
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hs : RoundSaved p s.mem u.mem := by
    intro j hj _ _ _ h18 _
    rw [hm]
    exact hdrStore_hdr _ _ _ (by decide) hj (Ne.symm h18)
  have hfr : RoundFrame p (s.gpr .rsp) s.mem u.mem :=
    (DrawFrame.of_scr (InScr.of_frm hf (fun r hr => Nat.le_trans (hhi r hr) p.space_bounds.1))).round
  refine WP.mono (roundsLoop_ok M K hu (hroom.congr hsp) hi hcu hpos (by omega) hc32)
    fun t ⟨consumed, hcons, ht, hr, hs', hf', kt⟩ => ?_
  rw [hsp] at hf'
  exact ⟨consumed, hcons, ht, hr, hs.trans hs', hfr.trans hf', (k.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
