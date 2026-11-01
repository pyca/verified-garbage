module
public import VerifiedGarbage.Proof.MillerRabin.Keeps
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerSave

import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.Framework.Offset

/-! # The actual x86-64 shared call preserves its RSA caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

def callRanges (w : Nat) : List (Nat × Nat) := [(pad w, 8)] ++ mutRanges Proof.MillerRabin.Round.extended w

private theorem outside_mm (r : Reg) (hr : r ∉ mmRegs) : r = .rdi ∨ r = .rsp := by
  cases r <;> simp_all [mmRegs]

private theorem callee_outside {r : Reg} (hr : r ∈ calleeSaved) (hne : r ≠ .rbx) :
    r ∉ [.rax, .rbx, .rcx, .rdx, .rsi] ∧ r ∉ [.rax, .rbx, .rcx, .rdi] := by
  cases r <;> simp_all [calleeSaved]

theorem call_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call v.name v.code) s fun t =>
      t.gpr .rdi = B ∧ word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) := by
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hN : 8 * callWords w ≤ 2 ^ 64 := by omega_arith
  have hpZ : pad w + 8 ≤ 8 * callWords w := by
    simp only [pad, slot, hdrBytes, aR1, callWords]
    omega_arith
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  refine WP.seq (WP.mono (save_ok hc.good hZ) ?_)
  rintro u ⟨hm, hb, hsi, hskeep⟩
  obtain ⟨hcu, heu⟩ := save_context hc he hd hm hskeep
  have hsp : u.gpr .rsp = s.gpr .rsp := hskeep.gpr (by decide)
  have hru : Room u B Z := by
    exact ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  have hxu : wv u.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c := by
    rw [hm, (saved_outside s B w (by omega_arith)).wv
      (Or.inl (by simp only [pad, slot, hdrBytes, aR1, aXm]; omega_arith))
      (by have := hd.w128; simp only [slot, hdrBytes, aXm]; omega_arith)]
    exact hx
  refine WP.seq (WP.mono (round_call_ok v hcu heu hd hZ hru hsi ho h3 hxu) ?_)
  rintro t ⟨hcs, hrd, hwr, hf, hv, hk, _⟩
  have htScr := hcu.good.scr.congr hwr
  have htw : word t.mem B (8 * sW) = BitVec.ofNat 64 w :=
    (kept_header hk (by unfold callWords; omega_arith) (by decide) (by decide)).trans hcu.good.hdr.hw
  have htbx : word t.mem B (pad w) = s.gpr .rbx := by
    rw [kept_padding hk hpZ, hm, saved_rbx]
  refine WP.mono (restore_ok htScr hZ ((hcs .rbx (by simp [calleeSaved])).trans hb) htw htbx hv) ?_
  rintro f ⟨hfm, hB, hOld, hfkeep⟩
  have hflag : word f.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) := by
    rw [hfm, word_writeW_self]
  have hfFinal : Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) u.mem f.mem := by
    rw [hsp] at hf
    rw [hfm]
    exact hf.writeW (r := ⟨B, 8 * callWords w⟩) (by simp) _
      (Offset.contains_base B (by simp only [kFlag, kPlen, sFn]; unfold callWords; omega_arith) (by decide))
  have hkFinal : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B (callWords w) w u.mem f.mem := by
    rw [hfm]
    exact keeps_write_flag hk hN (by decide) _
  have hSave : Frm B [(pad w, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (saved_outside s B w (by omega_arith)) (by simp)
  have hFrame : WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem f.mem :=
    (hSave.work.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((keeps_to_work hkFinal hfFinal).mono (fun r hr => List.mem_append_right _ hr))
  have hSP : f.gpr .rsp = s.gpr .rsp :=
    ((hfkeep.gpr (by decide)).trans (hcs .rsp (by simp [calleeSaved]))).trans hsp
  have hKeep : Keep mmRegs s f := by
    refine ⟨?_, hfkeep.2.1.trans (hrd.trans hskeep.2.1), hfkeep.2.2.trans (hwr.trans hskeep.2.2)⟩
    intro r hr
    rcases outside_mm r hr with rfl | rfl
    · exact hB.trans hc.good.rdi.symm
    · exact hSP
  refine ⟨hB, hflag, hFrame, hKeep, ?_⟩
  intro r hr
  by_cases h : r = .rbx
  · subst r
    exact hOld
  · have hh := callee_outside hr h
    exact ((hfkeep.gpr hh.2).trans (hcs r hr)).trans (hskeep.gpr hh.1)

end VG.Proof.MillerRabin.X86_64.Caller
