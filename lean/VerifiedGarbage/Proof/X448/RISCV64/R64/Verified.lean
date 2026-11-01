module

import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.RISCV64.Bits
public import VerifiedGarbage.Proof.X448.RISCV64.Setup
public import VerifiedGarbage.Proof.X448.RISCV64.Main
public import VerifiedGarbage.Impl.X448.RISCV64.R64
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.RISCV64.R64.CT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# X448 on RISC-V, 64-bit limbs: verified

The whole function: `vg_x448` writes `X448(k, u)` to `out`
(`x448_correct`), against `Proof/X448/RISCV64/Main.lean`'s contract, with
that file's decoding, bits and final reduction, and meets the shared
contract of `Spec/X448/Contract.lean`: the code calls no function and writes
only caller-saved registers (`WP.keep`), so the ABI's obligations hold of
every execution.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64


section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (X1 X2 Z2 X3 Z3 R BITS)
open VG.Proof.X448.RISCV64 (FS SlotsOk SlotsOk.mono SlotsOk.bits swapV LQ ladV IQ XPre wsB wsB_sub setup_ok
  bits_ok freeze_ok bytesAt_frame uOf cswap_fst iteT x448RISCV64)
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_swap_le)

section
variable {b : Addr}

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .t2 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have hr2 : Rest [.t0] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e11 : s2.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

end

theorem x448_correct {s : State} (hp : XPre s) :
    WP isa x448 s fun s' => x448RISCV64.post s s' := by
  have hB : BITS = 1064 := rfl
  have hsc_in : (⟨s.gpr .a1, 56⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  have hsub : Region.Sub ⟨wsB s, 2048⟩ ⟨s.gpr .a3, 8192⟩ := by
    have := wsB_sub s (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero] at this
  unfold x448
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .a1 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    (hp.sc_ws.sub_right hsub)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h0, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h0 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) hc5 hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : R64.Stp (wsB s) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have h3' : s6.gpr .a0 = s.gpr .a0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), hr1.gpr _ (by decide)]
  have hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  have hc6 : Ctx (wsB s) s6 := hc5.of_rest hr6 (by decide)
  refine WP.mono (freeze_ok hc6 h3'
    (fun k hk => in_base (len := 56) (by rw [hwr6, hp.wr]; simp) (by omega) (by omega)) (hp.out_ws.sub_right hsub).symm)
    fun s7 ⟨hbytes, _, _⟩ => ?_
  -- The result.
  show bytesAt s7.mem _ 56 = _
  rw [hbytes, VG.Proof.X448.x448_eq]
  -- The scalar, as read by `bits`.
  have hk : bytesAt s1.mem (s.gpr .a1) 56 = bytesAt s.mem (s.gpr .a1) 56 :=
    bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  have e6 : FS s6.mem (wsB s) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X448.toFe_val, ← VG.Proof.X448.encodeUCoordinate_eq]
  change VG.Spec.X448.encodeUCoordinate (FS s6.mem (wsB s) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X448.invert_eq, VG.Proof.X448.pow_pw, cswap_fst,
    uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end

section

open VG VG.RISCV64
open VG.Proof.X448.RISCV64 (x448RISCV64 XPre.of)

theorem x448_ok (s : State) (hs : x448RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X448.RISCV64.R64.x448 s t s' ∧ abiPreserved s s' ∧ x448RISCV64.post s s' := by
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (x448_correct (XPre.of hs)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

theorem x448_ct' : ConstantTime isa x448RISCV64.pre x448RISCV64.pub Impl.X448.RISCV64.R64.x448 :=
  x448_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x448Sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_verified :
    Verified RISCV64.target Impl.X448.RISCV64.R64.x448 (Spec.X448.x448Contract RISCV64.abi) :=
  Verified.of_correct x448_ok x448_ct' (by
    contract_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.RISCV64.x448RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X448.RISCV64.R64.x448Sat] using Proof.X448.RISCV64.R64.x448Sat)

end

end VG.Proof.X448.RISCV64.R64
