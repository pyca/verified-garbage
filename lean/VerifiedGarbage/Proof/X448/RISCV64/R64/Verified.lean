module

public import VerifiedGarbage.Proof.X448.Contract
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
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# X448 on RISC-V, 64-bit limbs: verified

The whole function: `vg_x448` writes `X448(k, u)` to `out`
(`x448_correct`), against `Proof/X448/RISCV64/Main.lean`'s contract, with
that file's decoding, bits and final reduction, and meets the shared
contract of `Spec/X448/Contract.lean`. Both entry points call the same tail,
keeping the return address in the unused end of their scratch area. The
proofs establish its preservation as well as the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64


section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (X1 X2 Z2 X3 Z3 R BITS)
open VG.Proof.X448.RISCV64 (FS SlotsOk SlotsOk.mono SlotsOk.bits swapV LQ ladV IQ XPre wsB wsB_sub setup_ok
  setupBase_ok bits_ok freeze_ok bytesAt_frame uOf cswap_fst iteT x448RISCV64 x448BaseRISCV64)
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

/-- The code after the setup, from the ladder's initial state for the
u-coordinate `pb` in the working space at `a3` of `s`. -/
theorem tail_correct {s s1 : State} {pb : List Byte}
    (hsc_in : (⟨s.gpr .a1, 56⟩ : Region) ∈ s.rd ++ s.wr) (hout : (⟨s.gpr .a0, 56⟩ : Region) ∈ s.wr)
    (sc_ws : Region.Disjoint ⟨s.gpr .a1, 56⟩ ⟨s.gpr .a3, 8192⟩)
    (out_ws : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a3, 8192⟩)
    (hc1 : Ctx (wsB s) s1) (hf1 : Frame [⟨s.gpr .a3, 8192⟩] s.mem s1.mem)
    (hS1 : SlotsOk s1.mem (wsB s) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate pb))
      (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate pb)))))
    (hr1 : Rest [.a2, .a3, .a4, .a5, .ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s s1) :
    WP isa tail s1 fun s' =>
      bytesAt s'.mem (s.gpr .a0) 56 = VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .a1) 56) pb ∧
      Ctx (wsB s) s' ∧ Frame [⟨wsB s, 1512⟩, ⟨s.gpr .a0, 56⟩] s1.mem s'.mem ∧
      Rest work s1 s' := by
  have hB : BITS = 1064 := rfl
  have hsub : Region.Sub ⟨wsB s, 2048⟩ ⟨s.gpr .a3, 8192⟩ := by
    have := wsB_sub s (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero] at this
  unfold tail
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .a1 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    (sc_ws.sub_right hsub)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
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
    (fun k hk => in_base (len := 56) (by rw [hwr6]; exact hout) (by omega) (by omega)) (out_ws.sub_right hsub).symm)
    fun s7 ⟨hbytes, hr7, hf7, _⟩ => ?_
  refine ⟨?_, hc6.of_rest hr7 (by decide), ?_,
    (hr2.mono (by decide)).trans (hst6.rest.trans (hr7.mono (by decide)))⟩
  swap
  · have f2 : Frame [⟨wsB s, 1512⟩, ⟨s.gpr .a0, 56⟩] s1.mem s2.mem :=
      hf2.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨⟨wsB s, 1512⟩, by simp, Offset.sub_base _ (by decide)⟩
    have f6 : Frame [⟨wsB s, 1512⟩, ⟨s.gpr .a0, 56⟩] s2.mem s6.mem :=
      hst6.frame.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        refine ⟨⟨wsB s, 1512⟩, by simp, ?_⟩
        simpa only [VG.Proof.X448.RISCV64.FA, VG.Impl.X448.RISCV64.ACC, BitVec.add_zero] using
          (Offset.sub_base (wsB s) (d := 0) (n := 1064) (k := 1512) (by decide))
    have f7 : Frame [⟨wsB s, 1512⟩, ⟨s.gpr .a0, 56⟩] s6.mem s7.mem :=
      hf7.sub fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨⟨wsB s, 1512⟩, by simp, Offset.sub_base _ (by decide)⟩
        · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, fun _ h => h⟩
    exact f2.trans (f6.trans f7)
  -- The result.
  rw [hbytes, VG.Proof.X448.x448_eq]
  -- The scalar, as read by `bits`.
  have hk : bytesAt s1.mem (s.gpr .a1) 56 = bytesAt s.mem (s.gpr .a1) 56 :=
    bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  have e6 : FS s6.mem (wsB s) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X448.toFe_val, ← VG.Proof.X448.encodeUCoordinate_eq]
  change VG.Spec.X448.encodeUCoordinate (FS s6.mem (wsB s) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X448.invert_eq, VG.Proof.X448.pow_pw, cswap_fst,
    X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

/-- Calls the common tail, keeping the return address in the unused last
doubleword of the aligned working area. -/
theorem tailCall_correct {s s1 : State} {pb : List Byte}
    (hsc_in : (⟨s.gpr .a1, 56⟩ : Region) ∈ s.rd ++ s.wr) (hout : (⟨s.gpr .a0, 56⟩ : Region) ∈ s.wr)
    (sc_ws : Region.Disjoint ⟨s.gpr .a1, 56⟩ ⟨s.gpr .a3, 8192⟩)
    (out_ws : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a3, 8192⟩)
    (hc1 : Ctx (wsB s) s1) (hf1 : Frame [⟨s.gpr .a3, 8192⟩] s.mem s1.mem)
    (hS1 : SlotsOk s1.mem (wsB s) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate pb))
      (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate pb)))))
    (hr1 : Rest [.a2, .a3, .a4, .a5] s s1) :
    WP isa tailCall s1 fun s' =>
      bytesAt s'.mem (s.gpr .a0) 56 = VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .a1) 56) pb ∧
      abiPreserved s s' := by
  unfold tailCall
  refine WP.seq (wp_sd (by decide) (by rw [hc1.a3]) (al8 hc1.al (by decide))
    (hc1.inW (by decide)) fun s2 u2 => WP.block_nil ?_)
  have hc2 : Ctx (wsB s) s2 := hc1.of_rest (u2.rest []) (by decide)
  have fs : Frame [⟨wsB s + BitVec.ofNat 64 2040, 8⟩] s1.mem s2.mem := by
    rw [u2.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains])
  have f2 : Frame [⟨s.gpr .a3, 8192⟩] s.mem s2.mem := hf1.trans (fs.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, wsB_sub s (by decide)⟩)
  have slots : SlotsOk s2.mem (wsB s) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate pb))
      (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate pb)))) := by
    intro q hq
    have hq' : q + 56 ≤ 1064 := by
      have : ∀ q ∈ LQ, q + 56 ≤ 1064 := by decide
      exact this q hq
    have e := VG.Proof.X448.RISCV64.limb_frame fs (o := q) fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint (wsB s) (e := 2040) (.inl (by omega)) (by omega) (by decide)
    rw [VG.Proof.X448.RISCV64.FS, VG.Proof.X448.RISCV64.V, val32_congr e]
    exact hS1 q hq
  have rc : Rest [.a2, .a3, .a4, .a5, .ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s s2.callEntry := by
    refine ⟨?_, u2.rd.trans hr1.rd, u2.wr.trans hr1.wr, u2.sp.trans hr1.sp⟩
    intro r hr
    rw [State.callEntry_gpr s2 (by cases r <;> simp_all [linkRegs]), u2.gpr,
      hr1.gpr r (fun h => hr (by simp_all))]
  have cc : Ctx (wsB s) s2.callEntry := ⟨hc2.a3, hc2.al, hc2.wr⟩
  obtain ⟨t, s3, he, hres, hc3, hf3, hr3⟩ := tail_correct hsc_in hout sc_ws out_ws cc f2 slots rc
  have hra : s3.gpr .ra = s2.callEntry.gpr .ra := hr3.gpr _ (by decide)
  have hret : isa.ret s2.callEntry s3 = some s3 := by
    simp only [isa, ret, hra, ↓reduceIte]
  refine WP.seq ⟨_, s3, Exec.call (call_callEntry s2) he hret, ?_⟩
  have saved : s3.mem.readW (wsB s + BitVec.ofNat 64 2040) 64 = s.gpr .ra := by
    rw [hf3.readW (r := ⟨wsB s + BitVec.ofNat 64 2040, 8⟩) (by simp [Region.Contains]) ?_ (by decide),
      State.callEntry_mem, u2.mem, Mem.readW_writeW_self64, hr1.gpr _ (by decide)]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Offset.disjoint_base (wsB s) (by decide) (by decide)
    · rw [List.mem_singleton.mp hr]
      exact (out_ws.sub_right (wsB_sub s (o := 2040) (n := 8) (by decide))).symm
  refine wp_ld (by decide) (by rw [hc3.a3]) (al8 hc3.al (by decide)) (hc3.inR (by decide))
    fun s4 u4 => WP.block_nil ⟨by rw [u4.mem]; exact hres, ?_,
      u4.sp.trans (hr3.sp.trans (u2.sp.trans hr1.sp)), u4.gpr.trans saved⟩
  have hp : ∀ r ∈ preserved, r ≠ Reg.ra ∧ r ∉ work ∧ r ∉ linkRegs ∧
      r ∉ [Reg.a2, .a3, .a4, .a5] := by decide
  intro r hr
  obtain ⟨hrr, hrw, hrl, hrs⟩ := hp r hr
  rw [u4.other r hrr, hr3.gpr r hrw, State.callEntry_gpr s2 hrl, u2.gpr, hr1.gpr r hrs]

theorem x448_correct {s : State} (hp : XPre s) :
    WP isa x448 s fun s' => x448RISCV64.post s s' ∧ abiPreserved s s' := by
  unfold x448
  exact WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ =>
    tailCall_correct (by rw [hp.rd]; simp) (by rw [hp.wr]; simp) hp.sc_ws hp.out_ws hc1 hf1 hS1 hr1)

/-- `vg_x448_base`'s precondition, by field. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 56⟩]
  wr : s.wr = [⟨s.gpr .a0, 56⟩, ⟨s.gpr .a2, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a1, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a2, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .a1, 56⟩ ⟨s.gpr .a2, 8192⟩

theorem x448Base_correct {s : State} (hp : BPre s) :
    WP isa x448Base s fun s' => x448BaseRISCV64.post s s' ∧ abiPreserved s s' := by
  unfold x448Base
  refine WP.seq ?_
  rw [List.singleton_append]
  refine wp_addi (imm := 0) (by decide) fun s0 u0 => ?_
  have e0 : s0.gpr .a3 = s.gpr .a2 := by rw [u0.gpr]; exact BitVec.add_zero _
  have a0 : s0.gpr .a0 = s.gpr .a0 := u0.other _ (by decide)
  have a1 : s0.gpr .a1 = s.gpr .a1 := u0.other _ (by decide)
  refine WP.mono (setupBase_ok (by rw [e0, u0.wr, hp.wr]; simp)) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_
  refine WP.mono (tailCall_correct (s := s0) (by rw [a1, u0.rd, hp.rd]; simp) (by rw [a0, u0.wr, hp.wr]; simp)
    (by rw [a1, e0]; exact hp.sc_ws) (by rw [a0, e0]; exact hp.out_ws) hc1 hf1 hS1 hr1) fun s' ⟨h, ha⟩ => ?_
  have hp : ∀ r ∈ preserved, r ≠ Reg.a3 := by decide
  refine ⟨?_, (fun r hr => (ha.1 r hr).trans (u0.other r (hp r hr))),
    ha.2.1.trans u0.sp, ha.2.2.trans (u0.other _ (by decide))⟩
  show bytesAt s'.mem (s.gpr .a0) 56 = _
  rw [← a0, h, a1, u0.mem]

end

section

open VG VG.RISCV64
open VG.Proof.X448.RISCV64 (x448RISCV64 x448BaseRISCV64 XPre.of)

theorem x448_ok (s : State) (hs : x448RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X448.RISCV64.R64.x448 s t s' ∧ abiPreserved s s' ∧ x448RISCV64.post s s' := by
  obtain ⟨t, s', he, h, ha⟩ := x448_correct (XPre.of hs)
  exact ⟨t, s', he, ha, h⟩

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
    Verified RISCV64.target Impl.X448.RISCV64.R64.x448 (Proof.X448.x448Contract RISCV64.abi) :=
  Verified.of_correct x448_ok x448_ct' (by
    contract_implies [Proof.X448.x448Contract, Proof.X448.x448Sig, Proof.X448.RISCV64.x448RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X448.RISCV64.R64.x448Sat] using Proof.X448.RISCV64.R64.x448Sat)

theorem BPre.of {s : State} (h : x448BaseRISCV64.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem x448Base_ok (s : State) (hs : x448BaseRISCV64.pre s) :
    ∃ t s', Exec isa Impl.X448.RISCV64.R64.x448Base s t s' ∧ abiPreserved s s' ∧
      x448BaseRISCV64.post s s' := by
  obtain ⟨t, s', he, h, ha⟩ := x448Base_correct (BPre.of hs)
  exact ⟨t, s', he, ha, h⟩

theorem x448Base_ct' : ConstantTime isa x448BaseRISCV64.pre x448BaseRISCV64.pub
    Impl.X448.RISCV64.R64.x448Base :=
  x448Base_ct fun _ _ _ _ ⟨h3, h4, h5, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying `vg_x448_base`'s precondition. -/
def x448BaseSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_verified :
    Verified RISCV64.target Impl.X448.RISCV64.R64.x448Base (Spec.X448.x448BaseContract RISCV64.abi) :=
  Verified.of_correct x448Base_ok x448Base_ct' (by
    contract_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Proof.X448.RISCV64.x448BaseRISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X448.RISCV64.R64.x448BaseSat]
      using Proof.X448.RISCV64.R64.x448BaseSat)

end

end VG.Proof.X448.RISCV64.R64
