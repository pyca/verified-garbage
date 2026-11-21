module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YDot
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Sample.Rej4
public import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2
meta import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr

/-! ### `MlDsa.X86_64.Arith.YMontgomery`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Arith.YMul`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt_avx2` and `vg_mldsa_multiply_add_ntt_avx2`

As `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt` (`Mul.lean`) on
eight coefficients at a time: each iteration of the loop loads eight
coefficients of `f`, `g` and `h` and, in each lane, does what the SSE2 code's
`mulCore` (`mulAddCore`) does (`ylanes`), on the coefficients `8i + 4l` to `8i +
4l + 3` of lane `l`, and stores the eight results (`YMul.step`); the loop
stores the first 248 (`YMul.loop_ok`), and the last eight, from the
coefficients of `h` in `ymm6` (`YMul.last`), are stored after MXCSR is loaded
back (`YMul.fn_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced)

/-- The constants, and `2⁶⁴ mod q` in both lanes of `ymm11`. -/
theorem ymulPro_ok (s : State) :
    WP isa (.block ymulPro) s fun s' => YConsts s' ∧ (∀ l < 2, s'.lane .xmm11 l = r2V) ∧
      (∀ l < 2, s'.lane .xmm6 l = s.lane .xmm6 l) ∧ Keep [.rax] s s' ∧ s'.mem = s.mem := by
  rw [ymulPro, WP.block_append_iff]
  refine WP.mono (yconsts_ok s) fun s1 ⟨c1, k1, m1, _, o1⟩ =>
    WP.mono (yconst_ok .xmm11 _ s1) fun s2 ⟨l2, k2, m2, _, o2⟩ =>
      ⟨fun l hl => ⟨?_, ?_⟩, fun l hl => by rw [l2 l hl]; decide,
        fun l hl => by rw [o2 _ (by decide) l hl, o1 _ (by decide) (by decide) l hl],
        (k1.trans k2).mono (by simp), m2.trans m1⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl]; exact (c1 l hl).q
  · rw [State.proj_xmm, o2 _ (by decide) l hl]; exact (c1 l hl).qinv

namespace YMul

/-- After `i` iterations: the first `8i` coefficients of `h` are `R`'s, the
others as they were in `s₀`. -/
structure Inv (h f g : Addr) (s₀ : State) (R : Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = h + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = f + BitVec.ofNat 64 (32 * i)
  rdx : s.gpr .rdx = g + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YConsts s
  r2 : ∀ l < 2, s.lane .xmm11 l = r2V
  x6 : ∀ l < 2, s.lane .xmm6 l = s₀.lane .xmm6 l
  frame : Frame [pR h] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem h k).toNat = (R[k]!).val
  rest : ∀ k < 256, 8 * i ≤ k → coeffAt s.mem h k = coeffAt s₀.mem h k

section
variable {h f g : Addr} {s₀ : State} (hwh : pR h ∈ s₀.wr) (hrf : pR f ∈ s₀.rd ++ s₀.wr)
  (hrg : pR g ∈ s₀.rd ++ s₀.wr) (hdf : (pR h).Disjoint (pR f)) (hdg : (pR h).Disjoint (pR g))
  {F G : Poly} (hF : ∀ k < 256, (coeffAt s₀.mem f k).toNat = (F[k]!).val)
  (hG : ∀ k < 256, (coeffAt s₀.mem g k).toNat = (G[k]!).val)
  {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
  (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
    s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
  (hY : laneSseBlock (toY core) = some core)
  {R : Poly} {H : Nat → BitVec 32} (hH : ∀ k < 248, coeffAt s₀.mem h k = H k)
  (hlane : ∀ i < 64, ∀ x y z : BitVec 128, (∀ e < 4, (dword x e).toNat = (F[4 * i + e]!).val) →
    (∀ e < 4, (dword y e).toNat = (G[4 * i + e]!).val) → (∀ e < 4, dword z e = H (4 * i + e)) →
    ∀ e < 4, (dword (Fv x y z) e).toNat = (R[4 * i + e]!).val)
include hwh hrf hrg hdf hdg hF hG hcore hY hH hlane

theorem step {i : Nat} (hi : i < 31) {s : State} (hI : Inv h f g s₀ R i s) :
    WP isa (.block (ymulLoads ++ toY core ++ ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv h f g s₀ R (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain j0 : 8 * i + 8 ≤ 256 := by omega_arith
  obtain e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr f (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega_arith
  obtain e2 : s.gpr .rdx + BitVec.ofNat 64 0 = coeffAddr g (8 * i) := by
    rw [add_ofNat_zero, hI.rdx]; congr 2; omega_arith
  obtain e3 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr h (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega_arith
  obtain mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  obtain mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [show ymulLoads ++ toY core ++ ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
    [.vmovdquLoad .l256 .xmm3 (at_ .rsi 0)] ++ [.vmovdquLoad .l256 .xmm13 (at_ .rdx 0)] ++
      [.vmovdquLoad .l256 .xmm5 (at_ .rdi 0)] ++ (toY core ++ (ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr)))
    by simp [ymulLoads, List.append_assoc],
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1, hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains32 f j0⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2, hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains32 g j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  obtain o12 := o1.trans o2
  refine WP.mono (yld_ok (by
    rw [o12.rd, o12.wr, o12.gpr, e3, hI.rd, hI.wr]; exact f_in32 (List.mem_append_right _ hwh) j0))
    fun s3 ⟨L3, o3⟩ => ?_
  obtain o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t =>
      t.xmm .xmm3 = Fv ((s3.proj l).xmm .xmm3) ((s3.proj l).xmm .xmm13) ((s3.proj l).xmm .xmm5))
    fun l hl => hcore _ (yonly_yconsts o13 hI.c (by decide) (by decide) l hl)
      (by rw [State.proj_xmm, o13.lane _ (by decide) l hl]; exact hI.r2 l hl))
    fun s4 ⟨B4, o4⟩ => ?_
  obtain o14 := o13.trans o4
  obtain g4 : s4.gpr .rdi = coeffAddr h (8 * i) := by rw [o14.gpr, ← e3, add_ofNat_zero]
  obtain w0 : InRegions s4.wr (s4.gpr .rdi) 32 := by rw [o14.wr, g4, hI.wr]; exact f_in32 hwh j0
  -- the lanes of the result
  obtain hl : ∀ l < 2, ∀ e < 4, (dword (s4.lane .xmm3 l) e).toNat = (R[8 * i + 4 * l + e]!).val := by
    intro l hl e he
    rw [← State.proj_xmm, B4 l hl, State.proj_xmm, State.proj_xmm, State.proj_xmm,
      o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, L1 l hl,
      L2 l hl, L3 l hl, o1.gpr, o1.mem, o2.gpr, o2.mem, o1.gpr, o1.mem, e1, e2, e3,
      show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega_arith]
    refine hlane (2 * i + l) (by omega_arith) _ _ _ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) e he
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mf _ (by omega_arith), hF _ (by omega_arith),
        show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega_arith]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mg _ (by omega_arith), hG _ (by omega_arith),
        show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega_arith]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hI.rest _ (by omega_arith) (by omega_arith),
        hH _ (by omega_arith), show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega_arith]
  simp only [ymulTail]
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ?_, fun l hl => ?_, ?_, fun k hk => ?_,
    fun k hk hk' => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rdx]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o14.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o14.wr, hI.wr]
  · rw [State.proj_xmm]; simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    exact (yonly_yconsts o14 hI.c (by decide) (by decide) l hl).q
  · rw [State.proj_xmm]; simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    exact (yonly_yconsts o14 hI.c (by decide) (by decide) l hl).qinv
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o14.lane _ (by decide) l hl]; exact hI.r2 l hl
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o14.lane _ (by decide) l hl]; exact hI.x6 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem, coeffAt_write256 _ _ j0 _ (by omega_arith)]
    split
    · rename_i hk'
      rw [State.ymm, extract_ymm _ _ (by omega_arith)]
      split
      · rename_i h4
        have := hl 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega_arith] at this
        exact this
      · rename_i h4
        have := hl 1 (by decide) (k - 8 * i - 4) (by omega_arith)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega_arith] at this
        exact this
    · exact hI.done k (by omega_arith)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem, coeffAt_write256 _ _ j0 _ hk, ifn (by omega_arith)]
    exact hI.rest k hk (by omega_arith)
  · exact ⟨by rw [o14.gpr], by rw [o14.gpr]⟩

theorem loop_ok (hdi : s₀.gpr .rdi = h) (hsi : s₀.gpr .rsi = f) (hdx : s₀.gpr .rdx = g) (hc : YConsts s₀)
    (h11 : ∀ l < 2, s₀.lane .xmm11 l = r2V) :
    WP isa (rcxLoop 31 (ymulLoads ++ toY core ++ ymulTail)) s₀ (Inv h f g s₀ R 31) :=
  wp_rcxLoopY (N := 31) (by decide) (by decide) _ (fun u o hy _ =>
    have lu : ∀ r l, u.lane r l = s₀.lane r l := fun r l => by simp only [State.lane]; rw [o.xmm, hy]
    ⟨by rw [o.keep.gpr (by decide), hdi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hsi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, add_ofNat_zero], o.keep.2.1, o.keep.2.2,
      fun l hl => ⟨by rw [State.proj_xmm, lu]; exact (hc l hl).q, by rw [State.proj_xmm, lu]; exact (hc l hl).qinv⟩,
      fun l hl => by rw [lu]; exact h11 l hl, fun l _ => lu _ l,
      by rw [o.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega_arith), fun k _ _ => by rw [o.mem]⟩)
    fun i hi u hI => step hwh hrf hrg hdf hdg hF hG hcore hY hH hlane hi hI

omit hwh hH in
/-- The last eight coefficients, with those of `h` in `ymm6`. -/
theorem last {s : State} (hI : Inv h f g s₀ R 31 s)
    (hz : ∀ l < 2, ∀ e < 4, dword (s₀.lane .xmm6 l) e = H (248 + 4 * l + e)) :
    WP isa (.block (ymulLast core)) s fun s' =>
      (∀ l < 2, ∀ e < 4, (dword (s'.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val) ∧ s'.gpr = s.gpr ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain j0 : 8 * 31 + 8 ≤ 256 := by decide
  obtain e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr f 248 := by rw [add_ofNat_zero, hI.rsi]
  obtain e2 : s.gpr .rdx + BitVec.ofNat 64 0 = coeffAddr g 248 := by rw [add_ofNat_zero, hI.rdx]
  obtain mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  obtain mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  obtain hY' : laneSseBlock ([.vop (.vmovdqa .l256 .xmm5 .xmm6)] ++ toY core) = some (xmov .xmm5 .xmm6 :: core) := by
    show (match laneSse _, laneSseBlock (toY core) with | some a, some b => some (a ++ b) | _, _ => none) = _
    rw [hY]; rfl
  rw [ymulLast, show ∀ a b c : Instr, ∀ l : List Instr, [a, b, c] ++ l = [a] ++ [b] ++ ([c] ++ l) from
    fun _ _ _ _ => rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1, hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains32 f j0⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2, hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains32 g j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  obtain o12 := o1.trans o2
  refine WP.mono (ylanes hY' (rs := [.xmm5, .xmm12, .xmm3, .xmm2, .xmm4]) (P := fun l t =>
      t.xmm .xmm3 = Fv ((s2.proj l).xmm .xmm3) ((s2.proj l).xmm .xmm13) ((s2.proj l).xmm .xmm6))
    fun l hl => ?_) fun s3 ⟨B3, o3⟩ => ⟨fun l hl e he => ?_, (o12.trans o3).gpr, (o12.trans o3).mem,
      (o12.trans o3).rd, (o12.trans o3).wr⟩
  · have c2 := yonly_yconsts o12 hI.c (by decide) (by decide) l hl
    rw [show xmov .xmm5 .xmm6 :: core = [xmov .xmm5 .xmm6] ++ core from rfl, WP.block_append_iff]
    vrund [eval_movdqa]
    refine WP.mono (hcore _ (c2.setXmm (by decide) (by decide) _)
      (by rw [xmm_setXmm, ifn (by decide), State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.r2 l hl))
      fun t ⟨ht, ot⟩ => ⟨?_, ?_⟩
    · rw [ht, xmm_setXmm, xmm_setXmm, xmm_setXmm, ifn (by decide), ifn (by decide), ifp rfl]
    · refine (XOnly.trans (⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr => ?_⟩ :
        XOnly [.xmm5] (s2.proj l) ((s2.proj l).setXmm .xmm5 ((s2.proj l).xmm .xmm6))) ot).mono
        (rs' := [.xmm5, .xmm12, .xmm3, .xmm2, .xmm4]) (by simp)
      rw [xmm_setXmm, ifn (by simpa using hr)]
  · rw [← State.proj_xmm, B3 l hl, State.proj_xmm, State.proj_xmm, State.proj_xmm,
      o2.lane _ (by decide) l hl, L1 l hl, L2 l hl, o1.gpr, o1.mem, e1, e2,
      o12.lane _ (by decide) l hl, hI.x6 l hl, show 248 + 4 * l + e = 4 * (62 + l) + e by omega_arith]
    refine hlane (62 + l) (by omega_arith) _ _ _ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) e he
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mf _ (by omega_arith), hF _ (by omega_arith),
        show 248 + 4 * l + e = 4 * (62 + l) + e by omega_arith]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mg _ (by omega_arith), hG _ (by omega_arith),
        show 248 + 4 * l + e = 4 * (62 + l) + e by omega_arith]
    · rw [hz l hl e he, show 248 + 4 * l + e = 4 * (62 + l) + e by omega_arith]

end


/-- The whole function, from its precondition, with a `core` whose lanes are
those of `t`. -/
theorem fn_ok {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} {σ : State} (hp : (mulK t hPre).pre σ)
    {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
      s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
    (hY : laneSseBlock (toY core) = some core)
    (hlane : ∀ i < 64, ∀ x y z : BitVec 128,
      (∀ e < 4, (dword x e).toNat = ((polyAt σ.mem (σ.gpr .rsi))[4 * i + e]!).val) →
      (∀ e < 4, (dword y e).toNat = ((polyAt σ.mem (σ.gpr .rdx))[4 * i + e]!).val) →
      (∀ e < 4, dword z e = coeffAt σ.mem (σ.gpr .rdi) (4 * i + e)) →
      ∀ e < 4, (dword (Fv x y z) e).toNat = ((t (polyAt σ.mem (σ.gpr .rdi)) (polyAt σ.mem (σ.gpr .rsi))
        (polyAt σ.mem (σ.gpr .rdx)))[4 * i + e]!).val)
    (hk : Code.allInstrs (writesIn [.rax, .rdi, .rsi, .rdx, .rcx])
      (.seq (.block ymulPro) (.seq (rcxLoop 31 (ymulLoads ++ toY core ++ ymulTail)) (.block (ymulLast core)))) =
        true) :
    WP isa (ymulFn core) σ fun s' => Keep [.r8, .rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] σ s' ∧
      Frame [pR (σ.gpr .rdi)] σ.mem s'.mem ∧ (mulK t hPre).post σ s' := by
  obtain ⟨hrd, hwr, hdf, hdg, -, -, -, -, redf, redg⟩ := hp
  generalize eh : σ.gpr .rdi = h at *
  generalize ef : σ.gpr .rsi = f at *
  generalize eg : σ.gpr .rdx = g at *
  let R := t (polyAt σ.mem h) (polyAt σ.mem f) (polyAt σ.mem g)
  obtain hwh : pR h ∈ σ.wr := by rw [hwr]; exact List.mem_singleton_self _
  simp only [ymulFn]
  rw [show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r8 = h ∧
      (∀ l < 2, s1.lane .xmm6 l = σ.mem.readW (coeffAddr h 248 + BitVec.ofNat 64 (16 * l)) 128) ∧
      Keep [.r8] σ s1 ∧ s1.mem = σ.mem) ?_ fun s1 ⟨h8, h6, k1, m1⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (Q := fun (s0 : State) => s0.gpr .r8 = h ∧ s0.gpr .rdi = h ∧ GOnly [.r8] σ s0 ∧
        s0.ymmHi = σ.ymmHi) (by vrund [eh, RegUpd.ymmHi_setReg]; gonlyd)
      fun s0 ⟨h80, hd0, o0, y0⟩ => ?_
    refine WP.mono (yld_ok (by
      rw [hd0, o0.keep.2.1, o0.keep.2.2]
      exact ⟨_, List.mem_append_right _ hwh, Offset.contains_base h (by omega_arith) (by omega_arith)⟩))
      fun s1 ⟨L1, o1⟩ => ⟨by rw [o1.gpr, h80], fun l hl => by rw [L1 l hl, hd0, o0.mem],
        ⟨fun r hr => by rw [o1.gpr, o0.keep.gpr hr], by rw [o1.rd, o0.keep.2.1], by rw [o1.wr, o0.keep.2.2]⟩,
        by rw [o1.mem, o0.mem]⟩
  obtain hw1 : pR h ∈ s1.wr := by rw [k1.2.2]; exact hwh
  refine WP.seq (WP.mono (noMxH_ok (p := h) (Q := fun (s3 : State) => Keep [.rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] s1 s3 ∧
      s3.gpr .rdi = coeffAddr h 248 ∧ Frame [pR h] σ.mem s3.mem ∧
      (∀ k < 248, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
      ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val)
    fun s2 k2 f2 x2 y2 => ?_) fun s4 ⟨s3, ⟨kk, hdi, fr, dn, ln⟩, f4, k4, x4, y4⟩ => ?_)
  · have fσ2 : Frame [mxH h] σ.mem s2.mem := by rw [← m1]; exact f2
    obtain l2 : ∀ r l, s2.lane r l = s1.lane r l := fun r l => by simp only [State.lane]; rw [x2, y2]
    refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx] (WP.seq (WP.mono (ymulPro_ok s2)
      fun w ⟨cw, xw, x6, kw, mw⟩ => ?_) (Q := fun (s3 : State) => s3.gpr .rdi = coeffAddr h 248 ∧
        Frame [pR h] σ.mem s3.mem ∧ (∀ k < 248, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
        ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val)) (writesOnly_of hk))
      fun s3 ⟨q3, kk⟩ => ⟨k2.trans kk, q3⟩
    obtain gw : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r8 → w.gpr r = σ.gpr r := fun r h1 h2 h3 => by
      rw [kw.gpr (by simpa using h1), k2.gpr (by simp [h1, h2]), k1.gpr (by simpa using h3)]
    obtain rw' : w.rd = σ.rd ∧ w.wr = σ.wr :=
      ⟨kw.2.1.trans (k2.2.1.trans k1.2.1), kw.2.2.trans (k2.2.2.trans k1.2.2)⟩
    obtain fσw : Frame [mxH h] σ.mem w.mem := by rw [mw]; exact fσ2
    obtain fσw' : Frame [pR h] σ.mem w.mem :=
      Frame.sub fσw fun r hr => ⟨pR h, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine WP.seq (WP.mono (loop_ok (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.2]; exact hwh) (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hY (fun k hk => Mul.coeffAt_mxH fσw (by omega_arith)) hlane
      (by rw [gw _ (by decide) (by decide) (by decide), eh]) (by rw [gw _ (by decide) (by decide) (by decide), ef])
      (by rw [gw _ (by decide) (by decide) (by decide), eg]) cw xw) fun s hI => ?_)
    refine WP.mono (last (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hY hlane hI (fun l hl e he => by
        rw [x6 l hl, l2, h6 l hl, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq]))
      fun s3 ⟨ln, g3, m3, _, _⟩ => ?_
    refine ⟨by rw [g3, hI.rdi], ?_, fun k hk => by rw [m3]; exact hI.done k (by omega_arith), ln⟩
    rw [m3]
    exact Frame.trans fσw' hI.frame
  · have k14 := (k1.trans kk).trans k4
    obtain hdi4 : s4.gpr .rdi = coeffAddr h 248 := by rw [k4.gpr (by simp), hdi]
    obtain wh4 : InRegions s4.wr (s4.gpr .rdi) 32 := by
      rw [hdi4, k14.2.2]; exact f_in32 hwh (by omega_arith)
    obtain l4 : ∀ r l, s4.lane r l = s3.lane r l := fun r l => by simp only [State.lane]; rw [x4, y4]
    simp only [yepi, List.singleton_append]
    vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
      State.setMem_ymm, wh4]
    obtain f4' : Frame [pR h] s3.mem s4.mem := Frame.sub f4 fun r hr => ⟨pR h, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine ⟨k14.mono (by simp), (fr.trans f4').writeW (List.mem_singleton_self _) _
      (by rw [hdi4]; exact pR_contains32 h (by omega_arith)), ?_⟩
    dsimp only [mulK]
    rw [eh, ef, eg, show ∀ s : State, (VOp.vzeroupper.exec s).mem = s.mem from fun _ => rfl, State.setMem_mem]
    refine polyIs_of_toNat fun k hk => ?_
    rw [n_eq] at hk
    rw [hdi4, coeffAt_write256 _ _ (j := 248) (by decide) _ hk]
    split
    · rw [State.ymm, extract_ymm _ _ (by omega_arith)]
      split
      · rename_i h1 h4
        have := ln 0 (by decide) (k - 248) h4
        rw [show 248 + 4 * 0 + (k - 248) = k by omega_arith, ← l4] at this
        exact this
      · rename_i h1 h4
        have := ln 1 (by decide) (k - 248 - 4) (by omega_arith)
        rw [show 248 + 4 * 1 + (k - 248 - 4) = k by omega_arith, ← l4] at this
        exact this
    · rw [Mul.coeffAt_mxH f4 (by omega_arith)]
      exact dn k (by omega_arith)

end YMul

end VG.Proof.MlDsa.X86_64.Arith

end

end

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced)

abbrev montMulK : Contract isa := mulK (fun _ f g => Proof.MlDsa.montgomeryMultiplyNTT f g) fun _ _ => True
abbrev montMulAddK : Contract isa := mulK Proof.MlDsa.montgomeryMultiplyAddNTT Reduced

theorem montMul_get (f g : Poly) {i : Nat} (hi : i < n) :
    (Proof.MlDsa.montgomeryMultiplyNTT f g)[i]! = f[i]! * g[i]! * Proof.MlDsa.montgomeryRInv := by
  rw [Proof.MlDsa.montgomeryMultiplyNTT, map_mul_get _ _ hi, mul_get _ _ hi]

theorem montMulY_correct (s : State) (hs : montMulK.pre s) :
    ∃ t s', Exec isa montMulAvx2 s t s' ∧ abiPreserved s s' ∧ montMulK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := montMulCore) (Fv := fun x y _ => montMulV x y)
    (fun s hc _ => montMulCore_ok hc) lane_montMulCore
    (fun i hi x y z hx hy _ e he => by
      rw [montMul_get _ _ (by rw [n_eq]; omega_using [hi, he])]
      exact montMul_lane hx hy he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem montMulAddY_correct (s : State) (hs : montMulAddK.pre s) :
    ∃ t s', Exec isa montMulAddAvx2 s t s' ∧ abiPreserved s s' ∧ montMulAddK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := montMulAddCore) (Fv := montMulAddV)
    (fun s hc _ => montMulAddCore_ok hc) lane_montMulAddCore
    (fun i hi x y z hx hy hz e he => by
      rw [Proof.MlDsa.montgomeryMultiplyAddNTT, add_get _ _ (by rw [n_eq]; omega_using [hi, he]), montMul_get _ _ (by rw [n_eq]; omega_using [hi, he])]
      exact montMulAdd_lane hx hy (c := fun e => (polyAt s.mem (s.gpr .rdi))[4 * i + e]!)
        (fun e he => by rw [hz e he, polyAt_val hs.2.2.2.2.2.2.2.1 (by rw [n_eq]; omega_using [hi, he])]) he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem montMulY_ct : ConstantTime isa montMulK.pre montMulK.pub montMulAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem montMulAddY_ct : ConstantTime isa montMulAddK.pre montMulAddK.pub montMulAddAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem montMulY_verified : Verified X86_64.target montMulAvx2 (Proof.MlDsa.montgomeryMulContract X86_64.abi) :=
  Verified.of_correct montMulY_correct montMulY_ct (by
    mldsa_implies [Proof.MlDsa.montgomeryMulContract, Proof.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

theorem montMulAddY_verified : Verified X86_64.target montMulAddAvx2 (Proof.MlDsa.montgomeryMulAddContract X86_64.abi) :=
  Verified.of_correct montMulAddY_correct montMulAddY_ct (by
    mldsa_implies [Proof.MlDsa.montgomeryMulAddContract, Proof.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.X86_64.Arith

end

end

/-! ### `MlDsa.X86_64.Arith.YAddSub`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_add_avx2` and `vg_mldsa_sub_avx2`

Each iteration of the loop loads eight coefficients of `f` and of `g` and, in
each lane, does what an iteration of `vg_mldsa_add` (`vg_mldsa_sub`) does
(`AddSub.lean`), whose proof holds of each lane (`ylanes`), and stores the
eight results to `f` (`YAddSub.step`); the loop leaves `f` with all 256
(`YAddSub.fn_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

theorem addFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = addV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcsub, vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem subFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = subV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem lane_addFix : laneSseBlock (toY (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) =
    some (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) := by decide +kernel

theorem lane_subFix : laneSseBlock (toY (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) =
    some (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2) := by decide +kernel

namespace YAddSub

/-- After `i` vectors of eight, each coefficient before `8i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qV
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
  {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
  {L : BitVec 32 → BitVec 32 → BitVec 32}
  (hF : ∀ (s : State), s.xmm .xmm15 = qV →
    WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
      s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s')
  (hY : laneSseBlock (toY (xb op .xmm0 .xmm1 :: fix)) = some (xb op .xmm0 .xmm1 :: fix))
  (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
include hp hF hY hL

/-- An iteration, which stores `F` of the vectors of `f` and `g` in each lane. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (yaccBody op fix ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega_using [hi]
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega_using []
  have e2 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega_using []
  rw [yaccBody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 (List.mem_append_right _ hw) j0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact ⟨_, hr, pR_contains32 _ j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY (P := fun l t => t.xmm .xmm0 = F ((s2.proj l).xmm .xmm0) ((s2.proj l).xmm .xmm1))
    fun l hl => hF _ (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have g3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have g3' : s3.gpr .rsi = coeffAddr (s₀.gpr .rsi) (8 * i) := by rw [o13.gpr, ← e2, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .rdi) 32 := by rw [o13.wr, g3]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega_using [h]), State.ymm, extract_ymm _ _ (by omega_using [h])]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e =
          L (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by
          rw [← State.proj_xmm, B3 l hl, hL _ _ _ he, State.proj_xmm, State.proj_xmm,
            o2.lane _ (by decide) l hl, L1 l hl, L2 l hl, o1.gpr, o1.mem, e1, e2, dword_readW _ _ he,
            dword_readW _ _ he, lane_load, lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq,
            hI.coeff _ (by omega_using [hi, hl, he]), ifn (by omega_using []),
            coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) (by rw [n_eq]; omega_using [hi, hl, he])]
      split
      · rename_i h4
        have := hc 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega_using [h]] at this
        exact this
      · rename_i h4
        have := hc 1 (by decide) (k - 8 * i - 4) (by omega_using [h])
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega_using [h4]] at this
        exact this
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega_using [h'])]
      · rw [ifn h', ifn (by omega_using [h, h'])]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

/-- The whole function, from its precondition. -/
theorem fn_ok (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : Code.allInstrs (writesIn [.rax, .rdi, .rsi, .rcx]) (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi)) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block (yconst .xmm15 8380417))
        (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hW : WP isa (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k =
        L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    refine WP.seq (WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy], lq l hl]; decide,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega_using [])]⟩)
      fun i hi u hI => step hp hF hY hL hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by simp only [yepi]; vrund; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega_using [hk])]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW (writesOnly_of hc)
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hco k hk]
    exact hv k hk

end

end YAddSub

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (n)

theorem addY_correct (s : State) (hs : (accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa addAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.add).post s s' :=
  YAddSub.fn_ok hs (op := .paddd) (fix := vcsub .xmm0 .xmm2) (L := fun a b => csubL (a + b)) addFixX_ok
    lane_addFix (fun x y e he => dword_addV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [add_get _ _ hk', addD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_add])
    (by decide +kernel) (by decide +kernel)

theorem subY_correct (s : State) (hs : (accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa subAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.sub).post s s' :=
  YAddSub.fn_ok hs (op := .psubd) (fix := vcadd .xmm0 .xmm2) (L := fun a b => caddL (a - b)) subFixX_ok
    lane_subFix (fun x y e he => dword_subV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [sub_get _ _ hk', subD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_sub])
    (by decide +kernel) (by decide +kernel)

theorem addY_ct : ConstantTime isa (accK Spec.MlDsa.add).pre (accK Spec.MlDsa.add).pub addAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem subY_ct : ConstantTime isa (accK Spec.MlDsa.sub).pre (accK Spec.MlDsa.sub).pub subAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem addY_verified : Verified X86_64.target addAvx2 (Proof.MlDsa.addContract X86_64.abi) :=
  Verified.of_correct addY_correct addY_ct (by
    mldsa_implies [Proof.MlDsa.addContract, Proof.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem subY_verified : Verified X86_64.target subAvx2 (Proof.MlDsa.subContract X86_64.abi) :=
  Verified.of_correct subY_correct subY_ct (by
    mldsa_implies [Proof.MlDsa.subContract, Proof.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlDsa.X86_64.Arith

end

end

/-! ### `MlDsa.X86_64.Sample.Rej5Verified`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64

theorem rejNTT4Avx2_verified {fast : Bool} : Verified X86_64.target (Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast)
    (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ (correct (fast := fast)) ct

theorem rejNTT4Avx2_ret {fast : Bool} {s s' : State} {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa (Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := rej4_ret (correct (fast := fast)) h e

end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end


/-!
# ML-DSA on x86-64: the polynomial arithmetic with AVX2, as an `ArithImpl`

The AVX2 code (`Impl/MlDsa/X86_64/Arith/Avx2.lean`) meets what the callers of
the polynomial arithmetic need of it (`FnOk`), and requires AVX and AVX2.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- The AVX2 code. -/
theorem avx2_sides : ArithSides .avx2Combined Impl.Scrub.X86_64.VecLevel.avx.level :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩

def ArithImpl.avx2 : ArithImpl where
  code := .avx2Combined
  ok :=
    { ntt := FnOk.of Arith.Lazy.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      invNtt := FnOk.of Arith.MontgomeryInv.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mul := FnOk.of Arith.montMulY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mulAdd := FnOk.of Arith.montMulAddY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      add := FnOk.of Arith.addY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      sub := FnOk.of Arith.subY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      highBits := FnOk.of Round.highBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      lowBits := FnOk.of Round.lowBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      normLt := FnOk.of Round.normLtY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      makeHint := FnOk.of Round.makeHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      useHint := FnOk.of Round.useHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      rej4 :=
        have h := Proof.MlKem.X86_64.nospMx_of (c := Backend.avx2Combined.rej4) (by lit_decide)
        ⟨Rej4.Segment.rejNTT4Avx2_verified, h.1, h.2, by lit_decide,
          by lit_decide, Code.all_of_spTest (by lit_decide), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
      expandMask4 :=
        have h := Proof.MlKem.X86_64.nospMx_of (c := Backend.avx2Combined.expandMask4) (by lit_decide)
        ⟨Mask4.expandMask4Avx2_verified, h.1, h.2,
          by lit_decide, by lit_decide, Code.all_of_spTest (by lit_decide)⟩
      dotInv := fun c hc => by
        rcases hc with rfl | rfl | rfl
        · exact FnOk.of Arith.YDot.verified4 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified5 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified7 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide) }
  features := ["avx", "avx2"]
  level := .avx
  sides := avx2_sides

/-- The AVX-512 code's backend. -/
abbrev avx512Backend : Backend := { Backend.avx2Combined with
    rej4 := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 true
    expandMask4 := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2 true
    sfx := "_avx512" }

theorem avx512_sides : ArithSides avx512Backend Impl.Scrub.X86_64.VecLevel.evex.level :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩

/-- AVX2 arithmetic with the AVX-512VL four-state permutation in both samplers: its other
functions are the AVX2 code's, which it calls by their names (`asfx`, `_avx2`), so that they
are emitted once, and the callers that call no sampler are not instantiated for it
(`Proof/Variants/MlDsaArith/X86_64.lean`, `samplerFreeVariants`). -/
def ArithImpl.avx512 : ArithImpl where
  code := { Backend.avx2Combined with
    rej4 := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 true
    expandMask4 := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2 true
    sfx := "_avx512" }
  ok := { ArithImpl.avx2.ok with
    rej4 :=
      have h := Proof.MlKem.X86_64.nospMx_of (c := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 true) (by lit_decide)
      ⟨Rej4.Segment.rejNTT4Avx2_verified, h.1, h.2, by lit_decide,
        by lit_decide, Code.all_of_spTest (by lit_decide), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
    expandMask4 :=
      have h := Proof.MlKem.X86_64.nospMx_of (c := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2 true) (by lit_decide)
      ⟨Mask4.expandMask4Avx2_verified, h.1, h.2,
        by lit_decide, by lit_decide, Code.all_of_spTest (by lit_decide)⟩ }
  features := ["avx", "avx2", "avx512f", "avx512vl"]
  level := .evex
  sides := avx512_sides

end VG.Proof.MlDsa.X86_64
