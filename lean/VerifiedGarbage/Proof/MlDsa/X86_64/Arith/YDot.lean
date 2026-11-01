module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
meta import VerifiedGarbage.Proof.MlDsa.Arith.Representation
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract

/-!
# ML-DSA on x86-64: `vg_mldsa_dot_inverse{c}_avx2`

Each of the 32 iterations of the loop sums, in each lane, the `c` products
of eight coefficients of `a[j]` and `b[j]` in quadwords (`dotMac`, `macs_ok`)
and reduces them (`dotRed`, `dot_lane`), storing the sums times `2⁻³²`
(`step`); then the inverse NTT with Montgomery scaling (`body_ok`) cancels
the factor (`Representation.inverse_encode`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.YDot

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly
  gprPreserved_of ifp ifn GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm
  withMxcsr_ok mxR)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs montgomeryRInv)

theorem lane_dotZero : laneSseBlock (toY dotZero) = some dotZero := by decide +kernel
theorem lane_dotMac : laneSseBlock (toY dotMac) = some dotMac := by decide +kernel
theorem lane_dotRed : laneSseBlock (toY dotRed) = some dotRed := by decide +kernel

/-- The sums of the first `n` products of the eight coefficients `Av j t`,
`Bv j t` (`t < 8`) in the quadwords of the lanes of `ymm5` (even `t`) and
`ymm6` (odd). -/
def AccOk (s : State) (Av Bv : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ l < 2, ∀ k < 2,
    (qword (s.lane .xmm5 l) k).toNat = dsum (fun j => Av j (4 * l + 2 * k)) (fun j => Bv j (4 * l + 2 * k)) n ∧
    (qword (s.lane .xmm6 l) k).toNat = dsum (fun j => Av j (4 * l + 2 * k + 1)) (fun j => Bv j (4 * l + 2 * k + 1)) n

/-- The first `n` products. -/
theorem macs_ok {c : Nat} (hc : c ≤ 7) {Av Bv : Nat → Nat → Nat} (hA : ∀ j < c, ∀ t < 8, Av j t < 3 * q)
    (hB : ∀ j < c, ∀ t < 8, Bv j t < 3 * q) {s : State}
    (hr : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 32)
    (hr' : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 32)
    (ha : ∀ j < c, ∀ l < 2, ∀ e < 4, (dword (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * j) +
      BitVec.ofNat 64 (16 * l)) 128) e).toNat = Av j (4 * l + e))
    (hb : ∀ j < c, ∀ l < 2, ∀ e < 4, (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * j) +
      BitVec.ofNat 64 (16 * l)) 128) e).toNat = Bv j (4 * l + e))
    (h0 : AccOk s Av Bv 0) :
    ∀ n ≤ c, WP isa (.block ((List.range n).flatMap fun j => dotLoads j ++ toY dotMac)) s fun s' =>
      AccOk s' Av Bv n ∧ YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm5, .xmm6] s s'
  | 0, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    vrund
    exact ⟨h0, YOnly.refl _ s⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (macs_ok hc hA hB hr hr' ha hb h0 n (by omega)) fun s1 ⟨A1, o1⟩ => ?_
    rw [dotLoads, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x] ++ ([y] ++ l) from fun _ _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact hr n (by omega))) fun s2 ⟨L2, o2⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (yld_ok (by rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact hr' n (by omega)))
      fun s3 ⟨L3, o3⟩ => ?_
    refine WP.mono (ylanes lane_dotMac (P := fun l t =>
        t.xmm .xmm5 = macE ((s3.proj l).xmm .xmm5) ((s3.proj l).xmm .xmm0) ((s3.proj l).xmm .xmm1) ∧
        t.xmm .xmm6 = macO ((s3.proj l).xmm .xmm6) ((s3.proj l).xmm .xmm0) ((s3.proj l).xmm .xmm1))
      fun l _ => WP.mono (dotMac_ok _) fun t ⟨h5, h6, ht⟩ => ⟨⟨h5, h6⟩, ht⟩) fun s4 ⟨M4, o4⟩ => ⟨?_, ?_⟩
    · intro l hl k hk
      have x0 : (s3.proj l).xmm .xmm0 = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * n) +
          BitVec.ofNat 64 (16 * l)) 128 := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, L2 l hl, o1.mem, o1.gpr]
      have x1 : (s3.proj l).xmm .xmm1 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * n) +
          BitVec.ofNat 64 (16 * l)) 128 := by
        rw [State.proj_xmm, L3 l hl, o2.mem, o2.gpr, o1.mem, o1.gpr]
      have x5 : (s3.proj l).xmm .xmm5 = s1.lane .xmm5 l := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl]
      have x6 : (s3.proj l).xmm .xmm6 = s1.lane .xmm6 l := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl]
      have e5 : s4.lane .xmm5 l = _ := (M4 l hl).1
      have e6 : s4.lane .xmm6 l = _ := (M4 l hl).2
      have a0 := ha n (by omega) l hl (2 * k) (by omega)
      have a1 := ha n (by omega) l hl (2 * k + 1) (by omega)
      have b0 := hb n (by omega) l hl (2 * k) (by omega)
      have b1 := hb n (by omega) l hl (2 * k + 1) (by omega)
      rw [← x0] at a0 a1
      rw [← x1] at b0 b1
      rw [show 4 * l + (2 * k + 1) = 4 * l + 2 * k + 1 by omega] at a1 b1
      refine ⟨?_, ?_⟩
      · rw [e5, qword_macE hk (by rw [x5, (A1 l hl k hk).1, a0, b0]; exact prod_bound hc hA hB (by omega) (by omega)), x5,
          (A1 l hl k hk).1, a0, b0]
        rfl
      · rw [e6, qword_macO hk (by rw [x6, (A1 l hl k hk).2, a1, b1]; exact prod_bound hc hA hB (by omega) (by omega)), x6,
          (A1 l hl k hk).2, a1, b1]
        rfl
    · exact (((o1.trans o2).trans o3).trans o4).mono (by simp)

/-- Coefficient `k` of the result: the sum of the products, times `2⁻³²`. -/
def dotOut (m : VG.Mem) (a b : Addr) (c k : Nat) : Zq :=
  Fin.ofNat q (dsum (fun j => famV m a j k) (fun j => famV m b j k) c) * montgomeryRInv

/-- After `i` iterations of the loop, from `s₀`. -/
structure DI (o a b : Addr) (c : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = coeffAddr o (8 * i)
  r10 : s.gpr .r10 = coeffAddr a (8 * i)
  rdx : s.gpr .rdx = coeffAddr b (8 * i)
  keep : Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s
  yc : YConsts s
  frame : Frame [pR o] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem o k).toNat = (dotOut s₀.mem a b c k).val

section
variable {o a b : Addr} {c : Nat} {s₀ : State} (hc7 : c ≤ 7) (hwo : pR o ∈ s₀.wr)
  (hra : ∀ j < c, ∀ k, k + 8 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (a + BitVec.ofNat 64 (1024 * j)) k) 32)
  (hrb : ∀ j < c, ∀ k, k + 8 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (b + BitVec.ofNat 64 (1024 * j)) k) 32)
  (hda : ∀ j < c, (pR (a + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hdb : ∀ j < c, (pR (b + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hA : ∀ j < c, ∀ k < 256, famV s₀.mem a j k < 3 * q) (hB : ∀ j < c, ∀ k < 256, famV s₀.mem b j k < 3 * q)
include hc7 hwo hra hrb hda hdb hA hB

theorem step {i : Nat} (hi : i < 32) {s : State} (hI : DI o a b c s₀ i s) :
    WP isa (.block (dotBody c ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      DI o a b c s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  -- the values of the coefficients loaded
  have hv : ∀ (p : Addr), (∀ j < c, (pR (p + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o)) → ∀ j < c, ∀ l < 2,
      ∀ e < 4, (dword (s.mem.readW (coeffAddr p (8 * i) + BitVec.ofNat 64 (1024 * j) + BitVec.ofNat 64 (16 * l)) 128)
        e).toNat = famV s₀.mem p j (8 * i + (4 * l + e)) := fun p hd j hj l hl e he => by
    rw [addr_fam, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, famV, ← Nat.add_assoc,
      coeffAt_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd j hj) (by rw [n_eq]; omega)]
  simp only [dotBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_dotZero (P := fun l t => t.xmm .xmm5 = 0 ∧ t.xmm .xmm6 = 0)
    fun l _ => WP.mono (dotZero_ok _) fun t ⟨h5, h6, ht⟩ => ⟨⟨h5, h6⟩, ht⟩) fun s1 ⟨Z1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (macs_ok hc7 (Av := fun j t => famV s₀.mem a j (8 * i + t)) (Bv := fun j t => famV s₀.mem b j (8 * i + t))
    (fun j hj t ht => hA j hj _ (by omega)) (fun j hj t ht => hB j hj _ (by omega))
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.r10, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hra j hj _ j0)
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.rdx, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hrb j hj _ j0)
    (fun j hj l hl e he => by rw [o1.mem, o1.gpr, hI.r10]; exact hv a hda j hj l hl e he)
    (fun j hj l hl e he => by rw [o1.mem, o1.gpr, hI.rdx]; exact hv b hdb j hj l hl e he)
    (fun l hl k hk => by
      have e5 : s1.lane .xmm5 l = _ := (Z1 l hl).1
      have e6 : s1.lane .xmm6 l = _ := (Z1 l hl).2
      rw [e5, e6]; exact ⟨by simp [qword, dsum], by simp [qword, dsum]⟩) c (Nat.le_refl _)) fun s2 ⟨A2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_dotRed (P := fun l t => t.xmm .xmm5 = csubV (redV ((s2.proj l).xmm .xmm5) ((s2.proj l).xmm .xmm6)))
    fun l hl => WP.mono (dotRed_ok (yonly_yconsts o12 hI.yc (by decide) (by decide) l hl)) fun t ⟨h5, ht⟩ => ⟨h5, ht⟩)
    fun s3 ⟨R3, o3⟩ => ?_
  have o13 := o12.trans o3
  -- the eight results
  have hres : ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm5 l) e).toNat = (dotOut s₀.mem a b c (8 * i + 4 * l + e)).val := by
    intro l hl e he
    have e3 : s3.lane .xmm5 l = _ := R3 l hl
    rw [e3, dot_lane (e := (s2.proj l).xmm .xmm5) (o := (s2.proj l).xmm .xmm6)
      (A := fun j t => famV s₀.mem a j (8 * i + (4 * l + t)))
      (B := fun j t => famV s₀.mem b j (8 * i + (4 * l + t))) hc7
      (fun j hj t ht => hA j hj _ (by omega)) (fun j hj t ht => hB j hj _ (by omega))
      (fun k hk => by rw [State.proj_xmm]; exact (A2 l hl k hk).1)
      (fun k hk => by rw [State.proj_xmm, (A2 l hl k hk).2]; simp only [Nat.add_assoc]) he]
    simp only [dotOut, Nat.add_assoc]
  have g3 : s3.gpr .r8 = coeffAddr o (8 * i) := by rw [o13.gpr, hI.r8]
  have w0 : InRegions s3.wr (s3.gpr .r8) 32 := by
    rw [o13.wr, g3, hI.keep.2.2]; exact f_in32 hwo j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  rw [g3, o13.mem]
  have p8 : coeffAddr o (8 * i) + 32 = coeffAddr o (8 * (i + 1)) := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, show 8 * i + 8 = 8 * (i + 1) by omega]
  have pa : ∀ p : Addr, coeffAddr p (8 * i) + 32 = coeffAddr p (8 * (i + 1)) := fun p => by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, show 8 * i + 8 = 8 * (i + 1) by omega]
  refine ⟨⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, fun k hk => ?_⟩, by rw [o13.gpr], by rw [o13.gpr]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    exact p8
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.r10]; exact pa a
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdx]; exact pa b
  · have hr0 := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false,
      State.setMem_gpr]
    rw [o13.gpr, hI.keep.1 r hr0]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.keep.2.1]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.keep.2.2]
  · exact ylanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hI.yc
      (by decide) (by decide)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [coeffAt_write256 _ _ j0 _ (by omega)]
    split
    · rw [State.ymm, extract_ymm _ _ (by omega)]
      split
      · have := hres 0 (by decide) (k - 8 * i) (by omega)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this; exact this
      · have := hres 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this; exact this
    · exact hI.done k (by omega)

/-- The loop, from the constants and the pointers, in `s₀`. -/
theorem pass_ok (h8 : s₀.gpr .r8 = o) (h10 : s₀.gpr .r10 = a) (hdx : s₀.gpr .rdx = b) (hc : YConsts s₀) :
    WP isa (rcxLoop 32 (dotBody c)) s₀ fun s' => PolyIs s'.mem o (Vector.ofFn fun k => dotOut s₀.mem a b c k.val) ∧
      Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s' ∧ Frame [pR o] s₀.mem s'.mem := by
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) (DI o a b c s₀)
    (fun u og hy _ => ⟨by rw [og.keep.gpr (by decide), h8, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), h10, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      og.keep.mono (by simp), ylanes_gpr (s := s₀) (og.lane hy) (YOnly.refl [] s₀) hc (by decide) (by decide),
      by rw [og.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩)
    (fun i hi u hI => step hc7 hwo hra hrb hda hdb hA hB hi hI)) fun u hI => ⟨⟨fun k hk => ?_, ?_⟩, hI.keep, hI.frame⟩
  · rw [n_eq] at hk
    rw [hI.done k (by omega)]; exact (dotOut s₀.mem a b c k).isLt
  · apply Vector.ext; intro k hk
    rw [polyAt, Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply Fin.ext
    rw [Fin.val_ofNat, hI.done k (by rw [n_eq] at hk; omega), Nat.mod_eq_of_lt (dotOut s₀.mem a b c k).isLt]

end

/-! ## The function -/

/-- The result: the sums times `2⁻³²`, which the inverse transform's factor cancels. -/
theorem dotOut_eq {m m' : VG.Mem} {a b : Addr} {c : Nat}
    (ha : ∀ j < c, ∀ k < 256, coeffAt m' (a + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (a + BitVec.ofNat 64 (1024 * j)) k)
    (hb : ∀ j < c, ∀ k < 256, coeffAt m' (b + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (b + BitVec.ofNat 64 (1024 * j)) k) :
    (Vector.ofFn fun k => dotOut m' a b c k.val) = Representation.encode true (Proof.MlDsa.dotNTT
      (fun j => polyAt m (a + BitVec.ofNat 64 (1024 * j))) (fun j => polyAt m (b + BitVec.ofNat 64 (1024 * j))) c) := by
  apply Vector.ext; intro k hk
  rw [Vector.getElem_ofFn, ← getElem!_pos (Representation.encode true _) k hk]
  change _ = (Montgomery.scale montgomeryRInv _)[k]!
  rw [Montgomery.scale_get, dotNTT_get (A := fun j => famV m' a j k) (B := fun j => famV m' b j k) hk
    (fun j hj => by rw [polyAt_get _ _ hk, famV, ha j hj k hk]) (fun j hj => by rw [polyAt_get _ _ hk, famV, hb j hj k hk])]
  rfl

theorem correct {c : Nat} (hc7 : c ≤ 7)
    (hk : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi]) (dotInvAvx2 c) = true)
    (hk' : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10])
      (.seq (.block (yconsts ++ ([.mov .r8 (.reg .rdi)] : List Instr))) (.seq (rcxLoop 32 (dotBody c)) montInvBody)) = true)
    (hctl : ctlOk (dotInvAvx2 c) = true) (s : State) (hs : (dotK c).pre s) :
    ∃ t s', Exec isa (dotInvAvx2 c) s t s' ∧ abiPreserved s s' ∧ (dotK c).post s s' := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, pa, pb⟩ := hs
  have hwo : pR (s.gpr .rdi) ∈ s.wr := by rw [hwr]; simp
  have hws : pR (s.gpr .rcx) ∈ s.wr := by rw [hwr]; simp
  have hW : WP isa (dotInvAvx2 c) s fun s' => PolyIs s'.mem (s.gpr .rdi) (Spec.MlDsa.nttInv (Proof.MlDsa.dotNTT
      (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
      (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .r10 = s.gpr .rsi ∧ w.gpr .rsi = s.gpr .rcx ∧
        GOnly [.r10, .rsi] s w ∧ w.ymmHi = s.ymmHi)
      (by vrund; exact ⟨by gonlyd, rfl⟩) fun w ⟨h10, hsi, og, hy⟩ => ?_)
    refine WP.mono (withMxcsr_ok (r := .rsi) (Q := fun u => PolyIs u.mem (s.gpr .rdi) (Spec.MlDsa.nttInv
        (Proof.MlDsa.dotNTT (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
          (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem u.mem) ⟨by decide, by decide⟩ [.rax, .rcx, .rdx, .r8, .r9, .r10]
      ⟨by decide, by decide⟩ hsi (by rw [og.keep.2.2]; exact hws) (writesOnly_of hk') (fun s1 k1 f1 => ?_))
      fun s' ⟨s2, ⟨hP, hf⟩, hf', _⟩ => ⟨?_, ?_⟩
    rotate_left
    · exact polyIs_frame hf' (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact d3.sub_right (mx_sub' _)) hP
    · exact hf.trans (frame_fs hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _))
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    have hsi1 : s1.gpr .rsi = s.gpr .rcx := by rw [k1.gpr (by decide), hsi]
    have h101 : s1.gpr .r10 = s.gpr .rsi := by rw [k1.gpr (by decide), h10]
    have hdx1 : s1.gpr .rdx = s.gpr .rdx := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    have wr1 : s1.wr = s.wr := by rw [k1.2.2, og.keep.2.2]
    have rd1 : s1.rd = s.rd := by rw [k1.2.1, og.keep.2.1]
    have hm : ∀ p : Addr, (pR (s.gpr .rcx)).Disjoint (famR p c) → ∀ j < c, ∀ k < 256,
        coeffAt s1.mem (p + BitVec.ofNat 64 (1024 * j)) k = coeffAt s.mem (p + BitVec.ofNat 64 (1024 * j)) k :=
      fun p hd j hj k hk => by
        rw [coeffAt_frame f1 (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact (hd.sub_right (fam_sub p hj)).symm.sub_right (mx_sub' _))
          (by rw [n_eq]; exact hk), og.mem]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (yconsts_ok s1) fun s2 ⟨c2, k2, m2, _, _⟩ => ?_
    have hdi2 : s2.gpr .rdi = s.gpr .rdi := by rw [k2.gpr (by decide), hdi1]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .r8 = s.gpr .rdi ∧ GOnly [.r8] s2 s3 ∧ s3.ymmHi = s2.ymmHi)
      (by vrund [hdi2]; exact ⟨by gonlyd, rfl⟩) fun s3 ⟨h8, og3, hy3⟩ => ?_
    have c3 : YConsts s3 := ylanes_gpr (s := s2) (GOnly.lane og3 hy3) (YOnly.refl [] s2) c2 (by decide) (by decide)
    have k13 : Keep [.rax, .r8] s1 s3 := (k2.trans og3.keep).mono (by simp)
    have m3 : s3.mem = s1.mem := by rw [og3.mem, m2]
    have hr : ∀ p : Addr, famR p c ∈ s.rd → ∀ j < c, ∀ k, k + 8 ≤ 256 →
        InRegions (s3.rd ++ s3.wr) (coeffAddr (p + BitVec.ofNat 64 (1024 * j)) k) 32 := fun p hp j hj k hk =>
      ⟨famR p c, by rw [k13.2.1, rd1]; exact List.mem_append_left _ hp, by
        rw [coeffAddr, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.seq (WP.mono (pass_ok (s₀ := s3) hc7 (by rw [k13.2.2, wr1]; exact hwo)
      (hr _ (by rw [hrd]; simp)) (hr _ (by rw [hrd]; simp))
      (fun j hj => (d1.sub_right (fam_sub _ hj)).symm) (fun j hj => (d2.sub_right (fam_sub _ hj)).symm)
      (fun j hj k hk => by rw [famV, m3, hm _ d4 j hj k hk]; exact pa j hj k (by rw [n_eq]; exact hk))
      (fun j hj k hk => by rw [famV, m3, hm _ d5 j hj k hk]; exact pb j hj k (by rw [n_eq]; exact hk))
      h8 (by rw [k13.gpr (by decide), h101]) (by rw [k13.gpr (by decide), hdx1]) c3) fun u ⟨hP, ku, fu⟩ => ?_)
    refine WP.mono (MontgomeryInv.body_ok (by rw [ku.gpr (by decide), k13.gpr (by decide), hdi1])
      (by rw [ku.gpr (by decide), k13.gpr (by decide), hsi1]) hP
      (by rw [ku.2.2, k13.2.2, wr1]; exact hwo) (by rw [ku.2.2, k13.2.2, wr1]; exact hws) d3) fun v ⟨hv, fv⟩ => ⟨?_, ?_⟩
    · have e : Proof.MlDsa.montgomeryNttInv (Representation.encode true (Proof.MlDsa.dotNTT
          (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
          (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) = _ :=
        Representation.inverse_encode true _
      rw [dotOut_eq (m := s.mem) (fun j hj k hk => by rw [m3, hm _ d4 j hj k hk])
        (fun j hj k hk => by rw [m3, hm _ d5 j hj k hk]), e] at hv
      exact hv
    · have f1' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s1.mem := by
        rw [← og.mem]; exact frame_fs f1 fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _)
      have fu' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s1.mem u.mem := by
        rw [← m3]; exact frame_fs fu fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inl fun _ h => h
      exact (f1'.trans fu').trans fv
  obtain ⟨tr, s', he, ⟨hP, hf⟩, hk2⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi] hW (writesOnly_of hk)
  exact ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk2 (by decide) hf (by simpa using ⟨r1, r2⟩)), hP⟩

theorem ct4 : ConstantTime isa (dotK 4).pre (dotK 4).pub (dotInvAvx2 4) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 4) (by taint_decide)

theorem ct5 : ConstantTime isa (dotK 5).pre (dotK 5).pub (dotInvAvx2 5) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 5) (by taint_decide)

theorem ct7 : ConstantTime isa (dotK 7).pre (dotK 7).pub (dotInvAvx2 7) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 7) (by taint_decide)

theorem verified4 : Verified X86_64.target (dotInvAvx2 4) (Proof.MlDsa.dotInverseContract 4 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct4
    (by dot_implies dotSat 4)

theorem verified5 : Verified X86_64.target (dotInvAvx2 5) (Proof.MlDsa.dotInverseContract 5 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct5
    (by dot_implies dotSat 5)

theorem verified7 : Verified X86_64.target (dotInvAvx2 7) (Proof.MlDsa.dotInverseContract 7 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct7
    (by dot_implies dotSat 7)

end VG.Proof.MlDsa.X86_64.Arith.YDot
