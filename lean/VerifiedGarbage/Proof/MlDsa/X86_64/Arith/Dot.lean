module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VLay
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes

/-!
# ML-DSA on x86-64: `vg_mldsa_dot_inverse{c}`

As `vg_mldsa_dot_inverse{c}_avx2` (`YDot.lean`) on four coefficients at a
time in SSE2 registers: each of the 64 iterations sums the `c` products in
quadwords (`macs_ok`) and reduces them (`dot_lane`) to the sum times `2⁻³²`,
which `dotPlain` multiplies by `2³²` (`plain_dw`), storing the sums modulo `q`
(`step`); then the inverse NTT (`invBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.DotS

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly WP.keep writesOnly gprPreserved_of ifp ifn GOnly
  wp_rcxLoop add_ofNat_zero withMxcsr_ok mxR xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs montgomeryRInv)

/-- A 128-bit load. -/
theorem xld_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 16) :
    WP isa (.block [.movdquLoad d (at_ p off)]) s fun s' =>
      s'.xmm d = s.mem.readW (s.gpr p + BitVec.ofNat 64 off) 128 ∧ XOnly [d] s s' := by
  vrund [h]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr => ?_⟩
  rw [xmm_setXmm, ifn (by simpa using hr)]

/-- The sums of the first `n` products of the four coefficients `Av j t`,
`Bv j t` (`t < 4`) in the quadwords of `xmm5` (even `t`) and `xmm6` (odd). -/
def AccS (s : State) (Av Bv : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ k < 2,
    (qword (s.xmm .xmm5) k).toNat = dsum (fun j => Av j (2 * k)) (fun j => Bv j (2 * k)) n ∧
    (qword (s.xmm .xmm6) k).toNat = dsum (fun j => Av j (2 * k + 1)) (fun j => Bv j (2 * k + 1)) n

/-- The first `n` products. -/
theorem macs_ok {c : Nat} (hc : c ≤ 7) {Av Bv : Nat → Nat → Nat} (hA : ∀ j < c, ∀ t < 4, Av j t < 3 * q)
    (hB : ∀ j < c, ∀ t < 4, Bv j t < 3 * q) {s : State}
    (hr : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 16)
    (hr' : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 16)
    (ha : ∀ j < c, ∀ e < 4,
      (dword (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 128) e).toNat = Av j e)
    (hb : ∀ j < c, ∀ e < 4,
      (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 128) e).toNat = Bv j e)
    (h0 : AccS s Av Bv 0) :
    ∀ n ≤ c, WP isa (.block ((List.range n).flatMap fun j => dotLoadsS j ++ dotMac)) s fun s' =>
      AccS s' Av Bv n ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm5, .xmm6] s s'
  | 0, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    vrund
    exact ⟨h0, XOnly.refl _ s⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (macs_ok hc hA hB hr hr' ha hb h0 n (by omega)) fun s1 ⟨A1, o1⟩ => ?_
    rw [dotLoadsS, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x] ++ ([y] ++ l) from fun _ _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (xld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact hr n (by omega))) fun s2 ⟨L2, o2⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (xld_ok (by rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact hr' n (by omega)))
      fun s3 ⟨L3, o3⟩ => ?_
    refine WP.mono (dotMac_ok s3) fun s4 ⟨M5, M6, o4⟩ => ⟨fun k hk => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
    have x0 : s3.xmm .xmm0 = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * n)) 128 := by
      rw [o3.xmm _ (by decide), L2, o1.mem, o1.gpr]
    have x1 : s3.xmm .xmm1 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * n)) 128 := by
      rw [L3, o2.mem, o2.gpr, o1.mem, o1.gpr]
    have x5 : s3.xmm .xmm5 = s1.xmm .xmm5 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
    have x6 : s3.xmm .xmm6 = s1.xmm .xmm6 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
    have a0 := ha n (by omega) (2 * k) (by omega)
    have a1 := ha n (by omega) (2 * k + 1) (by omega)
    have b0 := hb n (by omega) (2 * k) (by omega)
    have b1 := hb n (by omega) (2 * k + 1) (by omega)
    rw [← x0] at a0 a1
    rw [← x1] at b0 b1
    refine ⟨?_, ?_⟩
    · rw [M5, qword_macE hk (by rw [x5, (A1 k hk).1, a0, b0]; exact prod_bound hc hA hB (by omega) (by omega)), x5,
        (A1 k hk).1, a0, b0]
      rfl
    · rw [M6, qword_macO hk (by rw [x6, (A1 k hk).2, a1, b1]; exact prod_bound hc hA hB (by omega) (by omega)), x6,
        (A1 k hk).2, a1, b1]
      rfl

theorem dotPlain_ok {s : State} (hc : VConsts s) :
    WP isa (.block dotPlain) s fun s' => s'.xmm .xmm5 = csubV (montV (s.xmm .xmm5) (s.xmm .xmm11) (s.xmm .xmm11)) ∧
      XOnly [.xmm2, .xmm4, .xmm5] s s' := by
  simp only [dotPlain, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

/-- The sum times `2⁻³²`, times `2⁶⁴` times `2⁻³²`: the sum modulo `q`. -/
theorem plain_dw {x : BitVec 128} {P : Nat} {e : Nat} (he : e < 4)
    (hx : (dword x e).toNat = (Fin.ofNat q P * montgomeryRInv).val) :
    (dword (csubV (montV x r2V r2V)) e).toNat = (Fin.ofNat q P : Zq).val := by
  have hzo : ∀ j < 2, dword r2V (2 * j) = dword r2V (2 * j + 1) := fun j hj => by
    rw [dword_r2V (by omega), dword_r2V (by omega)]
  have hb : ∀ i < 4, (dword x i).toNat * (dword r2V i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [dword_r2V hi]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (dword x i).isLt (Nat.le_refl _) (by decide)) (by decide)
  have hm := dword_montV hzo hb he
  rw [dword_csubV _ he, csubL_toNat (by rw [hm]; exact mont_lt (hb e he)), hm, condSub_mont (hb e he), mont_inverse,
    dword_r2V he, hx]
  have h3 : ∀ (z : Zq) (a b : Nat), a < q → b < q → (z.val * a * b) % q = (z * Fin.ofNat q a * Fin.ofNat q b).val :=
    fun z a b ha hb => by
      rw [Fin.val_mul, Fin.val_mul, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
        Nat.mod_mul_mod]
  rw [show (2365951#32).toNat = 2365951 from rfl, h3 _ _ _ (by decide) (by decide), Fin.mul_assoc, Fin.mul_assoc,
    show montgomeryRInv * (Fin.ofNat q 2365951 * Fin.ofNat q 8265825) = 1 by decide, Fin.mul_one]

/-- Coefficient `k` of the sum of the products. -/
def dotP (m : VG.Mem) (a b : Addr) (c k : Nat) : Zq :=
  Fin.ofNat q (dsum (fun j => famV m a j k) (fun j => famV m b j k) c)

/-- After `i` iterations of the loop, from `s₀`. -/
structure DI (o a b : Addr) (c : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = coeffAddr o (4 * i)
  r10 : s.gpr .r10 = coeffAddr a (4 * i)
  rdx : s.gpr .rdx = coeffAddr b (4 * i)
  keep : Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s
  vc : VConsts s
  x11 : s.xmm .xmm11 = r2V
  frame : Frame [pR o] s₀.mem s.mem
  done : ∀ k < 4 * i, (coeffAt s.mem o k).toNat = (dotP s₀.mem a b c k).val

section
variable {o a b : Addr} {c : Nat} {s₀ : State} (hc7 : c ≤ 7) (hwo : pR o ∈ s₀.wr)
  (hra : ∀ j < c, ∀ k, k + 4 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (a + BitVec.ofNat 64 (1024 * j)) k) 16)
  (hrb : ∀ j < c, ∀ k, k + 4 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (b + BitVec.ofNat 64 (1024 * j)) k) 16)
  (hda : ∀ j < c, (pR (a + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hdb : ∀ j < c, (pR (b + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hA : ∀ j < c, ∀ k < 256, famV s₀.mem a j k < 3 * q) (hB : ∀ j < c, ∀ k < 256, famV s₀.mem b j k < 3 * q)
include hc7 hwo hra hrb hda hdb hA hB

theorem step {i : Nat} (hi : i < 64) {s : State} (hI : DI o a b c s₀ i s) :
    WP isa (.block (dotBodyS c ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      DI o a b c s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have hv : ∀ (p : Addr), (∀ j < c, (pR (p + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o)) → ∀ j < c,
      ∀ e < 4, (dword (s.mem.readW (coeffAddr p (4 * i) + BitVec.ofNat 64 (1024 * j)) 128) e).toNat =
        famV s₀.mem p j (4 * i + e) := fun p hd j hj e he => by
    rw [addr_fam, dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, famV,
      coeffAt_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd j hj) (by rw [n_eq]; omega)]
  simp only [dotBodyS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (dotZero_ok s) fun s1 ⟨z5, z6, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (macs_ok hc7 (Av := fun j t => famV s₀.mem a j (4 * i + t)) (Bv := fun j t => famV s₀.mem b j (4 * i + t))
    (fun j hj t ht => hA j hj _ (by omega)) (fun j hj t ht => hB j hj _ (by omega))
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.r10, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hra j hj _ j0)
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.rdx, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hrb j hj _ j0)
    (fun j hj e he => by rw [o1.mem, o1.gpr, hI.r10]; exact hv a hda j hj e he)
    (fun j hj e he => by rw [o1.mem, o1.gpr, hI.rdx]; exact hv b hdb j hj e he)
    (fun k hk => by rw [z5, z6]; exact ⟨by simp [qword, dsum], by simp [qword, dsum]⟩) c (Nat.le_refl _))
    fun s2 ⟨A2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (dotRed_ok (xonly_vconsts o12 hI.vc (by decide) (by decide))) fun s3 ⟨R3, o3⟩ => ?_
  have o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (dotPlain_ok (xonly_vconsts o13 hI.vc (by decide) (by decide))) fun s4 ⟨P4, o4⟩ => ?_
  have o14 := o13.trans o4
  have x11 : s3.xmm .xmm11 = r2V := by rw [o13.xmm _ (by decide), hI.x11]
  have hres : ∀ e < 4, (dword (s4.xmm .xmm5) e).toNat = (dotP s₀.mem a b c (4 * i + e)).val := by
    intro e he
    rw [P4, x11]
    refine plain_dw he ?_
    rw [R3, dot_lane (A := fun j t => famV s₀.mem a j (4 * i + t)) (B := fun j t => famV s₀.mem b j (4 * i + t)) hc7
      (fun j hj t ht => hA j hj _ (by omega)) (fun j hj t ht => hB j hj _ (by omega))
      (fun k hk => (A2 k hk).1) (fun k hk => (A2 k hk).2) he]
  have g4 : s4.gpr .r8 = coeffAddr o (4 * i) := by rw [o14.gpr, hI.r8]
  have w0 : InRegions s4.wr (coeffAddr o (4 * i)) 16 := by rw [o14.wr, hI.keep.2.2]; exact f_in hwo j0
  vrund [g4, w0]
  rw [o14.mem]
  have p16 : ∀ p : Addr, coeffAddr p (4 * i) + 16 = coeffAddr p (4 * (i + 1)) := fun p => by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  refine ⟨⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, fun k hk => ?_⟩, by rw [o14.gpr], by rw [o14.gpr]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact p16 o
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o14.gpr, hI.r10]; exact p16 a
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o14.gpr, hI.rdx]; exact p16 b
  · have hr0 := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    rw [o14.gpr, hI.keep.1 r hr0]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [o14.rd, hI.keep.2.1]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [o14.wr, hI.keep.2.2]
  · exact ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide)]; exact hI.vc.q,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide)]; exact hI.vc.qinv⟩
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide), hI.x11]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains o j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [coeffAt_write128 _ _ j0 _ (by omega)]
    split
    · rw [hres _ (by omega), show 4 * i + (k - 4 * i) = k by omega]
    · exact hI.done k (by omega)


/-- The loop, from the constants and the pointers, in `s₀`. -/
theorem pass_ok (h8 : s₀.gpr .r8 = o) (h10 : s₀.gpr .r10 = a) (hdx : s₀.gpr .rdx = b) (hc : VConsts s₀)
    (h11 : s₀.xmm .xmm11 = r2V) :
    WP isa (rcxLoop 64 (dotBodyS c)) s₀ fun s' => PolyIs s'.mem o (Vector.ofFn fun k => dotP s₀.mem a b c k.val) ∧
      Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s' ∧ Frame [pR o] s₀.mem s'.mem := by
  refine WP.mono (wp_rcxLoop (N := 64) (by decide) (by decide) (DI o a b c s₀)
    (fun u og _ => ⟨by rw [og.keep.gpr (by decide), h8, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), h10, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      og.keep.mono (by simp), ⟨by rw [og.xmm]; exact hc.q, by rw [og.xmm]; exact hc.qinv⟩,
      by rw [og.xmm]; exact h11, by rw [og.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩)
    (fun i hi u hI => step hc7 hwo hra hrb hda hdb hA hB hi hI)) fun u hI => ⟨⟨fun k hk => ?_, ?_⟩, hI.keep, hI.frame⟩
  · rw [n_eq] at hk
    rw [hI.done k (by omega)]; exact (dotP s₀.mem a b c k).isLt
  · apply Vector.ext; intro k hk
    rw [polyAt, Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply Fin.ext
    rw [Fin.val_ofNat, hI.done k (by rw [n_eq] at hk; omega), Nat.mod_eq_of_lt (dotP s₀.mem a b c k).isLt]

end

/-! ## The function -/

/-- The result: the sums. -/
theorem dotP_eq {m m' : VG.Mem} {a b : Addr} {c : Nat}
    (ha : ∀ j < c, ∀ k < 256, coeffAt m' (a + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (a + BitVec.ofNat 64 (1024 * j)) k)
    (hb : ∀ j < c, ∀ k < 256, coeffAt m' (b + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (b + BitVec.ofNat 64 (1024 * j)) k) :
    (Vector.ofFn fun k => dotP m' a b c k.val) = Proof.MlDsa.dotNTT
      (fun j => polyAt m (a + BitVec.ofNat 64 (1024 * j))) (fun j => polyAt m (b + BitVec.ofNat 64 (1024 * j))) c := by
  apply Vector.ext; intro k hk
  rw [Vector.getElem_ofFn, ← getElem!_pos (Proof.MlDsa.dotNTT _ _ c) k hk,
    dotNTT_get (A := fun j => famV m' a j k) (B := fun j => famV m' b j k) hk
    (fun j hj => by rw [polyAt_get _ _ hk, famV, ha j hj k hk]) (fun j hj => by rw [polyAt_get _ _ hk, famV, hb j hj k hk])]
  rfl

theorem correct {c : Nat} (hc7 : c ≤ 7)
    (hk : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi]) (dotInvSse2 c) = true)
    (hk' : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10])
      (.seq (.block (mulPro ++ ([.mov .r8 (.reg .rdi)] : List Instr))) (.seq (rcxLoop 64 (dotBodyS c)) nttInvBody)) = true)
    (hctl : ctlOk (dotInvSse2 c) = true) (s : State) (hs : (dotK c).pre s) :
    ∃ t s', Exec isa (dotInvSse2 c) s t s' ∧ abiPreserved s s' ∧ (dotK c).post s s' := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, pa, pb⟩ := hs
  have hwo : pR (s.gpr .rdi) ∈ s.wr := by rw [hwr]; simp
  have hws : pR (s.gpr .rcx) ∈ s.wr := by rw [hwr]; simp
  have hW : WP isa (dotInvSse2 c) s fun s' => PolyIs s'.mem (s.gpr .rdi) (Spec.MlDsa.nttInv (Proof.MlDsa.dotNTT
      (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
      (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .r10 = s.gpr .rsi ∧ w.gpr .rsi = s.gpr .rcx ∧
        GOnly [.r10, .rsi] s w)
      (by vrund; gonlyd) fun w ⟨h10, hsi, og⟩ => ?_)
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
    refine WP.mono (mulPro_ok s1) fun s2 ⟨c2, x2, _, k2, m2⟩ => ?_
    have hdi2 : s2.gpr .rdi = s.gpr .rdi := by rw [k2.gpr (by decide), hdi1]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .r8 = s.gpr .rdi ∧ GOnly [.r8] s2 s3)
      (by vrund [hdi2]; gonlyd) fun s3 ⟨h8, og3⟩ => ?_
    have c3 : VConsts s3 := ⟨by rw [og3.xmm]; exact c2.q, by rw [og3.xmm]; exact c2.qinv⟩
    have x3 : s3.xmm .xmm11 = r2V := by rw [og3.xmm]; exact x2
    have k13 : Keep [.rax, .r8] s1 s3 := (k2.trans og3.keep).mono (by simp)
    have m3 : s3.mem = s1.mem := by rw [og3.mem, m2]
    have hr : ∀ p : Addr, famR p c ∈ s.rd → ∀ j < c, ∀ k, k + 4 ≤ 256 →
        InRegions (s3.rd ++ s3.wr) (coeffAddr (p + BitVec.ofNat 64 (1024 * j)) k) 16 := fun p hp j hj k hk =>
      ⟨famR p c, by rw [k13.2.1, rd1]; exact List.mem_append_left _ hp, by
        rw [coeffAddr, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.seq (WP.mono (pass_ok (s₀ := s3) hc7 (by rw [k13.2.2, wr1]; exact hwo)
      (hr _ (by rw [hrd]; simp)) (hr _ (by rw [hrd]; simp))
      (fun j hj => (d1.sub_right (fam_sub _ hj)).symm) (fun j hj => (d2.sub_right (fam_sub _ hj)).symm)
      (fun j hj k hk => by rw [famV, m3, hm _ d4 j hj k hk]; exact pa j hj k (by rw [n_eq]; exact hk))
      (fun j hj k hk => by rw [famV, m3, hm _ d5 j hj k hk]; exact pb j hj k (by rw [n_eq]; exact hk))
      h8 (by rw [k13.gpr (by decide), h101]) (by rw [k13.gpr (by decide), hdx1]) c3 x3) fun u ⟨hP, ku, fu⟩ => ?_)
    refine WP.mono (invBody_ok (by rw [ku.gpr (by decide), k13.gpr (by decide), hdi1])
      (by rw [ku.gpr (by decide), k13.gpr (by decide), hsi1]) hP
      (by rw [ku.2.2, k13.2.2, wr1]; exact hwo) (by rw [ku.2.2, k13.2.2, wr1]; exact hws) d3) fun v ⟨hv, fv⟩ => ⟨?_, ?_⟩
    · rw [dotP_eq (m := s.mem) (fun j hj k hk => by rw [m3, hm _ d4 j hj k hk])
        (fun j hj k hk => by rw [m3, hm _ d5 j hj k hk])] at hv
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

theorem ct4 : ConstantTime isa (dotK 4).pre (dotK 4).pub (dotInvSse2 4) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 4) (by taint_decide)

theorem verified4 : Verified X86_64.target (dotInvSse2 4) (Proof.MlDsa.dotInverseContract 4 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct4
    (by dot_implies dotSat 4)

theorem ct5 : ConstantTime isa (dotK 5).pre (dotK 5).pub (dotInvSse2 5) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 5) (by taint_decide)

theorem verified5 : Verified X86_64.target (dotInvSse2 5) (Proof.MlDsa.dotInverseContract 5 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct5
    (by dot_implies dotSat 5)

theorem ct7 : ConstantTime isa (dotK 7).pre (dotK 7).pub (dotInvSse2 7) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 7) (by taint_decide)

theorem verified7 : Verified X86_64.target (dotInvSse2 7) (Proof.MlDsa.dotInverseContract 7 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ct7
    (by dot_implies dotSat 7)

end VG.Proof.MlDsa.X86_64.Arith.DotS
