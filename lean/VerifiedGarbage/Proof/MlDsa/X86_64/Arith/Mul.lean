import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr`. -/
section

/-!
# ML-DSA on x86-64: MXCSR through the end of a polynomial

`withMxcsr r 1016 c` (ML-KEM's, see `Impl/MlKem/X86_64/Vec.lean`) through the
last 8 bytes `mxH` of a writable polynomial at `r` (`withMxcsrH_ok`), as
ML-KEM's `withMxcsr_ok` through `scratch + 768`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ldmxcsr_ok)

/-- The last 8 bytes of the polynomial at `p`. -/
abbrev mxH (p : Addr) : Region := ⟨p + BitVec.ofNat 64 1016, 8⟩

theorem mxH_in {p : Addr} {rs : List Region} (hw : pR p ∈ rs) (d : Nat) (hd : 1016 ≤ d ∧ d ≤ 1020) :
    InRegions rs (p + BitVec.ofNat 64 d) 4 :=
  ⟨_, hw, Offset.contains_base p (by omega) (by omega)⟩

theorem mxH_sub (p : Addr) : Region.Sub (VG.Proof.MlDsa.X86_64.Arith.mxH p) (pR p) := Offset.sub_base p (by decide)

/-- `withMxcsr` through `mxH`: `c` runs from `s` but for `rax`, `r11` and
those bytes, and nothing more than they and MXCSR change after it. -/
theorem withMxcsrH_ok {c : Prog isa} {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .rax) (rs : List Reg)
    (hrs : r ∉ rs ∧ Reg.r11 ∉ rs) {p : Addr} {s : State} {Q : State → Prop}
    (hsi : s.gpr r = p) (hw : pR p ∈ s.wr) (hk : writesOnly rs c = true)
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [VG.Proof.MlDsa.X86_64.Arith.mxH p] s.mem s1.mem → s1.xmm = s.xmm → s1.ymmHi = s.ymmHi →
      WP isa c s1 Q) :
    WP isa (withMxcsr r 1016 c) s fun s' =>
      ∃ s2, Q s2 ∧ Frame [VG.Proof.MlDsa.X86_64.Arith.mxH p] s2.mem s'.mem ∧ Keep [] s2 s' ∧ s'.xmm = s2.xmm ∧ s'.ymmHi = s2.ymmHi := by
  have h0 := VG.Proof.MlDsa.X86_64.Arith.mxH_in hw 1016 (by decide)
  have h0' := VG.Proof.MlDsa.X86_64.Arith.mxH_in (List.mem_append_right s.rd hw) 1016 (by decide)
  have h4 := VG.Proof.MlDsa.X86_64.Arith.mxH_in hw 1020 (by decide)
  simp only [withMxcsr]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.r11] s s1 ∧
    Frame [VG.Proof.MlDsa.X86_64.Arith.mxH p] s.mem s1.mem ∧ s1.xmm = s.xmm ∧ s1.ymmHi = s.ymmHi) (by
      vrunm [hsi, h0, h0', Mem.readW_writeW_self32, hr.1]
      refine ⟨by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq],
        ⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains p (by decide) (by decide) (by decide)),
        by simp only [RegUpd.ymmHi_setReg, RegUpd.ymmHi_setFlags]⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h11, k1, f1, x1, y1⟩ => ?_)
  have hsi1 : s1.gpr r = p := by rw [k1.gpr (by simpa using hr.1), hsi]
  have h4' : InRegions s1.wr (p + BitVec.ofNat 64 (1016 + 4)) 4 := by rw [k1.2.2]; exact h4
  have h4'' : InRegions (s1.rd ++ s1.wr) (p + BitVec.ofNat 64 (1016 + 4)) 4 :=
    let ⟨r, hr, hc⟩ := h4'; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.seq (WP.mono (Q := fun (s2 : State) => Keep [.rax] s1 s2 ∧ Frame [VG.Proof.MlDsa.X86_64.Arith.mxH p] s1.mem s2.mem ∧
      s2.xmm = s1.xmm ∧ s2.ymmHi = s1.ymmHi)
    (by
      vrunm [hsi1, h4', h4'', Mem.readW_writeW_self32, hr.2]
      refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains p (by decide) (by decide) (by decide)), by simp only [RegUpd.ymmHi_setReg]⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s2 ⟨k2, f2, x2, y2⟩ => ?_))
  refine WP.seq (WP.mono (WP.keep _ (hc s2 ((k1.trans k2).mono (by simp)) (f1.trans f2) (x2.trans x1)
    (y2.trans y1)) hk)
    fun s3 ⟨hq, k3⟩ => ?_)
  have k23 := k2.trans k3
  have hsi3 : s3.gpr r = p := by rw [k23.gpr (by simp [hr.2, hrs.1]), hsi1]
  have h113 : s3.gpr .r11 = BitVec.setWidth 64 (s.mxcsr &&& 65535) := by rw [k23.gpr (by simp [hrs.2]), h11]
  have h03 : InRegions s3.wr (p + BitVec.ofNat 64 1016) 4 := by rw [k23.2.2, k1.2.2]; exact h0
  have h03' : InRegions (s3.rd ++ s3.wr) (p + BitVec.ofNat 64 1016) 4 :=
    let ⟨r, hr, hc⟩ := h03; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (Q := fun s4 => s4 = s3) (by vrunm) fun s4 h4 => ?_
  subst h4
  vrunm [hsi3, h113, h03, h03', Mem.readW_writeW_self32, ldmxcsr_ok]
  exact ⟨_, hq, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains p (by decide) (by decide) (by decide)), ⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21`. -/
section

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len` = 2 and 1

The layer with `len = 2` runs two blocks at a time (`vstep2`): the lower
halves of their coefficients gathered into `xmm0` and the upper ones into
`xmm1` by `punpcklqdq` and `punpckhqdq`, and back. The layer with `len = 1`
runs four blocks at a time (`vstep1`): their coefficients gathered by `pshufd`
and `punpck{l,h}qdq`, and interleaved back by `punpck{l,h}dq`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm mxcsr_setXmm ifp ifn sel sel_lt add_ofNat_zero Keep GOnly
  wp_rcxLoop sx32)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

theorem dword_punpcklqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpcklqdq a b) j = if j < 2 then dword a j else dword b (j - 2) := by
  rw [punpcklqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceSub, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_punpckhqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhqdq a b) j = if j < 2 then dword a (2 + j) else dword b j := by
  rw [punpckhqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceAdd, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_punpckldq' (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckldq a b) j = if j % 2 = 0 then dword a (j / 2) else dword b (j / 2) := by
  rw [dword_punpckldq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp

theorem dword_punpckhdq' (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhdq a b) j = if j % 2 = 0 then dword a (2 + j / 2) else dword b (2 + j / 2) := by
  rw [dword_punpckhdq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp

/-- The doublewords of `x` that `pshufd` with `0xD8` puts in place `e`: the
even ones in the lower half, the odd ones in the upper half. -/
theorem dword_d8 (x : BitVec 128) {e : Nat} (he : e < 4) :
    dword (shufDwords x 0xD8) e = dword x (if e < 2 then 2 * e else 2 * (e - 2) + 1) := by
  rw [dword_shufDwords _ _ he]
  rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl

/-- The general-purpose registers but `rs`, memory, the permissions and
MXCSR are as they were. -/
structure GKeep (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr

/-! ## The layer with `len = 2` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : VG.Spec.MlDsa.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlDsa.Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The loads, the zetas and the gathering of the lower and upper halves. -/
abbrev pre2 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post2 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
    .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

theorem vstep2 {fP sP : Addr} {i kz : Nat} (hi : i < 32) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kz + 4 ≤ 256) (hsel : ∀ e < 4, kz + sel o e = zi (2 * i + e / 2))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = coeffAddr fP (8 * i))
    (h8 : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP (layF blk F 2 zi (2 * i)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.pre2 o dz ++ (bf ++ VG.Proof.MlDsa.X86_64.Arith.post2))) s fun s' =>
      PolyIs s'.mem fP (layF blk F 2 zi (2 * (i + 1))) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv fP s s' := by
  have j0 : 8 * i + 4 ≤ 256 := by omega
  have j1 : 8 * i + 4 + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 16 = coeffAddr fP (8 * i + 4) := coeffAddr_add _ _ 4
  have r0 := f_in (List.mem_append_right s.rd hwf) j0
  have r1 := f_in (List.mem_append_right s.rd hwf) j1
  have hk' : ∀ j < 4, kz + sel o j < 256 := fun j _ => by have := sel_lt o j; omega
  generalize hG : layF blk F 2 zi (2 * i) = G at hS
  have lx := dlanes_load hS j0
  have ly := dlanes_load hS j1
  rw [WP.block_append_iff, show VG.Proof.MlDsa.X86_64.Arith.pre2 o dz = [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++
    (vzeta o ++ [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1,
      xb .punpckhqdq .xmm2 .xmm1, xmov .xmm1 .xmm2]) by simp, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok o hk' (by simp only [RegUpd.gpr_setXmm]; exact h8)
    (by simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm]; exact tab_in (List.mem_append_right _ hw) hk)
    (by simp only [RegUpd.mem_setXmm]; exact hT)) fun s1 ⟨z1, zo1, o1⟩ => ?_
  refine WP.mono (Q := fun (s1' : State) => DLanes (s1'.xmm .xmm0) (fun e => G[8 * i + e + 2 * (e / 2)]!) ∧
      DLanes (s1'.xmm .xmm1) (fun e => G[8 * i + 2 + e + 2 * (e / 2)]!) ∧
      ZLanes (s1'.xmm .xmm13) (fun e => zetas (zi (2 * i + e / 2))) ∧ ZOdd (s1'.xmm .xmm13) (s1'.xmm .xmm12) ∧
      VConsts s1' ∧ s1'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ VG.Proof.MlDsa.X86_64.Arith.GKeep [.r8] s s1') ?_
    fun s1' ⟨l0, l1, l13, l12, c1, h81, o1'⟩ => ?_
  · have g1 : s1.gpr = s.gpr := by rw [o1.gpr]; rfl
    have m1 : s1.mem = s.mem := by rw [o1.mem]; rfl
    have e1 : s1.rd = s.rd ∧ s1.wr = s.wr := ⟨by rw [o1.rd]; rfl, by rw [o1.wr]; rfl⟩
    have x1 : s1.mxcsr = s.mxcsr := by rw [o1.mxcsr]; rfl
    have x0 : s1.xmm .xmm0 = s.mem.readW (coeffAddr fP (8 * i)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have x1' : s1.xmm .xmm1 = s.mem.readW (coeffAddr fP (8 * i + 4)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have c1 : VConsts s1 := xonly_vconsts o1 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide)
      (by decide) _) (by decide) (by decide)
    vrund [g1, m1, e1.1, e1.2, x1, eval_movdqa]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro e he
      rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he, x0, x1']
      split
      · rw [lx e he]; dsimp only; rw [show 8 * i + e + 2 * (e / 2) = 8 * i + e by omega]
      · rw [ly (e - 2) (by omega)]; dsimp only
        rw [show 8 * i + e + 2 * (e / 2) = 8 * i + 4 + (e - 2) by omega]
    · intro e he
      rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he, x0, x1']
      split
      · rw [lx (2 + e) (by omega)]; dsimp only
        rw [show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + (2 + e) by omega]
      · rw [ly e he]; dsimp only; rw [show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 4 + e by omega]
    · intro e he
      rw [z1 e he]; dsimp only; rw [hsel e he]
    · exact zo1
    · exact c1.q
    · exact c1.qinv
    · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, g1]
      rw [ifn (by simpa using hr)]
    all_goals simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags, e1.1, e1.2, m1, x1]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13 l12) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1'.keep.2.1], by rw [o2.wr, o1'.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1'.mem]
  have w0 := f_in hwf j0
  have w1 := f_in hwf j1
  have c2 := xonly_vconsts o2 c1 (by decide) (by decide)
  simp only [VG.Proof.MlDsa.X86_64.Arith.post2, xmov, xb]
  vrund [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the coefficients stored
    refine polyIs_write2 hS j0 j1 (by omega)
      (a := fun e => if e < 2 then (op G[8 * i + e]! G[8 * i + 2 + e]! (zetas (zi (2 * i)))).1
        else (op G[8 * i + (e - 2)]! G[8 * i + 2 + (e - 2)]! (zetas (zi (2 * i)))).2)
      (b := fun e => if e < 2 then (op G[8 * i + 4 + e]! G[8 * i + 6 + e]! (zetas (zi (2 * i + 1)))).1
        else (op G[8 * i + 4 + (e - 2)]! G[8 * i + 6 + (e - 2)]! (zetas (zi (2 * i + 1)))).2)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he]
      split
      · rw [a0 e he]; dsimp only
        rw [ite_eq_left (by omega), show 8 * i + e + 2 * (e / 2) = 8 * i + e by omega,
          show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 2 + e by omega, show 2 * i + e / 2 = 2 * i by omega]
      · rw [a3 (e - 2) (by omega)]; dsimp only
        rw [ite_eq_right (by omega), show 8 * i + (e - 2) + 2 * ((e - 2) / 2) = 8 * i + (e - 2) by omega,
          show 8 * i + 2 + (e - 2) + 2 * ((e - 2) / 2) = 8 * i + 2 + (e - 2) by omega,
          show 2 * i + (e - 2) / 2 = 2 * i by omega]
    · rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he, eval_movdqa]
      split
      · rw [a0 (2 + e) (by omega)]; dsimp only
        rw [ite_eq_left (by omega), show 8 * i + (2 + e) + 2 * ((2 + e) / 2) = 8 * i + 4 + e by omega,
          show 8 * i + 2 + (2 + e) + 2 * ((2 + e) / 2) = 8 * i + 6 + e by omega,
          show 2 * i + (2 + e) / 2 = 2 * i + 1 by omega]
      · rw [a3 e he]; dsimp only
        rw [ite_eq_right (by omega), show 8 * i + e + 2 * (e / 2) = 8 * i + 4 + (e - 2) by omega,
          show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 6 + (e - 2) by omega,
          show 2 * i + e / 2 = 2 * i + 1 by omega]
    · -- the specification: two blocks
      rw [← hG, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, layF, foldl_range_succ, foldl_range_succ, ← layF,
        hG, show 2 * 2 * (2 * i) = 8 * i by omega, show 2 * 2 * (2 * i + 1) = 8 * i + 4 by omega]
      have hn : ∀ j, j < 256 → j < n := fun j h => by rw [n_eq]; exact h
      rw [hblk.get _ _ _ _ _ (by decide) (by decide) (by rw [n_eq]; omega) _ (hn j hj)]
      have p2 := fun j (h : j < 256) => hblk.get G 2 (zi (2 * i)) (8 * i) 2 (by decide) (by decide)
        (by rw [n_eq]; omega) j (hn j h)
      rcases (by omega : j < 8 * i ∨ (8 * i ≤ j ∧ j < 8 * i + 2) ∨ (8 * i + 2 ≤ j ∧ j < 8 * i + 4) ∨
          (8 * i + 4 ≤ j ∧ j < 8 * i + 6) ∨ (8 * i + 6 ≤ j ∧ j < 8 * i + 8) ∨ 8 * i + 8 ≤ j) with
        h | h | h | h | h | h
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 8 * i + (j - 8 * i) = j by omega, show 8 * i + 2 + (j - 8 * i) = j + 2 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 8 * i + (j - 8 * i - 2) = j - 2 by omega, show 8 * i + 2 + (j - 8 * i - 2) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j + 2) (by omega)]
        rw [show 8 * i + 4 + (j - (8 * i + 4)) = j by omega,
          show 8 * i + 6 + (j - (8 * i + 4)) = j + 2 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j - 2) (by omega)]
        rw [show 8 * i + 4 + (j - (8 * i + 4) - 2) = j - 2 by omega,
          show 8 * i + 6 + (j - (8 * i + 4) - 2) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1'.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1'.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv

omit hbf hblk in
/-- The prologue of the layers with `len` = 2 and 1. -/
theorem vpre21 {fP sP : Addr} (k : Nat) (hk : k + 4 ≤ 256) {s : State} (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ leaR .r8 .rsi (4 * k))) s fun w =>
      w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧ GOnly [.rdx, .r8] s w := by
  simp only [leaR]
  vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
  gonlyd

theorem vlay2_ok {fP sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 32, kz i + 4 ≤ 256) (hsel : ∀ i < 32, ∀ e < 4, kz i + sel o e = zi (2 * i + e / 2))
    (hstep : ∀ i < 32, coeffAddr sP (kz i) + BitVec.signExtend 64 dz = coeffAddr sP (kz (i + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (vlay2 bf k o dz) s fun s' => PolyIs s'.mem fP (layF blk F 2 zi 64) ∧ BInv fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.vpre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 2 zi (2 * i)) ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧
      u.gpr .r8 = coeffAddr sP (kz i) ∧ BInv fP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        gonly_vconsts ou (gonly_vconsts og hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++ vzeta o ++
      [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
        xmov .xmm1 .xmm2] ++ bf ++ [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = VG.Proof.MlDsa.X86_64.Arith.pre2 o dz ++ (bf ++ VG.Proof.MlDsa.X86_64.Arith.post2) by simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlDsa.X86_64.Arith.vstep2 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

/-! ## The layer with `len = 1` -/

/-- The loads, the zetas and the gathering of the coefficients. -/
abbrev pre1 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm2 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post1 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
    .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

theorem vstep1 {fP sP : Addr} {i kz : Nat} (hi : i < 32) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kz + 4 ≤ 256) (hsel : ∀ e < 4, kz + sel o e = zi (4 * i + e))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = coeffAddr fP (8 * i))
    (h8 : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP (layF blk F 1 zi (4 * i)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.pre1 o dz ++ (bf ++ VG.Proof.MlDsa.X86_64.Arith.post1))) s fun s' =>
      PolyIs s'.mem fP (layF blk F 1 zi (4 * (i + 1))) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv fP s s' := by
  have j0 : 8 * i + 4 ≤ 256 := by omega
  have j1 : 8 * i + 4 + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 16 = coeffAddr fP (8 * i + 4) := coeffAddr_add _ _ 4
  have r0 := f_in (List.mem_append_right s.rd hwf) j0
  have r1 := f_in (List.mem_append_right s.rd hwf) j1
  have hk' : ∀ j < 4, kz + sel o j < 256 := fun j _ => by have := sel_lt o j; omega
  generalize hG : layF blk F 1 zi (4 * i) = G at hS
  have lx := dlanes_load hS j0
  have ly := dlanes_load hS j1
  rw [WP.block_append_iff, show VG.Proof.MlDsa.X86_64.Arith.pre1 o dz = [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm2 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++
    (vzeta o ++ [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]) by simp, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok o hk' (by simp only [RegUpd.gpr_setXmm]; exact h8)
    (by simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm]; exact tab_in (List.mem_append_right _ hw) hk)
    (by simp only [RegUpd.mem_setXmm]; exact hT)) fun s1 ⟨z1, zo1, o1⟩ => ?_
  refine WP.mono (Q := fun (s1' : State) => DLanes (s1'.xmm .xmm0) (fun e => G[8 * i + 2 * e]!) ∧
      DLanes (s1'.xmm .xmm1) (fun e => G[8 * i + 2 * e + 1]!) ∧
      ZLanes (s1'.xmm .xmm13) (fun e => zetas (zi (4 * i + e))) ∧ ZOdd (s1'.xmm .xmm13) (s1'.xmm .xmm12) ∧
      VConsts s1' ∧ s1'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ VG.Proof.MlDsa.X86_64.Arith.GKeep [.r8] s s1') ?_
    fun s1' ⟨l0, l1, l13, l12, c1, h81, o1'⟩ => ?_
  · have g1 : s1.gpr = s.gpr := by rw [o1.gpr]; rfl
    have m1 : s1.mem = s.mem := by rw [o1.mem]; rfl
    have e1 : s1.rd = s.rd ∧ s1.wr = s.wr := ⟨by rw [o1.rd]; rfl, by rw [o1.wr]; rfl⟩
    have x1 : s1.mxcsr = s.mxcsr := by rw [o1.mxcsr]; rfl
    have x0 : s1.xmm .xmm0 = s.mem.readW (coeffAddr fP (8 * i)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have x2 : s1.xmm .xmm2 = s.mem.readW (coeffAddr fP (8 * i + 4)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have c1 : VConsts s1 := xonly_vconsts o1 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide)
      (by decide) _) (by decide) (by decide)
    vrund [g1, m1, e1.1, e1.2, x1, eval_movdqa]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro e he
      rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he, x0, x2]
      split
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ he, ite_eq_left (by omega), lx _ (by omega)]
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ (by omega), ite_eq_left (by omega), ly _ (by omega)]; dsimp only
        rw [show 8 * i + 4 + 2 * (e - 2) = 8 * i + 2 * e by omega]
    · intro e he
      rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he, x0, x2]
      split
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ (by omega), ite_eq_right (by omega), lx _ (by omega)]; dsimp only
        rw [show 8 * i + (2 * (2 + e - 2) + 1) = 8 * i + 2 * e + 1 by omega]
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ he, ite_eq_right (by omega), ly _ (by omega)]; dsimp only
        rw [show 8 * i + 4 + (2 * (e - 2) + 1) = 8 * i + 2 * e + 1 by omega]
    · intro e he
      rw [z1 e he]; dsimp only; rw [hsel e he]
    · exact zo1
    · exact c1.q
    · exact c1.qinv
    · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, g1]
      rw [ifn (by simpa using hr)]
    all_goals simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags, e1.1, e1.2, m1, x1]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13 l12) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1'.keep.2.1], by rw [o2.wr, o1'.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1'.mem]
  have w0 := f_in hwf j0
  have w1 := f_in hwf j1
  have c2 := xonly_vconsts o2 c1 (by decide) (by decide)
  simp only [VG.Proof.MlDsa.X86_64.Arith.post1, xmov, xb]
  vrund [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have lg : ∀ b, b ≤ 128 → ∀ j, j < 256 → _ := fun b hb j hj => layF1_get hblk F zi (b := b) hb (j := j) hj
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the coefficients stored
    refine polyIs_write2 hS j0 j1 (by omega)
      (a := fun e => (layF blk F 1 zi (4 * (i + 1)))[8 * i + e]!)
      (b := fun e => (layF blk F 1 zi (4 * (i + 1)))[8 * i + 4 + e]!)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpckldq' _ _ he]
      split
      · rw [a0 (e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (e / 2) = 8 * i + e by omega,
          show 4 * i + e / 2 = (8 * i + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (e / 2) = 8 * i + e - 1 by omega, show 8 * i + e - 1 + 1 = 8 * i + e by omega,
          show 4 * i + e / 2 = (8 * i + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rw [VG.Proof.MlDsa.X86_64.Arith.dword_punpckhdq' _ _ he, eval_movdqa]
      split
      · rw [a0 (2 + e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (2 + e / 2) = 8 * i + 4 + e by omega,
          show 4 * i + (2 + e / 2) = (8 * i + 4 + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (2 + e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (2 + e / 2) = 8 * i + 4 + e - 1 by omega,
          show 8 * i + 4 + e - 1 + 1 = 8 * i + 4 + e by omega,
          show 4 * i + (2 + e / 2) = (8 * i + 4 + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rcases (by omega : (8 * i ≤ j ∧ j < 8 * i + 4) ∨ (8 * i + 4 ≤ j ∧ j < 8 * i + 8) ∨
          j < 8 * i ∨ 8 * i + 8 ≤ j) with h | h | h | h
      · rw [ite_eq_left h, show 8 * i + (j - 8 * i) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_left h, show 8 * i + 4 + (j - (8 * i + 4)) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1'.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1'.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv

theorem vlay1_ok {fP sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 32, kz i + 4 ≤ 256) (hsel : ∀ i < 32, ∀ e < 4, kz i + sel o e = zi (4 * i + e))
    (hstep : ∀ i < 32, coeffAddr sP (kz i) + BitVec.signExtend 64 dz = coeffAddr sP (kz (i + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (vlay1 bf k o dz) s fun s' => PolyIs s'.mem fP (layF blk F 1 zi 128) ∧ BInv fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.vpre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 1 zi (4 * i)) ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧
      u.gpr .r8 = coeffAddr sP (kz i) ∧ BInv fP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        gonly_vconsts ou (gonly_vconsts og hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm2 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16)] ++ vzeta o ++
      [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
        xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2] ++ bf ++
      [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = VG.Proof.MlDsa.X86_64.Arith.pre1 o dz ++ (bf ++ VG.Proof.MlDsa.X86_64.Arith.post1) by simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlDsa.X86_64.Arith.vstep1 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt`

ML-KEM's `withMxcsr` runs its code from any MXCSR and keeps what it does
(`withMxcsr_ok`); the prologue leaves the table of zetas in `scratch` and the
constants (`vpro_ok`), each layer is `nttLayer` (`vlay_ok`, `vlay2_ok`,
`vlay1_ok`), and the eight layers are `NTT` (`ntt_eq_layers`). `LI`, `vpro_ok`
and `inPlaceSat` serve `NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of withMxcsr_ok mxR mx_sub xmm_setXmm
  GOnly add_ofNat_zero sel)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas ntt)

/-! ## The prologue -/

/-- A table of 256 `u32`s `t k`, stored at `sP` (in `r`), two at a time
through `r9`. -/
theorem dwordTab_ok (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {r : Reg} (hr : r ≠ .r9) {sP : Addr} {s : State}
    (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (dwordTab t 256 r)) s fun s' => Tab t s'.mem sP 256 ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr ∧ s'.xmm = s.xmm := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 128) (fun i w =>
      Tab t w.mem sP (2 * i) ∧ Frame [pR sP] s.mem w.mem ∧
        Keep [.r9] s w ∧ w.mxcsr = s.mxcsr ∧ w.xmm = s.xmm)
    (fun i w hi ⟨hT, hf, hk, hm, hx⟩ => ?_) 128 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _, Keep.refl _ _, rfl, rfl⟩)
    fun w ⟨hT, hf, hk, hm, hx⟩ => ⟨hT, hf, hk, hm, hx⟩
  have hsi' : w.gpr r = sP := by
    rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have w0 : InRegions w.wr (sP + BitVec.ofNat 64 (8 * i)) 8 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega) (by omega)⟩
  have hV : ∀ e < 2, (BitVec.ofNat 64 (t (2 * i) + 2 ^ 32 * t (2 * i + 1))).extractLsb' (32 * e) 32 =
      BitVec.ofNat 32 (t (2 * i + e)) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    have h0 := ht (2 * i)
    have h1 := ht (2 * i + 1)
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_zero]; omega
    · simp only [Nat.mul_one]; omega
  vrund [hsi', w0, hr]
  generalize BitVec.ofNat 64 (t (2 * i) + 2 ^ 32 * t (2 * i + 1)) = V at hV ⊢
  refine ⟨fun k hk' => ?_, hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base sP (by omega) (by omega)),
    ⟨fun r hr => ?_, hk.2.1, hk.2.2⟩, hm, hx⟩
  · by_cases h : 2 * i ≤ k
    · rw [coeffAt_eq, coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 * (k - 2 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega)),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega) (by decide),
        show 8 * (4 * (k - 2 * i)) = 32 * (k - 2 * i) by omega, hV _ (by omega),
        show 2 * i + (k - 2 * i) = k by omega]
    · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep sP (by omega) (by omega) (by omega)) (by decide)]
      exact hT k (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
    exact hk.1 r (by simp [hr])

theorem vconsts_ok (s : State) :
    WP isa (.block vconsts) s fun s' => VConsts s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr := by
  simp only [vconsts]
  vrund
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true]; decide
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]

/-- The table of zetas and the constants. -/
theorem vpro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block vpro) s fun s' => Tab zmTab s'.mem sP 256 ∧ VConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [vpro, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.dwordTab_ok zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1, _⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Arith.vconsts_ok s1) fun s2 ⟨hc, k2, m2, x2⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-! ## The layers -/

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants. -/
structure LI (fP sP : Addr) (s₀ : State) (F : VG.Spec.MlDsa.Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : VConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- The last layer. -/
theorem LI.last {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l : Prog isa}
    {F F' : VG.Spec.MlDsa.Poly}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.LI fP sP s₀ F s) : WP isa l s (VG.Proof.MlDsa.X86_64.Arith.LI fP sP s₀ F') :=
  WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩

/-- A layer, then `c`. -/
theorem LI.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : VG.Spec.MlDsa.Poly} {Q : State → Prop}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    (hc : ∀ s, VG.Proof.MlDsa.X86_64.Arith.LI fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.LI fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem step_fwd (p : Addr) (a d : Nat) {dz : BitVec 32} (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (4 * d)) :
    coeffAddr p a + BitVec.signExtend 64 dz = coeffAddr p (a + d) := by
  rw [h, coeffAddr_add]

theorem step_bwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (4 * d) + BitVec.signExtend 64 dz = 0) :
    coeffAddr p (a + d) + BitVec.signExtend 64 dz = coeffAddr p a := by
  rw [← coeffAddr_add, BitVec.add_assoc, h]; exact BitVec.add_zero _

/-- The block of `NTT`. -/
abbrev fwdBlk : VG.Spec.MlDsa.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlDsa.Poly := fun f len k st t => blockN bfly f len (zetas k) st t

theorem nttLayer_eq (F : VG.Spec.MlDsa.Poly) (len : Nat) :
    nttLayer F len = layF VG.Proof.MlDsa.X86_64.Arith.fwdBlk F len (fun c => 128 / len + c) (128 / len) := rfl

/-- A layer of `NTT` with `len ≥ 4`, whose first zeta is `zetas k`. -/
theorem fwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat) (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (hk : 128 / len = k)
    {F : VG.Spec.MlDsa.Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vbfly len k 4) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  rw [VG.Proof.MlDsa.X86_64.Arith.nttLayer_eq]
  exact vlay_ok vbfly_spec nttBlk_ok hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => VG.Proof.MlDsa.X86_64.Arith.step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem fwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : VG.Spec.MlDsa.Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vbfly 64 0x50 8) s fun s' => PolyIs s'.mem fP (nttLayer F 2) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0x50 e = e / 2 := by decide
  rw [VG.Proof.MlDsa.X86_64.Arith.nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact VG.Proof.MlDsa.X86_64.Arith.vlay2_ok vbfly_spec nttBlk_ok 64 0x50 8 (fun c => 64 + c) (fun i => 64 + 2 * i) rfl
    (fun i _ => by omega) (fun i _ e he => by rw [hs e he]; omega)
    (fun i _ => (VG.Proof.MlDsa.X86_64.Arith.step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem fwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : VG.Spec.MlDsa.Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay1 vbfly 128 0xE4 16) s fun s' => PolyIs s'.mem fP (nttLayer F 1) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0xE4 e = e := by decide
  rw [VG.Proof.MlDsa.X86_64.Arith.nttLayer_eq, show 128 / 1 = 128 from rfl]
  exact VG.Proof.MlDsa.X86_64.Arith.vlay1_ok vbfly_spec nttBlk_ok 128 0xE4 16 (fun c => 128 + c) (fun i => 128 + 4 * i) rfl
    (fun i _ => by omega) (fun i _ e he => by rw [hs e he]; omega)
    (fun i _ => (VG.Proof.MlDsa.X86_64.Arith.step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

/-! ## `vg_mldsa_ntt` -/

theorem mx_sub' (sP : Addr) : Region.Sub (mxR sP) (pR sP) := mx_sub sP

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- The code in `withMxcsr`, from its state `s1`: the prologue, then the
layers `l`, which leave `F`, then `NTT⁻¹`'s scaling or nothing. -/
theorem nttBody_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {s s1 : State} (hs : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).pre s) {l : Prog isa} {G : VG.Spec.MlDsa.Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, VG.Proof.MlDsa.X86_64.Arith.LI (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => VG.Proof.MlDsa.X86_64.Arith.LI (s.gpr .rdi) (s.gpr .rsi) s2 G s3) :
    WP isa (.seq (.block vpro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (VG.Proof.MlDsa.X86_64.Arith.mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.vpro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 hI => ⟨hI.P, ?_⟩
  refine (VG.Proof.MlDsa.X86_64.Arith.frame_fs f1 ?_).trans ((VG.Proof.MlDsa.X86_64.Arith.frame_fs hf2 ?_).trans (VG.Proof.MlDsa.X86_64.Arith.frame_fs hI.frame ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (VG.Proof.MlDsa.X86_64.Arith.mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- `withMxcsr` around the body, and the ABI. -/
theorem mx_correct {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {l : Prog isa} (s : State) (hs : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).pre s)
    (hk : writesOnly [.rax, .rcx, .rdx, .r8, .r9] (.seq (.block vpro) l) = true)
    (hctl : ctlOk (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) = true)
    (hk' : writesOnly [.rax, .rcx, .rdx, .r8, .r9, .r11]
      (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block vpro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) s tr s' ∧
      abiPreserved s s' ∧ (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := withMxcsr_ok (c := .seq (.block vpro) l) (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw
    hk (hl)
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW hk'
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Arith.mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (VG.Proof.MlDsa.X86_64.Arith.mx_sub' _)) hP

theorem ntt_correct (s : State) (hs : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.ntt s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlDsa.X86_64.Arith.inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine VG.Proof.MlDsa.X86_64.Arith.mx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (VG.Proof.MlDsa.X86_64.Arith.nttBody_ok hs k1 f1 (G := nttLens.foldl nttLayer (polyAt s.mem (s.gpr .rdi)))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [ntt_eq_layers]; exact hP, hf⟩
  simp only [nttLens, List.foldl_cons, List.foldl_nil]
  refine LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay_ok hd 4 32 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay2_ok hd) ?_ hI
  exact fun _ hI => LI.last hdi hsi hwf hw hd (VG.Proof.MlDsa.X86_64.Arith.fwdLay1_ok hd) hI

/-- The pointers and `rsp` are public. -/
theorem inPlace_agree {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} (s₁ s₂ : State) (_ : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).pre s₁) (_ : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).pre s₂)
    (hp : (VG.Proof.MlDsa.X86_64.Arith.inPlaceK t).pub s₁ s₂) : X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem ntt_ct : ConstantTime isa (VG.Proof.MlDsa.X86_64.Arith.inPlaceK ntt).pre (VG.Proof.MlDsa.X86_64.Arith.inPlaceK ntt).pub Impl.MlDsa.X86_64.Arith.ntt :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) VG.Proof.MlDsa.X86_64.Arith.inPlace_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.ntt (Spec.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.ntt_correct VG.Proof.MlDsa.X86_64.Arith.ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, VG.Proof.MlDsa.X86_64.Arith.inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using VG.Proof.MlDsa.X86_64.Arith.inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

A doubleword of `mulV x y` is the product of those of `x` and `y`
(`mul_lane`): `mont` of `mont` of their product by `2⁶⁴ mod q`
(`mont_mont_R2`). The loop stores four of them at a time to the first 252
coefficients of `h` (`Mul.step`, `Mul.loop_ok`), inside `withMxcsr` through
the last 8 bytes of `h`; the last four are computed from the coefficients of
`h` loaded before (`Mul.last`), and stored after MXCSR is loaded back
(`Mul.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly WP.keep writesOnly gprPreserved_of ifn xmm_setXmm wp_rcxLoop
  add_ofNat_zero)
open VG.Impl.MlKem.X86_64 (xb xmov rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced)

/-! ## Four products -/

/-- `2⁶⁴ mod q` in each doubleword, as the prologue leaves it in `xmm11`. -/
def r2V : BitVec 128 := shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 2365951#32) 0

theorem dword_r2V {i : Nat} (hi : i < 4) : dword VG.Proof.MlDsa.X86_64.Arith.r2V i = 2365951#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

/-- What `mulCore` leaves in `xmm3` of the vectors of `f` and `g`. -/
def mulV (x y : BitVec 128) : BitVec 128 := csubV (montV (montV x y (shufDwords y 0xF5)) VG.Proof.MlDsa.X86_64.Arith.r2V VG.Proof.MlDsa.X86_64.Arith.r2V)

/-- What `mulAddCore` leaves in `xmm3`, with the vector of `h`. -/
def mulAddV (x y z : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddd (VG.Proof.MlDsa.X86_64.Arith.mulV x y) z)

theorem mul_lane {x y : BitVec 128} {a b : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b) {i : Nat}
    (hi : i < 4) : (dword (VG.Proof.MlDsa.X86_64.Arith.mulV x y) i).toNat = (a i * b i).val := by
  have hzo : ZOdd y (shufDwords y 0xF5) := fun j hj => by
    rw [dword_shufDwords _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have hb1 : ∀ i < 4, (dword x i).toNat * (dword y i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [hx i hi, hy i hi]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (a i)) (Nat.le_of_lt (val_lt (b i)))
      (by decide)) (by decide)
  have m1 := fun i (hi : i < 4) => dword_montV hzo hb1 hi
  have hb2 : ∀ i < 4, (dword (montV x y (shufDwords y 0xF5)) i).toNat * (dword VG.Proof.MlDsa.X86_64.Arith.r2V i).toNat < q * 2 ^ 32 :=
    fun i hi => by
      rw [m1 i hi, VG.Proof.MlDsa.X86_64.Arith.dword_r2V hi]
      have := mont_lt (hb1 i hi)
      rw [q_eq] at this ⊢
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le this (Nat.le_refl 2365951) (by decide)) (by decide)
  have hzo2 : ZOdd VG.Proof.MlDsa.X86_64.Arith.r2V VG.Proof.MlDsa.X86_64.Arith.r2V := fun j hj => by rw [VG.Proof.MlDsa.X86_64.Arith.dword_r2V (by omega), VG.Proof.MlDsa.X86_64.Arith.dword_r2V (by omega)]
  rw [VG.Proof.MlDsa.X86_64.Arith.mulV, dword_csubV _ hi, csubL_toNat (by rw [dword_montV hzo2 hb2 hi]; exact mont_lt (hb2 i hi)),
    dword_montV hzo2 hb2 hi, condSub_mont (hb2 i hi), m1 i hi, VG.Proof.MlDsa.X86_64.Arith.dword_r2V hi,
    show (2365951#32).toNat = 2 ^ 64 % q from rfl, mont_mont_R2, hx i hi, hy i hi, val_mul]

theorem mulAdd_lane {x y z : BitVec 128} {a b c : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b)
    (hz : DLanes z c) {i : Nat} (hi : i < 4) : (dword (VG.Proof.MlDsa.X86_64.Arith.mulAddV x y z) i).toNat = (c i + a i * b i).val := by
  have hm := VG.Proof.MlDsa.X86_64.Arith.mul_lane hx hy hi
  rw [VG.Proof.MlDsa.X86_64.Arith.mulAddV, dword_csubV _ hi, dword_paddd _ _ hi, addD_toNat (by rw [hm]; exact val_lt _)
    (by rw [hz i hi]; exact val_lt _), hm, hz i hi, Nat.add_comm, ← val_add]

theorem mulCore_ok {s : State} (hc : VConsts s) (h11 : s.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V) :
    WP isa (.block mulCore) s fun s' =>
      s'.xmm .xmm3 = VG.Proof.MlDsa.X86_64.Arith.mulV (s.xmm .xmm3) (s.xmm .xmm13) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [mulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, h11]
  exact ⟨rfl, by xonly⟩

theorem mulAddCore_ok {s : State} (hc : VConsts s) (h11 : s.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V) :
    WP isa (.block mulAddCore) s fun s' =>
      s'.xmm .xmm3 = VG.Proof.MlDsa.X86_64.Arith.mulAddV (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧
        XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [mulAddCore, mulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, h11]
  exact ⟨rfl, by xonly⟩

theorem mulPro_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Arith.mulPro) s fun s' => VConsts s' ∧ s'.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V ∧ s'.xmm .xmm6 = s.xmm .xmm6 ∧
      Keep [.rax] s s' ∧ s'.mem = s.mem := by
  simp only [VG.Impl.MlDsa.X86_64.Arith.mulPro, vconsts, List.cons_append, List.nil_append]
  vrund
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]

/-! ## The loop -/

namespace Mul

theorem ptr16 (p : Addr) (i : Nat) : coeffAddr p (4 * i) + 16 = p + BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [coeffAddr, BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2; omega

/-- After `i` iterations: the first `4i` coefficients of `h` are `R`'s, the
others as they were in `s₀`. -/
structure Inv (h f g : Addr) (s₀ : State) (R : VG.Spec.MlDsa.Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = h + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = f + BitVec.ofNat 64 (16 * i)
  rdx : s.gpr .rdx = g + BitVec.ofNat 64 (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : VConsts s
  r2 : s.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V
  x6 : s.xmm .xmm6 = s₀.xmm .xmm6
  frame : Frame [pR h] s₀.mem s.mem
  done : ∀ k < 4 * i, (coeffAt s.mem h k).toNat = (R[k]!).val
  rest : ∀ k < 256, 4 * i ≤ k → coeffAt s.mem h k = coeffAt s₀.mem h k

section
variable {h f g : Addr} {s₀ : State} (hwh : pR h ∈ s₀.wr) (hrf : pR f ∈ s₀.rd ++ s₀.wr)
  (hrg : pR g ∈ s₀.rd ++ s₀.wr) (hdf : (pR h).Disjoint (pR f)) (hdg : (pR h).Disjoint (pR g))
  {F G : VG.Spec.MlDsa.Poly} (hF : ∀ k < 256, (coeffAt s₀.mem f k).toNat = (F[k]!).val)
  (hG : ∀ k < 256, (coeffAt s₀.mem g k).toNat = (G[k]!).val)
  {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
  (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V → WP isa (.block core) s fun s' =>
    s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
  {R : VG.Spec.MlDsa.Poly} {H : Nat → BitVec 32} (hH : ∀ k < 252, coeffAt s₀.mem h k = H k)
  (hlane : ∀ i < 64, ∀ x y z : BitVec 128, (∀ e < 4, (dword x e).toNat = (F[4 * i + e]!).val) →
    (∀ e < 4, (dword y e).toNat = (G[4 * i + e]!).val) → (∀ e < 4, dword z e = H (4 * i + e)) →
    ∀ e < 4, (dword (Fv x y z) e).toNat = (R[4 * i + e]!).val)
include hwh hrf hrg hdf hdg hF hG hcore hH hlane

theorem step {i : Nat} (hi : i < 63) {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.Mul.Inv h f g s₀ R i s) :
    WP isa (.block (mulLoads ++ core ++ mulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.Mul.Inv h f g s₀ R (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have e1 : s.gpr .rdi = coeffAddr h (4 * i) := by rw [hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi = coeffAddr f (4 * i) := by rw [hI.rsi]; congr 2; omega
  have e3 : s.gpr .rdx = coeffAddr g (4 * i) := by rw [hI.rdx]; congr 2; omega
  have rf : InRegions (s.rd ++ s.wr) (coeffAddr f (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains f j0⟩
  have rg : InRegions (s.rd ++ s.wr) (coeffAddr g (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains g j0⟩
  have rh : InRegions (s.rd ++ s.wr) (coeffAddr h (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact f_in (List.mem_append_right _ hwh) j0
  have wh : InRegions s.wr (coeffAddr h (4 * i)) 16 := by rw [hI.wr]; exact f_in hwh j0
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [show mulLoads ++ core ++ mulTail ++ [.alu .sub .rcx (.imm 1)] =
    mulLoads ++ (core ++ (mulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) by simp [List.append_assoc],
    WP.block_append_iff]
  simp only [mulLoads]
  vrund [e1, e2, e3, rf, rg, rh]
  rw [WP.block_append_iff]
  refine WP.mono (hcore _ (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2))
    fun s2 ⟨h3, o2⟩ => ?_
  have c2 := xonly_vconsts o2 (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by decide) (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have r2 : s2.rd = s.rd := o2.rd
  have w2 : s2.wr = s.wr := o2.wr
  have x11 : s2.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V := by rw [o2.xmm _ (by decide)]; simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2
  simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false] at h3
  generalize hV : Fv (s.mem.readW (coeffAddr f (4 * i)) 128) (s.mem.readW (coeffAddr g (4 * i)) 128)
    (s.mem.readW (coeffAddr h (4 * i)) 128) = V at h3
  simp only [mulTail]
  vrund [g2, m2, r2, w2, e1, e2, e3, wh, h3]
  have lx : ∀ e < 4, (dword (s.mem.readW (coeffAddr f (4 * i)) 128) e).toNat = (F[4 * i + e]!).val :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega)]
  have ly : ∀ e < 4, (dword (s.mem.readW (coeffAddr g (4 * i)) 128) e).toNat = (G[4 * i + e]!).val :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega)]
  have lz : ∀ e < 4, dword (s.mem.readW (coeffAddr h (4 * i)) 128) e = H (4 * i + e) :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, hI.rest _ (by omega) (by omega),
      hH _ (by omega)]
  have hl := hlane i (by omega) _ _ _ lx ly lz
  rw [hV] at hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
      RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.xmm_setReg,
      RegUpd.xmm_setFlags, ite_true, ite_false, reduceCtorEq]
  · exact VG.Proof.MlDsa.X86_64.Arith.Mul.ptr16 h i
  · exact VG.Proof.MlDsa.X86_64.Arith.Mul.ptr16 f i
  · exact VG.Proof.MlDsa.X86_64.Arith.Mul.ptr16 g i
  · exact hI.rd
  · exact hI.wr
  · exact c2.q
  · exact c2.qinv
  · exact x11
  · rw [o2.xmm _ (by decide)]; simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.x6
  · exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains h j0)
  · intro k hk
    rw [coeffAt_write128 _ _ j0 _ (by omega)]
    split
    · rw [hl _ (by omega), show 4 * i + (k - 4 * i) = k by omega]
    · exact hI.done k (by omega)
  · intro k hk hk'
    rw [coeffAt_write128 _ _ j0 _ hk, ifn (by omega)]
    exact hI.rest k hk (by omega)

theorem loop_ok (hdi : s₀.gpr .rdi = h) (hsi : s₀.gpr .rsi = f) (hdx : s₀.gpr .rdx = g) (hc : VConsts s₀)
    (h11 : s₀.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V) : WP isa (rcxLoop 63 (mulLoads ++ core ++ mulTail)) s₀ (VG.Proof.MlDsa.X86_64.Arith.Mul.Inv h f g s₀ R 63) :=
  wp_rcxLoop (N := 63) (by decide) (by decide) _ (fun u o _ =>
    ⟨by rw [o.keep.gpr (by decide), hdi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hsi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, add_ofNat_zero], o.keep.2.1, o.keep.2.2,
      ⟨by rw [o.xmm]; exact hc.q, by rw [o.xmm]; exact hc.qinv⟩, by rw [o.xmm]; exact h11, by rw [o.xmm],
      by rw [o.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega), fun k _ _ => by rw [o.mem]⟩)
    fun i hi u hI => VG.Proof.MlDsa.X86_64.Arith.Mul.step hwh hrf hrg hdf hdg hF hG hcore hH hlane hi hI


omit hwh hH in
/-- The last four coefficients, with those of `h` in `xmm6`. -/
theorem last {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.Mul.Inv h f g s₀ R 63 s) (hz : ∀ e < 4, dword (s₀.xmm .xmm6) e = H (252 + e)) :
    WP isa (.block (mulLast core)) s fun s' =>
      (∀ e < 4, (dword (s'.xmm .xmm3) e).toNat = (R[252 + e]!).val) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem := by
  have j0 : 4 * 63 + 4 ≤ 256 := by decide
  have e2 : s.gpr .rsi = coeffAddr f (4 * 63) := hI.rsi
  have e3 : s.gpr .rdx = coeffAddr g (4 * 63) := hI.rdx
  have rf : InRegions (s.rd ++ s.wr) (coeffAddr f (4 * 63)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains f j0⟩
  have rg : InRegions (s.rd ++ s.wr) (coeffAddr g (4 * 63)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains g j0⟩
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [mulLast, WP.block_append_iff]
  vrund [e2, e3, rf, rg, eval_movdqa]
  refine WP.mono (hcore _ (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2))
    fun s2 ⟨h3, o2⟩ => ⟨fun e he => ?_, o2.gpr, o2.mem⟩
  simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false, hI.x6] at h3
  rw [h3]
  refine hlane 63 (by decide) _ _ _ (fun e he => ?_) (fun e he => ?_) hz e he
  · rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega)]
  · rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega)]

end


theorem coeffAt_mxH {m m' : Mem} {p : Addr} (hf : Frame [VG.Proof.MlDsa.X86_64.Arith.mxH p] m m') {k : Nat} (hk : k < 254) :
    coeffAt m' p k = coeffAt m p k :=
  hf.readW (r := ⟨coeffAddr p k, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint p (by omega) (by omega) (by omega)) (by decide)

/-- The whole function, from its precondition, with a `core` whose lanes are
those of `t`. -/
theorem fn_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {hPre : Mem → Addr → Prop} {σ : State} (hp : (VG.Proof.MlDsa.X86_64.Arith.mulK t hPre).pre σ)
    {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = VG.Proof.MlDsa.X86_64.Arith.r2V → WP isa (.block core) s fun s' =>
      s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
    (hlane : ∀ i < 64, ∀ x y z : BitVec 128,
      (∀ e < 4, (dword x e).toNat = ((polyAt σ.mem (σ.gpr .rsi))[4 * i + e]!).val) →
      (∀ e < 4, (dword y e).toNat = ((polyAt σ.mem (σ.gpr .rdx))[4 * i + e]!).val) →
      (∀ e < 4, dword z e = coeffAt σ.mem (σ.gpr .rdi) (4 * i + e)) →
      ∀ e < 4, (dword (Fv x y z) e).toNat = ((t (polyAt σ.mem (σ.gpr .rdi)) (polyAt σ.mem (σ.gpr .rsi))
        (polyAt σ.mem (σ.gpr .rdx)))[4 * i + e]!).val)
    (hk : writesOnly [.rax, .rdi, .rsi, .rdx, .rcx]
      (.seq (.block VG.Impl.MlDsa.X86_64.Arith.mulPro) (.seq (rcxLoop 63 (mulLoads ++ core ++ mulTail)) (.block (mulLast core)))) = true) :
    WP isa (mulFn core) σ fun s' => Keep [.r8, .rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] σ s' ∧
      Frame [pR (σ.gpr .rdi)] σ.mem s'.mem ∧ (VG.Proof.MlDsa.X86_64.Arith.mulK t hPre).post σ s' := by
  obtain ⟨hrd, hwr, hdf, hdg, -, -, -, -, redf, redg⟩ := hp
  generalize eh : σ.gpr .rdi = h at *
  generalize ef : σ.gpr .rsi = f at *
  generalize eg : σ.gpr .rdx = g at *
  let R := t (polyAt σ.mem h) (polyAt σ.mem f) (polyAt σ.mem g)
  have hwh : pR h ∈ σ.wr := by rw [hwr]; exact List.mem_singleton_self _
  have r6 : InRegions (σ.rd ++ σ.wr) (coeffAddr h 252) 16 :=
    ⟨_, List.mem_append_right _ hwh, Offset.contains_base h (by omega) (by omega)⟩
  simp only [mulFn]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r8 = h ∧
      s1.xmm .xmm6 = σ.mem.readW (coeffAddr h 252) 128 ∧ Keep [.r8] σ s1 ∧ s1.mem = σ.mem) (by
    vrund [eh, r6]
    exact ⟨fun r hr => by
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, hr, ite_false], rfl, rfl⟩) fun s1 ⟨h8, h6, k1, m1⟩ => ?_)
  have hw1 : pR h ∈ s1.wr := by rw [k1.2.2]; exact hwh
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.withMxcsrH_ok (r := .r8) ⟨by decide, by decide⟩ [.rax, .rdi, .rsi, .rdx, .rcx]
    ⟨by decide, by decide⟩ h8 hw1 hk (Q := fun (s3 : State) => Keep [.rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] s1 s3 ∧
      s3.gpr .rdi = coeffAddr h 252 ∧ Frame [pR h] σ.mem s3.mem ∧
      (∀ k < 252, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
      ∀ e < 4, (dword (s3.xmm .xmm3) e).toNat = (R[252 + e]!).val)
    fun s2 k2 f2 x2 _ => ?_) fun s4 ⟨s3, ⟨kk, hdi, fr, dn, ln⟩, f4, k4, x4, _⟩ => ?_)
  · have fσ2 : Frame [VG.Proof.MlDsa.X86_64.Arith.mxH h] σ.mem s2.mem := by rw [← m1]; exact f2
    refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx] (WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.mulPro_ok s2)
      fun w ⟨cw, xw, x6, kw, mw⟩ => ?_) (Q := fun (s3 : State) => s3.gpr .rdi = coeffAddr h 252 ∧
        Frame [pR h] σ.mem s3.mem ∧ (∀ k < 252, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
        ∀ e < 4, (dword (s3.xmm .xmm3) e).toNat = (R[252 + e]!).val)) hk)
      fun s3 ⟨q3, kk⟩ => ⟨k2.trans kk, q3⟩
    have gw : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r8 → w.gpr r = σ.gpr r := fun r h1 h2 h3 => by
      rw [kw.gpr (by simpa using h1), k2.gpr (by simp [h1, h2]), k1.gpr (by simpa using h3)]
    have rw' : w.rd = σ.rd ∧ w.wr = σ.wr :=
      ⟨kw.2.1.trans (k2.2.1.trans k1.2.1), kw.2.2.trans (k2.2.2.trans k1.2.2)⟩
    have fσw : Frame [VG.Proof.MlDsa.X86_64.Arith.mxH h] σ.mem w.mem := by rw [mw]; exact fσ2
    have fσw' : Frame [pR h] σ.mem w.mem :=
      Frame.sub fσw fun r hr => ⟨pR h, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.X86_64.Arith.mxH_sub h⟩
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.Mul.loop_ok (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.2]; exact hwh) (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore (fun k hk => VG.Proof.MlDsa.X86_64.Arith.Mul.coeffAt_mxH fσw (by omega)) hlane
      (by rw [gw _ (by decide) (by decide) (by decide), eh]) (by rw [gw _ (by decide) (by decide) (by decide), ef])
      (by rw [gw _ (by decide) (by decide) (by decide), eg]) cw xw) fun s hI => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.Mul.last (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hlane hI (fun e he => by
        rw [x6, x2, h6, dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq])) fun s3 ⟨ln, g3, m3⟩ => ?_
    refine ⟨by rw [g3, hI.rdi], ?_, fun k hk => by rw [m3]; exact hI.done k (by omega), ln⟩
    rw [m3]
    exact Frame.trans fσw' hI.frame
  · have k14 := (k1.trans kk).trans k4
    have hdi4 : s4.gpr .rdi = coeffAddr h 252 := by rw [k4.gpr (by simp), hdi]
    have wh4 : InRegions s4.wr (coeffAddr h 252) 16 := by
      rw [k14.2.2]; exact ⟨_, hwh, Offset.contains_base h (by omega) (by omega)⟩
    vrund [hdi4, wh4]
    have f4' : Frame [pR h] s3.mem s4.mem := Frame.sub f4 fun r hr => ⟨pR h, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.X86_64.Arith.mxH_sub h⟩
    refine ⟨k14.mono (by simp), (fr.trans f4').writeW (List.mem_singleton_self _) _
      (Offset.contains_base h (by omega) (by omega)), ?_⟩
    dsimp only [VG.Proof.MlDsa.X86_64.Arith.mulK]
    rw [eh, ef, eg]
    refine polyIs_of_toNat fun k hk => ?_
    rw [n_eq] at hk
    rw [coeffAt_write128 _ _ (j := 252) (by decide) _ hk]
    split
    · rw [x4]
      have := ln (k - 252) (by omega)
      rwa [show 252 + (k - 252) = k by omega] at this
    · rw [VG.Proof.MlDsa.X86_64.Arith.Mul.coeffAt_mxH f4 (by omega)]
      exact dn k (by omega)

end Mul

/-! ## The functions -/

/-- The contract of `vg_mldsa_multiply_ntt`. -/
abbrev mulK' : Contract isa := VG.Proof.MlDsa.X86_64.Arith.mulK (fun _ f g => Spec.MlDsa.multiplyNTT f g) fun _ _ => True

/-- The contract of `vg_mldsa_multiply_add_ntt`. -/
abbrev mulAddK : Contract isa := VG.Proof.MlDsa.X86_64.Arith.mulK (fun h f g => Spec.MlDsa.add h (Spec.MlDsa.multiplyNTT f g)) Reduced

theorem mul_correct (s : State) (hs : mulK'.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mul s t s' ∧ abiPreserved s s' ∧ mulK'.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := Mul.fn_ok hs (core := mulCore) (Fv := fun x y _ => VG.Proof.MlDsa.X86_64.Arith.mulV x y)
    (fun s hc h11 => VG.Proof.MlDsa.X86_64.Arith.mulCore_ok hc h11)
    (fun i hi x y z hx hy _ e he => by
      rw [mul_get _ _ (by rw [n_eq]; omega)]
      exact VG.Proof.MlDsa.X86_64.Arith.mul_lane hx hy he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem mulAdd_correct (s : State) (hs : mulAddK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mulAdd s t s' ∧ abiPreserved s s' ∧ mulAddK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := Mul.fn_ok hs (core := mulAddCore) (Fv := VG.Proof.MlDsa.X86_64.Arith.mulAddV)
    (fun s hc h11 => VG.Proof.MlDsa.X86_64.Arith.mulAddCore_ok hc h11)
    (fun i hi x y z hx hy hz e he => by
      rw [add_get _ _ (by rw [n_eq]; omega), mul_get _ _ (by rw [n_eq]; omega)]
      exact VG.Proof.MlDsa.X86_64.Arith.mulAdd_lane hx hy (c := fun e => (polyAt s.mem (s.gpr .rdi))[4 * i + e]!)
        (fun e he => by rw [hz e he, polyAt_val hs.2.2.2.2.2.2.2.1 (by rw [n_eq]; omega)]) he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

/-- The pointers and `rsp` are public. -/
def mulτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]

theorem mul_agree {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {r : Mem → Addr → Prop} (s₁ s₂ : State) (_ : (VG.Proof.MlDsa.X86_64.Arith.mulK t r).pre s₁)
    (_ : (VG.Proof.MlDsa.X86_64.Arith.mulK t r).pre s₂) (hp : (VG.Proof.MlDsa.X86_64.Arith.mulK t r).pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.MlDsa.X86_64.Arith.mulτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

theorem mul_ct : ConstantTime isa mulK'.pre mulK'.pub Impl.MlDsa.X86_64.Arith.mul :=
  VG.Taint.constantTime (A := VG.X86_64.taint) VG.Proof.MlDsa.X86_64.Arith.mulτ VG.Proof.MlDsa.X86_64.Arith.mul_agree (by taint_decide)

theorem mulAdd_ct : ConstantTime isa mulAddK.pre mulAddK.pub Impl.MlDsa.X86_64.Arith.mulAdd :=
  VG.Taint.constantTime (A := VG.X86_64.taint) VG.Proof.MlDsa.X86_64.Arith.mulτ VG.Proof.MlDsa.X86_64.Arith.mul_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mul (Spec.MlDsa.mulContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.mul_correct VG.Proof.MlDsa.X86_64.Arith.mul_ct (by
    mldsa_implies [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, VG.Proof.MlDsa.X86_64.Arith.mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using VG.Proof.MlDsa.X86_64.Arith.mulSat)

theorem mulAdd_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mulAdd (Spec.MlDsa.mulAddContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.mulAdd_correct VG.Proof.MlDsa.X86_64.Arith.mulAdd_ct (by
    mldsa_implies [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, VG.Proof.MlDsa.X86_64.Arith.mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using VG.Proof.MlDsa.X86_64.Arith.mulSat)

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay`. -/
section

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len ≥ 4` on AVX2 registers

For any butterfly code `bf` that does what `op` does to the doublewords of two
SSE registers (`VBflyOk`) and whose AVX2 form does it in each lane
(`laneSseBlock (toY bf) = some bf`), and any block of the specification whose
butterflies do `op` (`BlkOk`): eight butterflies of a block (`ystep`), the
`len / 8` of them of a block (`yblock_ok`), and the `128 / len` blocks of a
layer with `len ≥ 8` (`ylay_ok`); and the layer with `len = 4`, two blocks at
a time, the lower halves of their coefficients gathered into `ymm0` and the
upper ones into `ymm1` by `vperm2i128` (`ylay4_ok`). The zetas: `yzeta1_ok`
and `yzetaS_ok`, and the layers' result coefficient by coefficient
(`layF_get`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt sel_zero sel_55
  add_ofNat_zero GOnly addR_ok wp_rcxLoopY wp_countdown ybcast_ok yblend_ok yperm_ok perm20 perm31
  wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas)

/-! ## A layer, coefficient by coefficient -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : VG.Spec.MlDsa.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlDsa.Poly} (hblk : BlkOk blk op)
include hblk

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem layF_get (F : VG.Spec.MlDsa.Poly) {len : Nat} (hl : 0 < len) (zi : Nat → Nat) {b : Nat} (hb : 2 * len * b ≤ 256)
    {j : Nat} (hj : j < 256) :
    (layF blk F len zi b)[j]! = if j < 2 * len * b then
      (if j % (2 * len) < len then (op F[j]! F[j + len]! (zetas (zi (j / (2 * len))))).1
        else (op F[j - len]! F[j]! (zetas (zi (j / (2 * len))))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    have hb' : 2 * len * b + 2 * len ≤ 256 := by rw [Nat.mul_succ] at hb; exact hb
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ len _ _ len hl (Nat.le_refl _) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    have hd : ∀ i, 2 * len * b ≤ i → i < 2 * len * b + 2 * len → i / (2 * len) = b ∧
        i % (2 * len) = i - 2 * len * b := fun i h1 h2 => by
      have e1 : i / (2 * len) = b := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact h1
        · rw [Nat.succ_mul, Nat.mul_comm b]; exact h2
      refine ⟨e1, ?_⟩
      have := Nat.div_add_mod i (2 * len)
      rw [e1] at this; omega
    by_cases h1 : 2 * len * b ≤ j ∧ j < 2 * len * b + len
    · obtain ⟨d1, d2⟩ := hd j h1.1 (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ih (by omega) hj, ih (by omega) (by omega), d1,
        ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show j % (2 * len) < len by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + len < 2 * len * b by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : 2 * len * b + len ≤ j ∧ j < 2 * len * b + len + len
      · obtain ⟨d1, d2⟩ := hd j (by omega) (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ih (by omega) (by omega), ih (by omega) hj, d1,
          ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j % (2 * len) < len by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - len < 2 * len * b by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ih (by omega) hj]
        by_cases h3 : j < 2 * len * b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]

end

/-! ## Coefficients in both lanes -/

/-- The facts a piece of a layer keeps. -/
structure BInvY (fP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem
  consts : YConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInvY.trans {fP : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.X86_64.Arith.BInvY fP s₁ s₂) (h₂ : VG.Proof.MlDsa.X86_64.Arith.BInvY fP s₂ s₃) :
    VG.Proof.MlDsa.X86_64.Arith.BInvY fP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-- `YConsts` after code that changed the vector registers `rs` only, then
nothing in them. -/
theorem ylanes_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) (hc : YConsts s₀) (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' :=
  fun l hl => ⟨by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).q,
    by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).qinv⟩

/-- Two registers stored into a polynomial at coefficients `j` and `j'`,
lane `l` of each holding the four coefficients of `R` from `j + 4l` and
`j' + 4l`. -/
theorem polyIs_write2L {m : Mem} {p : Addr} {P R : VG.Spec.MlDsa.Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {s : State} {x y : XReg}
    (hx : ∀ l < 2, DLanes (s.lane x l) (fun e => R[j + 4 * l + e]!))
    (hy : ∀ l < 2, DLanes (s.lane y l) (fun e => R[j' + 4 * l + e]!))
    (hR : ∀ i < 256, (i < j ∨ j + 8 ≤ i) → (i < j' ∨ j' + 8 ≤ i) → R[i]! = P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) (s.ymm x)).writeW (coeffAddr p j') (s.ymm y)) p R :=
  polyIs_write2Y hP hj hj' hsep (a := fun e => R[j + e]!) (b := fun e => R[j' + e]!)
    (ylanes_ymm (fun e he => (hx 0 (by decide) e he).trans (by simp only [Nat.mul_zero, Nat.add_zero]))
      (fun e he => (hx 1 (by decide) e he).trans (by dsimp only; rw [show j + 4 * 1 + e = j + (e + 4) by omega])))
    (ylanes_ymm (fun e he => (hy 0 (by decide) e he).trans (by simp only [Nat.mul_zero, Nat.add_zero]))
      (fun e he => (hy 1 (by decide) e he).trans (by dsimp only; rw [show j' + 4 * 1 + e = j' + (e + 4) by omega])))
    fun i hi => by
      by_cases h1 : j ≤ i ∧ i < j + 8
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), show j + (i - j) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : j' ≤ i ∧ i < j' + 8
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), show j' + (i - j') = i by omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; exact hR i hi (by omega) (by omega)

theorem DLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : DLanes x f) (e : ∀ i < 4, f i = g i) : DLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem ZLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : ZLanes x f) (e : ∀ i < 4, f i = g i) : ZLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem getP_congr (P : VG.Spec.MlDsa.Poly) {a b : Nat} (h : a = b) : P[a]! = P[b]! := h ▸ rfl

/-- A butterfly of the coefficients at `a` and `b` of `P` with the zeta of
index `zi c`, at other indices that are the same. -/
theorem op_idx (op : Zq → Zq → Zq → Zq × Zq) (P : VG.Spec.MlDsa.Poly) (zi : Nat → Nat) {a b c a' b' c' : Nat} (ha : a = a')
    (hb : b = b') (hc : c = c') : op P[a]! P[b]! (zetas (zi c)) = op P[a']! P[b']! (zetas (zi c')) := by
  subst ha hb hc; rfl

/-- The prologue of the layers with `len` = 4, 2 and 1. -/
theorem ypre21 {fP sP : Addr} (k : Nat) (hk : k + 4 ≤ 256) {s : State} (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ leaR .r8 .rsi (4 * k))) s fun w =>
      w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧ GOnly [.rdx, .r8] s w ∧ w.ymmHi = s.ymmHi := by
  simp only [leaR]
  vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
  exact ⟨by gonlyd, rfl⟩

/-! ## The zetas -/

theorem zodd_F5 (x : BitVec 128) : ZOdd x (shufDwords x 0xF5) := fun j hj => by
  rw [dword_shufDwords _ _ (by omega)]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

/-- The zetas `pshufd` with `o` leaves of the four at index `k` of the table. -/
theorem zlanes_tab (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 256) {m : Mem}
    (ht : Tab zmTab m zP 256) :
    ZLanes (shufDwords (m.readW (coeffAddr zP k) 128) o) (fun i => zetas (k + sel o i)) := fun i hi => by
  have hs := sel_lt o i
  rw [dword_shufDwords_sel _ _ hi, dword_readW _ _ hs, coeffAddr_add]
  exact tab_zeta ht (hk i hi)

theorem zsse1_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzeta1_ok {zP : Addr} {k : Nat} (hk : k + 4 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta1) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun _ => zetas k) ∧
      ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta1, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) 0 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s1.lane .xmm13 l) 0) 0xF5)
    fun l _ => VG.Proof.MlDsa.X86_64.Arith.zsse1_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have e13 : s2.lane .xmm13 l = _ := (l2 l hl).1
  have e12 : s2.lane .xmm12 l = _ := (l2 l hl).2
  rw [e12, e13, b1 l hl, h8, add_ofNat_zero]
  refine ⟨fun i hi => ?_, VG.Proof.MlDsa.X86_64.Arith.zodd_F5 _⟩
  rw [VG.Proof.MlDsa.X86_64.Arith.zlanes_tab 0 (fun j _ => by rw [sel_zero]; omega) ht i hi]
  dsimp only; rw [sel_zero, Nat.add_zero]

theorem zsseS_ok (o₀ o₁ : BitVec 8) (t : State) :
    WP isa (.block [.xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) o₀ ∧ t'.xmm .xmm2 = shufDwords (t.xmm .xmm13) o₁) ∧
        XOnly [.xmm2, .xmm13] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem zsseF5_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      t'.xmm .xmm12 = shufDwords (t.xmm .xmm13) 0xF5 ∧ XOnly [.xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The odd zetas of each lane of `ymm13` in the even doublewords of `ymm12`. -/
theorem yF5_ok (s : State) :
    WP isa (.block (toY [.xop (.pshufd .xmm12 .xmm13 0xF5)])) s fun s' =>
      (∀ l < 2, s'.lane .xmm12 l = shufDwords (s.lane .xmm13 l) 0xF5) ∧ YOnly [.xmm12] s s' :=
  ylanes (by decide) (P := fun l t => t.xmm .xmm12 = shufDwords (s.lane .xmm13 l) 0xF5)
    fun l _ => VG.Proof.MlDsa.X86_64.Arith.zsseF5_ok (s.proj l)

theorem yzetaS_ok (o₀ o₁ : BitVec 8) {zP : Addr} {k : Nat} (hk0 : ∀ j < 4, k + sel o₀ j < 256)
    (hk1 : ∀ j < 4, k + sel o₁ j < 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (yzetaS o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => zetas (k + sel o₀ i)) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => zetas (k + sel o₁ i)) ∧
      (∀ l < 2, ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm2, .xmm12] s s' := by
  rw [yzetaS, WP.block_append_iff, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) o₀ ∧ t.xmm .xmm2 = shufDwords (s1.lane .xmm13 l) o₁)
    fun l _ => VG.Proof.MlDsa.X86_64.Arith.zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yF5_ok s3) fun s4 ⟨f4, o4⟩ => ?_
  have x0 : s4.lane .xmm13 0 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₀ := by
    have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [o4.lane _ (by decide) 0 (by decide), e0, e, b1 0 (by decide), h8, add_ofNat_zero]
  have x1 : s4.lane .xmm13 1 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₁ := by
    have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [o4.lane _ (by decide) 1 (by decide), e1, e, b1 1 (by decide), h8, add_ofNat_zero]
  refine ⟨by rw [x0]; exact VG.Proof.MlDsa.X86_64.Arith.zlanes_tab o₀ hk0 ht, by rw [x1]; exact VG.Proof.MlDsa.X86_64.Arith.zlanes_tab o₁ hk1 ht,
    fun l hl => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
  rw [f4 l hl, o4.lane _ (by decide) l hl]
  exact VG.Proof.MlDsa.X86_64.Arith.zodd_F5 _

/-! ## A layer with `len ≥ 8` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  (hY : laneSseBlock (toY bf) = some bf)
  {blk : VG.Spec.MlDsa.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlDsa.Poly} (hblk : BlkOk blk op)
include hbf hY

/-- The butterflies of `bf` in each lane, from the coefficients `x` and `y`
of the lanes of `ymm0` and `ymm1` and the zetas `ζ` of those of `ymm13`. -/
theorem ybf_ok {s : State} (hc : YConsts s) {x y ζ : Nat → Nat → Zq}
    (hx : ∀ l < 2, DLanes (s.lane .xmm0 l) (x l)) (hy : ∀ l < 2, DLanes (s.lane .xmm1 l) (y l))
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (ζ l)) (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l)) :
    WP isa (.block (toY bf)) s fun s' =>
      (∀ l < 2, DLanes (s'.lane .xmm0 l) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
        DLanes (s'.lane .xmm3 l) (fun i => (op (x l i) (y l i) (ζ l i)).2)) ∧
      YOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' :=
  ylanes hY (P := fun l t => DLanes (t.xmm .xmm0) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
      DLanes (t.xmm .xmm3) (fun i => (op (x l i) (y l i) (ζ l i)).2))
    fun l hl => WP.mono (hbf _ (hc l hl) _ _ _ (hx l hl) (hy l hl) (hz l hl) (ho l hl))
      fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩

include hblk

/-- The body of the loop over the vectors of a block. -/
abbrev ybody (bf : List Instr) (len : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx (4 * len))] ++ toY bf ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (4 * len)) .xmm3,
      .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem ystep {fP : Addr} {len st u k : Nat} (hl : 8 ≤ len) (hs : st + 2 * len ≤ 256) (hu : 8 * u + 8 ≤ len)
    {G : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => zetas k))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l))
    (hdx : s.gpr .rdx = coeffAddr fP (st + 8 * u)) (hS : PolyIs s.mem fP (blk G len k st (8 * u)))
    (hw : pR fP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.ybody bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (8 * (u + 1))) ∧ s'.gpr .rdx = coeffAddr fP (st + 8 * (u + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        (∀ l < 2, s'.lane .xmm12 l = s.lane .xmm12 l) ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 8 * u + 8 ≤ 256 := by omega
  have j1 : st + 8 * u + len + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 (4 * len) = coeffAddr fP (st + 8 * u + len) :=
    coeffAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 0) 32 := by
    rw [add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 (4 * len)) 32 := by
    rw [a1]; exact f_in32 (List.mem_append_right _ hw) j1
  rw [VG.Proof.MlDsa.X86_64.Arith.ybody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [hdx]; exact r0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, hdx]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  generalize hP : blk G len k st (8 * u) = P at hS
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.ybf_ok hbf hY (yonly_yconsts o12 hc (by decide) (by decide))
    (x := fun l e => P[st + 8 * u + 4 * l + e]!) (y := fun l e => P[st + 8 * u + len + 4 * l + e]!)
    (ζ := fun _ _ => zetas k)
    (fun l hl => by
      rw [o2.lane _ (by decide) l hl, L1 l hl, hdx, add_ofNat_zero]; exact dlanes_loadY hS j0 hl)
    (fun l hl => by
      rw [L2 l hl, o1.gpr, o1.mem, hdx, a1]; exact dlanes_loadY hS j1 hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hz l hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact ho l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have w0 : InRegions s3.wr (s3.gpr .rdx) 32 := by
    rw [o13.wr, o13.gpr, hdx]; exact f_in32 hw j0
  have w1 : InRegions s3.wr (s3.gpr .rdx + BitVec.ofNat 64 (4 * len)) 32 := by
    rw [o13.wr, o13.gpr, hdx, a1]; exact f_in32 hw j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx32]
  have g3 : s3.gpr .rdx = coeffAddr fP (st + 8 * u) := by rw [o13.gpr, hdx]
  rw [g3, a1, o13.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have hR : ∀ i < 256, (blk G len k st (8 * (u + 1)))[i]! = if st + 8 * u ≤ i ∧ i < st + 8 * u + 8 then
        (op P[i]! P[i + len]! (zetas k)).1 else if st + 8 * u + len ≤ i ∧ i < st + 8 * u + len + 8 then
        (op P[i - len]! P[i]! (zetas k)).2 else P[i]! := fun i hi => by
      rw [← hP, show 8 * (u + 1) = 8 * u + 8 by omega, hblk.add, hblk.get _ _ _ _ _ (by omega) (by omega)
        (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    refine VG.Proof.MlDsa.X86_64.Arith.polyIs_write2L (s := s3) hS j0 j1 (by omega) (fun l hl e he => ?_) (fun l hl e he => ?_)
      (fun i hi h1 h2 => by rw [hR i hi, ite_eq_right (by omega), ite_eq_right (by omega)])
    · rw [(B3 l hl).1 e he]; dsimp only; rw [hR _ (by omega), ite_eq_left (by omega),
        show st + 8 * u + len + 4 * l + e = st + 8 * u + 4 * l + e + len by omega]
    · rw [(B3 l hl).2 e he]; dsimp only; rw [hR _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show st + 8 * u + len + 4 * l + e - len = st + 8 * u + 4 * l + e by omega]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show st + 8 * u + 8 = st + 8 * (u + 1) by omega]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o13.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]
  · rw [o13.gpr]
  · rw [o13.gpr]
  · exact o13.mxcsr

/-- The code of a block of a layer with `len ≥ 8`. -/
abbrev yblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (yzeta1 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (rcxLoop (len / 8) ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (at_ .rdx (4 * len))] ++ toY bf ++
        [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 32)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))

theorem yblock_ok {fP sP : Addr} {len st kz : Nat} (h8 : 8 ≤ len) (hl8 : len % 8 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz + 4 ≤ 256) (dz : BitVec 32) {G : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = coeffAddr fP st) (h8r : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP G)
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (VG.Proof.MlDsa.X86_64.Arith.yblk bf len dz) s fun s' => PolyIs s'.mem fP (blk G len kz st len) ∧
      s'.gpr .rdx = coeffAddr fP (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yzeta1_ok hkz h8r (tab_in (List.mem_append_right _ hw) hkz) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (addR_ok .r8 dz s1) fun s2 ⟨h82, o2, y2⟩ => ?_
  have l2 := o2.lane y2
  have c2 : YConsts s2 := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s1) l2 o1 hc (by decide) (by decide)
  have dx2 : s2.gpr .rdx = coeffAddr fP st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR fP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hwf
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoopY (N := len / 8) (by omega) (by omega)
    (fun u w => PolyIs w.mem fP (blk G len kz st (8 * u)) ∧ w.gpr .rdx = coeffAddr fP (st + 8 * u) ∧
      YConsts w ∧ (∀ l < 2, w.lane .xmm13 l = s2.lane .xmm13 l) ∧ (∀ l < 2, w.lane .xmm12 l = s2.lane .xmm12 l) ∧
      Keep [.rcx, .rdx] s2 w ∧ Frame [pR fP] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hy _ => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s2) (o.lane hy) (YOnly.refl [] s2) c2 (by decide) (by decide),
      fun l _ => o.lane hy _ l, fun l _ => o.lane hy _ l, o.keep.mono (by simp),
      by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Arith.ystep hbf hY hblk h8 hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl8); omega) hc'
        (fun l hl => by rw [hz' l hl, l2]; exact (z1 l hl).1)
        (fun l hl => by rw [hz' l hl, hzo' l hl, l2, l2]; exact (z1 l hl).2) hdx' hS'
        (by rw [hk'.2.2]; exact hw2))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], fun l hl => by rw [hzo'' l hl, hzo' l hl],
          (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩))
    fun w ⟨hS3, hdx3, hc3, _, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 8 * (len / 8) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl8)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82, g1]
  vrund [hdx3, sx_ofNat (show 4 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [coeffAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := w) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] w) hc3
      (by decide) (by decide),
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

theorem ylay_ok {fP sP : Addr} {len k : Nat} (hlen : len ∈ [8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c + 4 ≤ 256)
    (hstep : ∀ c < 128 / len, coeffAddr sP (zi c) + BitVec.signExtend 64 dz = coeffAddr sP (zi (c + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay bf len k dz) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128 / len)) ∧
      VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have hl : 8 ≤ len ∧ len % 8 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h8, hl8, hl128, hcov, hpos, h16⟩ := hl
  have hk : k + 4 ≤ 256 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR]
      vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi, RegUpd.ymmHi_setReg]
      refine ⟨?_, by gonlyd, rfl⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o, hy⟩ => ?_)
  have hwf' : pR fP ∈ w.wr := by rw [o.keep.2.2]; exact hwf
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  have cw : YConsts w := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s) (o.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => PolyIs u.mem fP (layF blk F len zi c) ∧ u.gpr .rdx = coeffAddr fP (2 * len * c) ∧
      u.gpr .r8 = coeffAddr sP (zi c) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP w u ∧ Tab zmTab u.mem sP 256)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, cw, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yblock_ok hbf hY hblk h8 hl8 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hwf') (by rw [hb'.keep.2.2]; exact hw'))
    fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'',
        hT'.frame hb''.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)⟩, hax'', hzf''⟩

/-! ## The layer with `len = 4` -/

/-- The body of the layer with `len = 4`. -/
abbrev ybody4 (bf : List Instr) (o₀ o₁ : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm4 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ (yzetaS o₀ o₁ ++
    ([.alu .add .r8 (.imm dz)] ++ ([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20)] ++
    ([.vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ (toY bf ++ ([.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20)] ++
    ([.vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31)] ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))))))

theorem ystep4 {fP sP : Addr} {m kb : Nat} (hm : m < 16) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kb + 4 ≤ 256) (hsel : ∀ e < 4, kb + sel o₀ e = zi (2 * m) ∧ kb + sel o₁ e = zi (2 * m + 1))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hdx : s.gpr .rdx = coeffAddr fP (16 * m))
    (h8 : s.gpr .r8 = coeffAddr sP kb) (hS : PolyIs s.mem fP (layF blk F 4 zi (2 * m)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.ybody4 bf o₀ o₁ dz)) s fun s' =>
      PolyIs s'.mem fP (layF blk F 4 zi (2 * (m + 1))) ∧ s'.gpr .rdx = coeffAddr fP (16 * (m + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have j0 : 16 * m + 8 ≤ 256 := by omega
  have j1 : 16 * m + 8 + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP (16 * m) + BitVec.ofNat 64 32 = coeffAddr fP (16 * m + 8) := coeffAddr_add _ _ 8
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right s.rd hwf) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact f_in32 (List.mem_append_right s.rd hwf) j1
  generalize hP : layF blk F 4 zi (2 * m) = P at hS
  -- the loads
  rw [VG.Proof.MlDsa.X86_64.Arith.ybody4, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L5, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the zetas
  rw [WP.block_append_iff]
  have hk0 : ∀ j < 4, kb + sel o₀ j < 256 := fun j _ => by have := sel_lt o₀ j; omega
  have hk1 : ∀ j < 4, kb + sel o₁ j < 256 := fun j _ => by have := sel_lt o₁ j; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yzetaS_ok o₀ o₁ (zP := sP) (k := kb) hk0 hk1 (by rw [o12.gpr, h8])
    (by rw [o12.rd, o12.wr]; exact tab_in (List.mem_append_right _ hw) hk) (by rw [o12.mem]; exact hT))
    fun s3 ⟨Z0, Z1, ZO, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := g4.lane y4
  -- the lower and upper halves
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s4) fun s5 ⟨P5, o5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s5) fun s6 ⟨P6, o6⟩ => ?_
  have c6 : YConsts s6 := yonly_yconsts (o5.trans o6)
    (VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  have m3 : s3.mem = s.mem := (o12.trans o3).mem
  have q4 : ∀ l < 2, s4.lane .xmm4 l = s.mem.readW (coeffAddr fP (16 * m) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L4 l hl, hdx, add_ofNat_zero]
  have q5 : ∀ l < 2, s4.lane .xmm5 l =
      s.mem.readW (coeffAddr fP (16 * m + 8) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, L5 l hl, o1.gpr, o1.mem, hdx, a1]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.ybf_ok hbf hY c6 (x := fun l e => P[16 * m + 8 * l + e]!)
    (y := fun l e => P[16 * m + 8 * l + 4 + e]!) (ζ := fun l _ => zetas (zi (2 * m + l)))
    (fun l hl => by
      rw [o6.lane _ (by decide) l hl, P5 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 0 (by decide)]
        exact (dlanes_loadY hS j0 (by decide)).congr fun e _ => VG.Proof.MlDsa.X86_64.Arith.getP_congr P (by omega)
      · rw [ifn (by decide), q5 0 (by decide)]
        exact (dlanes_loadY hS j1 (by decide)).congr fun e _ => VG.Proof.MlDsa.X86_64.Arith.getP_congr P (by omega))
    (fun l hl => by
      rw [P6 l hl, perm31 _ _ hl, o5.lane .xmm4 (by decide) 1 (by decide), o5.lane .xmm5 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 1 (by decide)]
        exact (dlanes_loadY hS j0 (by decide)).congr fun e _ => VG.Proof.MlDsa.X86_64.Arith.getP_congr P (by omega)
      · rw [ifn (by decide), q5 1 (by decide)]
        exact (dlanes_loadY hS j1 (by decide)).congr fun e _ => VG.Proof.MlDsa.X86_64.Arith.getP_congr P (by omega))
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, l4]
      rcases lane01 hl with rfl | rfl
      · exact Z0.congr fun i hi => congrArg zetas (hsel i hi).1
      · exact Z1.congr fun i hi => congrArg zetas (hsel i hi).2)
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, (o5.trans o6).lane _ (by decide) l hl, l4, l4]
      exact ZO l hl))
    fun s7 ⟨B7, o7⟩ => ?_
  -- the blocks back
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s7) fun s8 ⟨P8, o8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s8) fun s9 ⟨P9, o9⟩ => ?_
  have o59 := (o5.trans o6).trans (o7.trans (o8.trans o9))
  have w0 : InRegions s9.wr (s9.gpr .rdx) 32 := by
    rw [o59.wr, o59.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx]
    exact f_in32 hwf j0
  have w1 : InRegions s9.wr (s9.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [o59.wr, o59.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx, a1]
    exact f_in32 hwf j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have g9 : s9.gpr = s4.gpr := o59.gpr
  have m9 : s9.mem = s.mem := by rw [o59.mem, g4.mem, m3]
  have dx9 : s9.gpr .rdx = coeffAddr fP (16 * m) := by
    rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  rw [dx9, a1, m9]
  have hR : ∀ i < 256, (layF blk F 4 zi (2 * (m + 1)))[i]! = if 16 * m ≤ i ∧ i < 16 * m + 16 then
      (if i % (2 * 4) < 4 then (op P[i]! P[i + 4]! (zetas (zi (i / (2 * 4))))).1
        else (op P[i - 4]! P[i]! (zetas (zi (i / (2 * 4))))).2) else P[i]! := fun i hi => by
    have hF : ∀ j, 16 * m ≤ j → j < 256 → P[j]! = F[j]! := fun j h1 h2 => by
      rw [← hP, VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
    rw [VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hi]
    by_cases h1 : 16 * m ≤ i ∧ i < 16 * m + 16
    · rw [ite_eq_left (by omega), ite_eq_left h1]
      by_cases h2 : i % (2 * 4) < 4
      · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hi, hF _ (by omega) (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hi]
    · rw [ite_eq_right h1, ← hP, VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hi]
      by_cases h3 : i < 16 * m
      · rw [ite_eq_left (show i < 2 * 4 * (2 * (m + 1)) by omega),
          ite_eq_left (show i < 2 * 4 * (2 * m) by omega)]
      · rw [ite_eq_right (show ¬ i < 2 * 4 * (2 * (m + 1)) by omega),
          ite_eq_right (show ¬ i < 2 * 4 * (2 * m) by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · refine VG.Proof.MlDsa.X86_64.Arith.polyIs_write2L (s := s9) hS j0 j1 (by omega) (fun l hl => ?_) (fun l hl => ?_)
      (fun i hi h1 h2 => by rw [hR i hi, ite_eq_right (by omega)])
    · rw [o9.lane .xmm4 (by decide) l hl, P8 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]
        exact (B7 0 (by decide)).1.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
          exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op P zi (by omega) (by omega) (by omega))
      · rw [ifn (by decide)]
        exact (B7 0 (by decide)).2.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
          exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op P zi (by omega) (by omega) (by omega))
    · rw [P9 l hl, perm31 _ _ hl, o8.lane .xmm0 (by decide) 1 (by decide),
        o8.lane .xmm3 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]
        exact (B7 1 (by decide)).1.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
          exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op P zi (by omega) (by omega) (by omega))
      · rw [ifn (by decide)]
        exact (B7 1 (by decide)).2.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
          exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op P zi (by omega) (by omega) (by omega))
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide, coeffAddr_add,
      Nat.mul_succ]
  · rw [g9, h84, o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g9, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]
    rw [o59.rd, g4.keep.2.1, o3.rd, o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]
    rw [o59.wr, g4.keep.2.2, o3.wr, o12.wr]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s9) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane])
      o59 (VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  · exact o59.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

theorem ylay4_ok {fP sP : Addr} (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi kb : Nat → Nat)
    (hkb0 : kb 0 = k) (hk : ∀ m < 16, kb m + 4 ≤ 256)
    (hsel : ∀ m < 16, ∀ e < 4, kb m + sel o₀ e = zi (2 * m) ∧ kb m + sel o₁ e = zi (2 * m + 1))
    (hstep : ∀ m < 16, coeffAddr sP (kb m) + BitVec.signExtend 64 dz = coeffAddr sP (kb (m + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay4 bf k o₀ o₁ dz) s fun s' => PolyIs s'.mem fP (layF blk F 4 zi 32) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 4 zi (2 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.vmovdquLoad .l256 .xmm4 (at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ yzetaS o₀ o₁ ++
      [.alu .add .r8 (.imm dz), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20),
        .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ toY bf ++
      [.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
        .vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] = VG.Proof.MlDsa.X86_64.Arith.ybody4 bf o₀ o₁ dz by
    simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlDsa.X86_64.Arith.ystep4 hbf hY hblk hi o₀ o₁ dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21`. -/
section

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len` = 2 and 1 on AVX2 registers

Each iteration of these layers loads sixteen coefficients, from `j`, into
`ymm0` and `ymm1` (or `ymm2`), and in each lane `l` runs `vlay2`'s or
`vlay1`'s gathering, butterflies and interleaving back (`Ntt.lean`) on the
four coefficients from `j + 4l` and the four from `j + 8 + 4l` (`core2_ok`,
`core1_ok`), with the zetas of their blocks in lane `l` of `ymm13`
(`yzetaS_ok`, `yzeta8_ok`, `yzeta8R_ok`); `ystep21` is an iteration for any
such code, and `ylay2_ok` and `ylay1_ok` the layers.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt add_ofNat_zero GOnly
  addR_ok wp_rcxLoopY wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem q256lo q256hi
  lo4 hi4)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas)

/-! ## An iteration -/

/-- The body of the loop of the layers with `len` = 2 and 1. -/
abbrev ybody21 (r2 : XReg) (zl core : List Instr) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 r2 (at_ .rdx 32)] ++ (zl ++
    ([.alu .add .r8 (.imm dz)] ++ (toY core ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))

/-- An iteration of a layer with `len` = 2 or 1: the sixteen coefficients of
`G` from `j`, in lane `l` the four from `j + 4l` and the four from
`j + 8 + 4l`, become those of `R`, with the zetas `ζ l` that `zl` leaves in
the lanes of `ymm13`. -/
theorem ystep21 {core zl : List Instr} {r2 : XReg} {zs : List XReg} {dz : BitVec 32}
    (hY : laneSseBlock (toY core) = some core) (h0 : XReg.xmm0 ∉ zs) (h2 : r2 ∉ zs)
    (h14 : XReg.xmm14 ∉ [XReg.xmm0] ++ [r2] ++ zs) (h15 : XReg.xmm15 ∉ [XReg.xmm0] ++ [r2] ++ zs)
    (h20 : XReg.xmm0 ∉ [r2]) {fP : Addr} {j : Nat} (hj : j + 16 ≤ 256) {G R : VG.Spec.MlDsa.Poly}
    {ζ : Nat → Nat → Zq} {s : State} (hc : YConsts s) (hdx : s.gpr .rdx = coeffAddr fP j)
    (hS : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : ∀ s', XKeep s s' →
      WP isa (.block zl) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ l) ∧
        ZOdd (s''.lane .xmm13 l) (s''.lane .xmm12 l)) ∧ YOnly zs s' s'')
    (hcore : ∀ l < 2, ∀ t : State, VConsts t → DLanes (t.xmm .xmm0) (fun e => G[j + 4 * l + e]!) →
      DLanes (t.xmm r2) (fun e => G[j + 8 + 4 * l + e]!) → ZLanes (t.xmm .xmm13) (ζ l) →
      ZOdd (t.xmm .xmm13) (t.xmm .xmm12) →
      WP isa (.block core) t fun t' => (DLanes (t'.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
        DLanes (t'.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t')
    (hR : ∀ i < 256, i < j ∨ j + 16 ≤ i → R[i]! = G[i]!) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.ybody21 r2 zl core dz)) s fun s' =>
      PolyIs s'.mem fP R ∧ s'.gpr .rdx = coeffAddr fP (j + 16) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have j0 : j + 8 ≤ 256 := by omega
  have j1 : j + 8 + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP j + BitVec.ofNat 64 32 = coeffAddr fP (j + 8) := coeffAddr_add _ _ 8
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact f_in32 (List.mem_append_right s.rd hw) j1
  rw [VG.Proof.MlDsa.X86_64.Arith.ybody21, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (d := r2) (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (hz s2 o12.toXKeep) fun s3 ⟨Z3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := g4.lane y4
  have c4 : YConsts s4 := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s3) l4 (o12.trans o3) hc h14 h15
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => DLanes (t.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
      DLanes (t.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!))
    fun l hl => hcore l hl _ (c4 l hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h0 l hl, o2.lane _ h20 l hl, L0 l hl, hdx, add_ofNat_zero]
          exact dlanes_loadY hS j0 hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h2 l hl, L2 l hl, o1.gpr, o1.mem, hdx, a1]
          exact dlanes_loadY hS j1 hl)
      (by rw [State.proj_xmm, l4]; exact (Z3 l hl).1)
      (by rw [State.proj_xmm, State.proj_xmm, l4, l4]; exact (Z3 l hl).2)) fun s5 ⟨C5, o5⟩ => ?_
  have m5 : s5.mem = s.mem := by rw [o5.mem, g4.mem, o3.mem, o12.mem]
  have g5 : s5.gpr = s4.gpr := o5.gpr
  have dx5 : s5.gpr .rdx = coeffAddr fP j := by rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  have k5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [o5.rd, g4.keep.2.1, o3.rd, o12.rd],
    by rw [o5.wr, g4.keep.2.2, o3.wr, o12.wr]⟩
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [k5.2, dx5]; exact f_in32 hw j0
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 32) 32 := by rw [k5.2, dx5, a1]; exact f_in32 hw j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  rw [dx5, a1, m5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · exact VG.Proof.MlDsa.X86_64.Arith.polyIs_write2L (s := s5) hS j0 j1 (by omega) (fun l hl => (C5 l hl).1)
      (fun l hl => (C5 l hl).2) fun i hi _ _ => hR i hi (by omega)
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide, coeffAddr_add]
  · rw [g5, h84, o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g5, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; exact k5.1
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; exact k5.2
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o5 c4
      (by decide) (by decide)
  · exact o5.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

theorem gath2_ok (t : State) :
    WP isa (.block gath2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm1) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm1)) ∧ XOnly [.xmm2, .xmm0, .xmm1] t t' := by
  simp only [gath2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat2_ok (t : State) :
    WP isa (.block scat2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem gath1_ok (t : State) :
    WP isa (.block gath1) t fun t' =>
      (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8)) ∧
        XOnly [.xmm0, .xmm2, .xmm1] t t' := by
  simp only [gath1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat1_ok (t : State) :
    WP isa (.block scat1) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpckldq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
include hbf

/-- `vlay2`'s work on the coefficients `A` of `xmm0` and `B` of `xmm1`: the
blocks `A` and `B` of `len = 2`, with the zetas `ζ` (the first two for `A`,
the last two for `B`). -/
theorem core2_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm1) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath2 ++ bf ++ scat2)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e < 2 then (op (A e) (A (2 + e)) (ζ e)).1
          else (op (A (e - 2)) (A e) (ζ (e - 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e < 2 then (op (B e) (B (2 + e)) (ζ (2 + e))).1
          else (op (B (e - 2)) (B e) (ζ e)).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.gath2_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A e else B (e - 2)) (fun e => if e < 2 then A (2 + e) else B e) ζ
    (fun e he => by
      dsimp only; rw [e0, VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA e he
      · exact hB (e - 2) (by omega))
    (fun e he => by
      dsimp only; rw [e1, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA (2 + e) (by omega)
      · exact hB e he)
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.scat2_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he]
    split
    · rw [X e he]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›)]
    · rw [Y (e - 2) (by omega)]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), show 2 + (e - 2) = e by omega]
  · rw [f1, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he]
    split
    · rw [X (2 + e) (by omega)]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), show 2 + e - 2 = e by omega]
    · rw [Y e he]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›)]
  · exact ((o1.trans o2).trans o3).mono (by simp)

/-- `vlay1`'s work on the coefficients `A` of `xmm0` and `B` of `xmm2`: the
blocks `A₀₁`, `A₂₃`, `B₀₁` and `B₂₃` of `len = 1`, with the zetas `ζ`. -/
theorem core1_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm2) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath1 ++ bf ++ scat1)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e % 2 = 0 then (op (A e) (A (e + 1)) (ζ (e / 2))).1
          else (op (A (e - 1)) (A e) (ζ (e / 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e % 2 = 0 then (op (B e) (B (e + 1)) (ζ (2 + e / 2))).1
          else (op (B (e - 1)) (B e) (ζ (2 + e / 2))).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.gath1_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A (2 * e) else B (2 * (e - 2))) (fun e => if e < 2 then A (2 * e + 1) else B (2 * (e - 2) + 1))
    ζ
    (fun e he => by
      dsimp only; rw [e0, VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ he, ite_eq_left h]; exact hA _ (by omega)
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ (by omega), ite_eq_left (by omega)]; exact hB _ (by omega))
    (fun e he => by
      dsimp only; rw [e1, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ (by omega), ite_eq_right (by omega), show 2 * (2 + e - 2) + 1 = 2 * e + 1 by omega]
        exact hA _ (by omega)
      · rw [VG.Proof.MlDsa.X86_64.Arith.dword_d8 _ he, ite_eq_right h]; exact hB _ (by omega))
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.scat1_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, VG.Proof.MlDsa.X86_64.Arith.dword_punpckldq' _ _ he]
    split
    · rw [X (e / 2) (by omega)]; dsimp only
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left ‹e % 2 = 0›,
        show 2 * (e / 2) = e by omega]
    · rw [Y (e / 2) (by omega)]; dsimp only
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (e / 2) = e - 1 by omega, show e - 1 + 1 = e by omega]
  · rw [f1, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhdq' _ _ he]
    split
    · rw [X (2 + e / 2) (by omega)]; dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ‹e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e by omega]
    · rw [Y (2 + e / 2) (by omega)]; dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e - 1 by omega, show e - 1 + 1 = e by omega]
  · exact ((o1.trans o2).trans o3).mono (by simp)

end

/-! ## The zetas of the layer with `len = 1` -/

/-- A doubleword of four of the zetas, at index `i` of the table. -/
theorem dword_tab {m : Mem} {zP : Addr} (ht : Tab zmTab m zP 256) {j e i : Nat} (he : e < 4) (hi : j + e = i)
    (hi' : i < 256) : (dword (m.readW (coeffAddr zP j) 128) e).toNat = (zetas i).val * 2 ^ 32 % q := by
  subst hi; rw [dword_readW _ _ he, coeffAddr_add]; exact tab_zeta ht hi'

/-- `vpermq` with `0x27`: lane 0 is `punpckhqdq` of the upper and the lower lane, lane 1 their `punpcklqdq`. -/
theorem perm27 (a b : BitVec 128) :
    permQwords (b ++ a) 0x27 = qword256 (b ++ a) 0 ++ qword256 (b ++ a) (2 + 0) ++
      qword256 (b ++ a) 1 ++ qword256 (b ++ a) (2 + 1) := rfl

theorem perm27_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 0 128 = XBinOp.eval .punpckhqdq b a := by
  rw [VG.Proof.MlDsa.X86_64.Arith.perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), lo4]; rfl

theorem perm27_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 128 128 = XBinOp.eval .punpcklqdq b a := by
  rw [VG.Proof.MlDsa.X86_64.Arith.perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), hi4]; rfl

/-- `vpermq d, r, 0x27`. -/
theorem ypermq27_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0x27)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpckhqdq (s.lane r 1) (s.lane r 0) ∧
      s'.lane d 1 = XBinOp.eval .punpcklqdq (s.lane r 1) (s.lane r 0) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, VG.Proof.MlDsa.X86_64.Arith.perm27_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, VG.Proof.MlDsa.X86_64.Arith.perm27_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT`: in lane `l`, zetas `k + 2l`, `k + 2l + 1`, `k + 2l + 4`
and `k + 2l + 5`. -/
theorem yzeta8_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yF5_ok s2) fun s3 ⟨f3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  rw [f3 l hl, o3.lane _ (by decide) l hl]
  refine ⟨fun e he => ?_, VG.Proof.MlDsa.X86_64.Arith.zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  rcases lane01 hl with rfl | rfl
  · rw [e0, VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht he (by omega) (by omega)
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht (by omega) (by omega) (by omega)
  · rw [e1, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht (by omega) (by omega) (by omega)
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht he (by omega) (by omega)

theorem dword_b1 (x : BitVec 128) {e : Nat} (he : e < 4) :
    dword (shufDwords x 0xB1) e = dword x (if e % 2 = 0 then e + 1 else e - 1) := by
  rw [dword_shufDwords _ _ he]
  rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl

theorem zsseR_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0xB1), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0xB1 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0xB1) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT⁻¹`, which take them in decreasing order: in lane `l`, zetas
`k + 7 - 2l`, `k + 6 - 2l`, `k + 3 - 2l` and `k + 2 - 2l`. -/
theorem yzeta8R_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8R) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + 7 - (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8R, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.ypermq27_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s2.lane .xmm13 l) 0xB1 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s2.lane .xmm13 l) 0xB1) 0xF5)
    fun l _ => VG.Proof.MlDsa.X86_64.Arith.zsseR_ok (s2.proj l)) fun s3 ⟨l3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  have e13 : s3.lane .xmm13 l = _ := (l3 l hl).1
  have e12 : s3.lane .xmm12 l = _ := (l3 l hl).2
  rw [e12, e13]
  refine ⟨fun e he => ?_, VG.Proof.MlDsa.X86_64.Arith.zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  have he' : (if e % 2 = 0 then e + 1 else e - 1) < 4 := by split <;> omega
  rw [VG.Proof.MlDsa.X86_64.Arith.dword_b1 _ he]
  generalize hf : (if e % 2 = 0 then e + 1 else e - 1) = f at he'
  have hf' : f = if e % 2 = 0 then e + 1 else e - 1 := hf.symm
  rcases lane01 hl with rfl | rfl
  · rw [e0, VG.Proof.MlDsa.X86_64.Arith.dword_punpckhqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht (by omega) (by split at hf' <;> omega) (by omega)
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht he' (by split at hf' <;> omega) (by omega)
  · rw [e1, VG.Proof.MlDsa.X86_64.Arith.dword_punpcklqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht he' (by split at hf' <;> omega) (by omega)
    · exact VG.Proof.MlDsa.X86_64.Arith.dword_tab ht (by omega) (by split at hf' <;> omega) (by omega)

/-! ## The layers -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : VG.Spec.MlDsa.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlDsa.Poly} (hblk : BlkOk blk op)
include hblk

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 2`. -/
theorem layF2_next (F : VG.Spec.MlDsa.Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 2 zi (4 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 2) < 2 then
        (op (layF blk F 2 zi (4 * i))[x]! (layF blk F 2 zi (4 * i))[x + 2]! (zetas (zi (x / (2 * 2))))).1
      else (op (layF blk F 2 zi (4 * i))[x - 2]! (layF blk F 2 zi (4 * i))[x]! (zetas (zi (x / (2 * 2))))).2)
      else (layF blk F 2 zi (4 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 2 zi (4 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
  rw [VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    by_cases h2 : x % (2 * 2) < 2
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hx]
  · rw [ite_eq_right h1, VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 2 * (4 * (i + 1)) by omega), ite_eq_left (show x < 2 * 2 * (4 * i) by omega)]
    · rw [ite_eq_right (show ¬ x < 2 * 2 * (4 * (i + 1)) by omega),
        ite_eq_right (show ¬ x < 2 * 2 * (4 * i) by omega)]

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 1`. -/
theorem layF1_next (F : VG.Spec.MlDsa.Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 1 zi (8 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 1) < 1 then
        (op (layF blk F 1 zi (8 * i))[x]! (layF blk F 1 zi (8 * i))[x + 1]! (zetas (zi (x / (2 * 1))))).1
      else (op (layF blk F 1 zi (8 * i))[x - 1]! (layF blk F 1 zi (8 * i))[x]! (zetas (zi (x / (2 * 1))))).2)
      else (layF blk F 1 zi (8 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 1 zi (8 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
  rw [VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    by_cases h2 : x % (2 * 1) < 1
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hx]
  · rw [ite_eq_right h1, VG.Proof.MlDsa.X86_64.Arith.layF_get hblk F (by decide) zi (by omega) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 1 * (8 * (i + 1)) by omega), ite_eq_left (show x < 2 * 1 * (8 * i) by omega)]
    · rw [ite_eq_right (show ¬ x < 2 * 1 * (8 * (i + 1)) by omega),
        ite_eq_right (show ¬ x < 2 * 1 * (8 * i) by omega)]

variable {bf : List Instr} (hbf : VBflyOk bf op)
include hbf

theorem ylay2_ok (hY : laneSseBlock (toY (gath2 ++ bf ++ scat2)) = some (gath2 ++ bf ++ scat2)) {fP sP : Addr}
    (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 4 ≤ 256)
    (hsel : ∀ i < 16, ∀ e < 4, kb i + sel o₀ e = zi (4 * i + 2 * (e / 2)) ∧
      kb i + sel o₁ e = zi (4 * i + 1 + 2 * (e / 2)))
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay2 bf k o₀ o₁ dz) s fun s' => PolyIs s'.mem fP (layF blk F 2 zi 64) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 2 zi (4 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  have hk0' : ∀ j < 4, kb i + sel o₀ j < 256 := fun j _ => by have := sel_lt o₀ j; have := hk i hi; omega
  have hk1' : ∀ j < 4, kb i + sel o₁ j < 256 := fun j _ => by have := sel_lt o₁ j; have := hk i hi; omega
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx 32)] ++ yzetaS o₀ o₁ ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath2 ++ bf ++ scat2) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      VG.Proof.MlDsa.X86_64.Arith.ybody21 .xmm1 (yzetaS o₀ o₁) (gath2 ++ bf ++ scat2) dz by simp [List.append_assoc]]
  have hR := fun x hx => VG.Proof.MlDsa.X86_64.Arith.layF2_next hblk F zi hi (x := x) hx
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.ystep21 hY (zs := [.xmm13, .xmm2, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (j := 16 * i) (by omega) (R := layF blk F 2 zi (4 * (i + 1)))
    (ζ := fun l e => zetas (zi (4 * i + l + 2 * (e / 2)))) hb'.consts hdx' hS' hwf' (fun s' k' => ?_)
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega)]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  · -- the zetas
    refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.yzetaS_ok o₀ o₁ (zP := sP) (k := kb i) hk0' hk1' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact tab_in (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
      fun s'' ⟨Z0, Z1, ZO, o⟩ => ⟨fun l hl => ⟨?_, ZO l hl⟩, o⟩
    rcases lane01 hl with rfl | rfl
    · exact Z0.congr fun e he => congrArg zetas ((hsel i hi e he).1.trans (congrArg zi (by omega)))
    · exact Z1.congr fun e he => congrArg zetas ((hsel i hi e he).2.trans (congrArg zi (by omega)))
  · -- the blocks of a lane
    refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.core2_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
      ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
      · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
      · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))

theorem ylay1_ok (hY : laneSseBlock (toY (gath1 ++ bf ++ scat1)) = some (gath1 ++ bf ++ scat1)) {fP sP : Addr}
    (k : Nat) (zl : List Instr) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 8 ≤ 256)
    (hzl : ∀ i < 16, ∀ s : State, s.gpr .r8 = coeffAddr sP (kb i) →
      InRegions (s.rd ++ s.wr) (coeffAddr sP (kb i)) 32 → Tab zmTab s.mem sP 256 →
      WP isa (.block zl) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l)
          (fun e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) ∧ ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧
        YOnly [.xmm13, .xmm12] s s')
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : VG.Spec.MlDsa.Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay1 bf k zl dz) s fun s' => PolyIs s'.mem fP (layF blk F 1 zi 128) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Arith.ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 1 zi (8 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ VG.Proof.MlDsa.X86_64.Arith.BInvY fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        VG.Proof.MlDsa.X86_64.Arith.ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm2 (at_ .rdx 32)] ++ zl ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath1 ++ bf ++ scat1) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      VG.Proof.MlDsa.X86_64.Arith.ybody21 .xmm2 zl (gath1 ++ bf ++ scat1) dz by simp [List.append_assoc]]
  have hR := fun x hx => VG.Proof.MlDsa.X86_64.Arith.layF1_next hblk F zi hi (x := x) hx
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.ystep21 hY (zs := [.xmm13, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (j := 16 * i) (by omega) (R := layF blk F 1 zi (8 * (i + 1)))
    (ζ := fun l e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) hb'.consts hdx' hS' hwf'
    (fun s' k' => hzl i hi s' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact f_in32 (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega)]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  -- the blocks of a lane
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.core1_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
    ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (VG.Proof.MlDsa.X86_64.Arith.op_idx op _ zi (by omega) (by omega) (by omega))

end

end VG.Proof.MlDsa.X86_64.Arith

end
