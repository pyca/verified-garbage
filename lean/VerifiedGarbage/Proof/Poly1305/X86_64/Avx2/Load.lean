import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Poly1305.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: straight-line code, quadword by quadword

The vector code of `vg_poly1305_blocks_avx2` moves, adds, multiplies, masks
and shifts the four quadwords of `ymm` registers, and loads 64 bytes at `rsi`.
`Sym.run` computes each quadword after a block of such instructions as a term
(`Q`) in the quadwords, general-purpose registers and memory before it, and
`srun_ok` proves the machine agrees. Every instruction but the loads,
`vpermq`, `vpunpck{l,h}qdq`, `vmovq` and `vpbroadcastq` acts on each quadword
on its own, so a term is evaluated at a quadword (a lane) `k < 4`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64

/-! ## Registers and quadwords -/

/-- The vector register numbered `i`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- The number of a vector register. -/
def xi : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

theorem xr_xi (r : XReg) : VG.Proof.Poly1305.X86_64.Avx2.xr (VG.Proof.Poly1305.X86_64.Avx2.xi r) = r := by cases r <;> rfl

theorem xi_inj {r r' : XReg} : VG.Proof.Poly1305.X86_64.Avx2.xi r = VG.Proof.Poly1305.X86_64.Avx2.xi r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

/-- Quadword `k` (`k < 4`) of `ymm r`. -/
def qw (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.lane r (k / 2)) (k % 2)

theorem cases4 {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

/-! ### Quadwords of values -/

@[simp] theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem qword_app1 (a b : BitVec 64) : qword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem qword_eq (v : BitVec 128) (i : Nat) : qword v i = dword v (2 * i + 1) ++ dword v (2 * i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  by_cases h : j < 32
  · simp only [h, ite_true, decide_true, Bool.true_and]; congr 1; omega
  · simp only [h, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]; congr 1; omega

theorem qword_and (x y : BitVec 128) (i : Nat) : qword (x &&& y) i = qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_or (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_andn (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (~~~x &&& y) i = ~~~qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj, show 64 * i + j < 128 by omega]

theorem dword_lo (x : BitVec 128) (i : Nat) : dword x (2 * i) = (qword x i).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 0 + j < 64 by omega)]
  exact congrArg _ (by omega)

theorem dword_hi (x : BitVec 128) (i : Nat) : dword x (2 * i + 1) = (qword x i).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 32 + j < 64 by omega)]
  exact congrArg _ (by omega)

/-- The low doubleword of a quadword, zero-extended. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x.extractLsb' 0 32).setWidth 64

theorem qword_paddq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .paddq x y) i = qword x i + qword y i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_pmuludq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pmuludq x y) i = VG.Proof.Poly1305.X86_64.Avx2.lo32 (qword x i) * VG.Proof.Poly1305.X86_64.Avx2.lo32 (qword y i) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XBinOp.eval, VG.Proof.Poly1305.X86_64.Avx2.qword_app0, VG.Proof.Poly1305.X86_64.Avx2.lo32, ← VG.Proof.Poly1305.X86_64.Avx2.dword_lo]
  · simp only [XBinOp.eval, VG.Proof.Poly1305.X86_64.Avx2.qword_app1, VG.Proof.Poly1305.X86_64.Avx2.lo32, ← VG.Proof.Poly1305.X86_64.Avx2.dword_lo]

theorem qword_punpcklqdq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .punpcklqdq x y) i = if i = 0 then qword x 0 else qword y 0 := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_punpckhqdq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .punpckhqdq x y) i = if i = 0 then qword x 1 else qword y 1 := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_psllq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psllq x n) i = qword x i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem qword_psrlq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x n) i = qword x i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

/-- A quadword from its doublewords picked by two selector bits. -/
def pick2 (a b : BitVec 64) (lo hi : Bool) : BitVec 64 :=
  (if hi then b.extractLsb' 32 32 else a.extractLsb' 32 32) ++
    (if lo then b.extractLsb' 0 32 else a.extractLsb' 0 32)

theorem qword_ofDwords (a b c d : BitVec 32) {i : Nat} (hi : i < 2) :
    qword (ofDwords a b c d) i = if i = 0 then b ++ a else d ++ c := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rw [VG.Proof.Poly1305.X86_64.Avx2.qword_eq] <;> simp

theorem qword_blendDwords (x y : BitVec 128) (imm : BitVec 4) {i : Nat} (hi : i < 2) :
    qword (blendDwords x y imm) i =
      VG.Proof.Poly1305.X86_64.Avx2.pick2 (qword x i) (qword y i) (imm.getLsbD (2 * i)) (imm.getLsbD (2 * i + 1)) := by
  simp only [blendDwords]
  rw [VG.Proof.Poly1305.X86_64.Avx2.qword_ofDwords _ _ _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [ite_true, VG.Proof.Poly1305.X86_64.Avx2.pick2, ← VG.Proof.Poly1305.X86_64.Avx2.dword_lo, ← VG.Proof.Poly1305.X86_64.Avx2.dword_hi, Nat.mul_zero, Nat.zero_add]
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, VG.Proof.Poly1305.X86_64.Avx2.pick2, ← VG.Proof.Poly1305.X86_64.Avx2.dword_lo, ← VG.Proof.Poly1305.X86_64.Avx2.dword_hi]

/-- Quadword `k` (`k < 4`) of a 256-bit value. -/
theorem qword256_eq (x : BitVec 256) (k : Nat) :
    qword256 x k = qword (x.extractLsb' (128 * (k / 2)) 128) (k % 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * (k % 2) + j < 128 by omega)]
  congr 1; omega

theorem qword256_ymm (s : State) (r : XReg) {k : Nat} (hk : k < 4) : qword256 (s.ymm r) k = VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  rw [VG.Proof.Poly1305.X86_64.Avx2.qword256_eq, VG.Proof.Poly1305.X86_64.Avx2.qw]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> simp [hj]

theorem qword256_cat (a b c d : BitVec 64) {k : Nat} (hk : k < 4) :
    qword256 (a ++ b ++ c ++ d) k = if k = 0 then d else if k = 1 then c else if k = 2 then b else a := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have e : (a ++ b ++ c ++ d).toNat = ((a.toNat * 2 ^ 64 + b.toNat) * 2 ^ 64 + c.toNat) * 2 ^ 64 + d.toNat := by
    rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, ← Nat.shiftLeft_add_eq_or_of_lt c.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt d.isLt]
    simp only [Nat.shiftLeft_eq]
  simp only [qword256, BitVec.extractLsb'_toNat, e, Nat.shiftRight_eq_div_pow]
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- The selector of quadword `k` in `vpermq`'s immediate. -/
def sel4 (o k : Nat) : Nat := o / 4 ^ k % 4

theorem sel4_lt (o k : Nat) : VG.Proof.Poly1305.X86_64.Avx2.sel4 o k < 4 := Nat.mod_lt _ (by decide)

theorem qword256_perm (x : BitVec 256) (o : BitVec 8) {k : Nat} (hk : k < 4) :
    qword256 (permQwords x o) k = qword256 x (VG.Proof.Poly1305.X86_64.Avx2.sel4 o.toNat k) := by
  have e : ∀ i, (o.extractLsb' (2 * i) 2).toNat = VG.Proof.Poly1305.X86_64.Avx2.sel4 o.toNat i := fun i => by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul, VG.Proof.Poly1305.X86_64.Avx2.sel4]
  simp only [permQwords, VG.Proof.Poly1305.X86_64.Avx2.qword256_cat _ _ _ _ hk, e]
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-! ### Quadwords of registers after an instruction -/

theorem qw_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (k : Nat) :
    VG.Proof.Poly1305.X86_64.Avx2.qw (s.setV .l256 d lo hi) r k = if r = d then qword (if k / 2 = 0 then lo else hi) (k % 2) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.qw, State.lane_setV256]
  split <;> rfl

theorem qw_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) (k : Nat) :
    VG.Proof.Poly1305.X86_64.Avx2.qw (s.setV .l128 d lo hi) r k = if r = d then (if k / 2 = 0 then qword lo (k % 2) else 0) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.qw, State.lane_setV128]
  split
  · split
    · rfl
    · simp [qword]
  · rfl

/-- `qw` of the lane of `k`. -/
theorem qw_lane (s : State) (r : XReg) (k : Nat) : qword (s.lane r (k / 2)) (k % 2) = VG.Proof.Poly1305.X86_64.Avx2.qw s r k := rfl

theorem lane_sel (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (if k / 2 = 0 then s.lane r 0 else s.lane r 1) = s.lane r (k / 2) := by
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem qw_vbin (op : VBinOp) (s : State) (d a b r : XReg) (k : Nat) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vbin op .l256 d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.qw, lane_vbin256]
  split <;> rfl

theorem qw_vshift (op : XShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) (k : Nat) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vshift op .l256 d a n).exec s) r k =
      if r = d then qword (op.eval (s.lane a (k / 2)) n) (k % 2) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.qw, lane_vshift256]
  split <;> rfl

theorem qw_vmovdqa (s : State) (d a r : XReg) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vmovdqa .l256 d a).exec s) r k = if r = d then VG.Proof.Poly1305.X86_64.Avx2.qw s a k else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx2.qw_setV256, VG.Proof.Poly1305.X86_64.Avx2.lane_sel _ _ hk, VG.Proof.Poly1305.X86_64.Avx2.qw_lane]

theorem getLsbD_nibble (n : BitVec 8) (l j : Nat) (hj : j < 4) :
    (n.extractLsb' (4 * l) 4).getLsbD j = n.toNat.testBit (4 * l + j) := by
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, BitVec.testBit_toNat]

theorem qw_vpblendd (s : State) (d a b r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vpblendd .l256 d a b n).exec s) r k =
      if r = d then VG.Proof.Poly1305.X86_64.Avx2.pick2 (VG.Proof.Poly1305.X86_64.Avx2.qw s a k) (VG.Proof.Poly1305.X86_64.Avx2.qw s b k) (n.toNat.testBit (2 * k)) (n.toNat.testBit (2 * k + 1))
      else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx2.qw_setV256]
  split
  · have e : (if k / 2 = 0 then blendDwords (s.lane a 0) (s.lane b 0) (n.extractLsb' 0 4)
        else blendDwords (s.lane a 1) (s.lane b 1) (n.extractLsb' 4 4)) =
        blendDwords (s.lane a (k / 2)) (s.lane b (k / 2)) (n.extractLsb' (4 * (k / 2)) 4) := by
      rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, VG.Proof.Poly1305.X86_64.Avx2.qword_blendDwords _ _ _ (Nat.mod_lt _ (by decide)), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane,
      VG.Proof.Poly1305.X86_64.Avx2.getLsbD_nibble _ _ _ (by omega), VG.Proof.Poly1305.X86_64.Avx2.getLsbD_nibble _ _ _ (by omega),
      show 4 * (k / 2) + 2 * (k % 2) = 2 * k by omega,
      show 4 * (k / 2) + (2 * (k % 2) + 1) = 2 * k + 1 by omega]
  · rfl

theorem qw_vpbroadcastq (s : State) (d a r : XReg) (k : Nat) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vpbroadcastq .l256 d a).exec s) r k = if r = d then VG.Proof.Poly1305.X86_64.Avx2.qw s a 0 else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx2.qw_setV256]
  split
  · have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> split <;> simp [VG.Proof.Poly1305.X86_64.Avx2.qw, State.lane]
  · rfl

theorem qw_vmovq (s : State) (d r : XReg) (g : Reg) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vmovq d g).exec s) r k = if r = d then (if k = 0 then s.gpr g else 0) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx2.qw_setV128]
  split
  · rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> simp
  · rfl

theorem qw_vpermq (s : State) (d a r : XReg) (o : BitVec 8) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86_64.Avx2.qw ((VOp.vpermq d a o).exec s) r k = if r = d then VG.Proof.Poly1305.X86_64.Avx2.qw s a (VG.Proof.Poly1305.X86_64.Avx2.sel4 o.toNat k) else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx2.qw_setV256]
  split
  · rw [← VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm _ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _), ← VG.Proof.Poly1305.X86_64.Avx2.qword256_perm _ _ hk, VG.Proof.Poly1305.X86_64.Avx2.qword256_eq]
    rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem qw_load (s : State) (d r : XReg) (a : Addr) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86_64.Avx2.qw (s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  rw [VG.Proof.Poly1305.X86_64.Avx2.qw_setV256]
  split
  · have e : (if k / 2 = 0 then (s.mem.readW a 256).extractLsb' 0 128 else (s.mem.readW a 256).extractLsb' 128 128) =
        (s.mem.readW a 256).extractLsb' (128 * (k / 2)) 128 := by
      rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, ← VG.Proof.Poly1305.X86_64.Avx2.qword256_eq, qword256, show 64 * k = 8 * (8 * k) by omega]
    exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)
  · rfl

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive Q
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : VG.Proof.Poly1305.X86_64.Avx2.Q)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : VG.Proof.Poly1305.X86_64.Avx2.Q)
  /-- Quadword `i + k` of memory at `rsi`. -/
  | ld (i : Nat)
  | add (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  /-- The product of the low doublewords. -/
  | mul (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  | and (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  /-- `~a & b`. -/
  | andn (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  | or (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  | shl (a : VG.Proof.Poly1305.X86_64.Avx2.Q) (n : Nat)
  | shr (a : VG.Proof.Poly1305.X86_64.Avx2.Q) (n : Nat)
  /-- `vpunpcklqdq`, `vpunpckhqdq`. -/
  | unpl (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  | unph (a b : VG.Proof.Poly1305.X86_64.Avx2.Q)
  /-- `vpermq` with the immediate `o`. -/
  | perm (a : VG.Proof.Poly1305.X86_64.Avx2.Q) (o : Nat)
  /-- `vpblendd` with the immediate `sel`. -/
  | blend (a b : VG.Proof.Poly1305.X86_64.Avx2.Q) (sel : Nat)
  deriving DecidableEq, Repr

def Q.eval (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx2.Q → Nat → BitVec 64
  | .reg r, k => VG.Proof.Poly1305.X86_64.Avx2.qw s₀ (VG.Proof.Poly1305.X86_64.Avx2.xr r) k
  | .gpr r, _ => s₀.gpr r
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld i, k => s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * (i + k))) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .mul a b, k => VG.Proof.Poly1305.X86_64.Avx2.lo32 (a.eval s₀ k) * VG.Proof.Poly1305.X86_64.Avx2.lo32 (b.eval s₀ k)
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .andn a b, k => ~~~a.eval s₀ k &&& b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .perm a o, k => a.eval s₀ (VG.Proof.Poly1305.X86_64.Avx2.sel4 o k)
  | .blend a b sel, k => VG.Proof.Poly1305.X86_64.Avx2.pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))

/-! ## The machine -/

/-- The terms of the vector registers (by number). -/
structure Sym where
  reg : Nat → VG.Proof.Poly1305.X86_64.Avx2.Q

def Sym.init : VG.Proof.Poly1305.X86_64.Avx2.Sym := ⟨.reg⟩

def Sym.set (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) (d : XReg) (t : VG.Proof.Poly1305.X86_64.Avx2.Q) : VG.Proof.Poly1305.X86_64.Avx2.Sym := ⟨fun r => if r = VG.Proof.Poly1305.X86_64.Avx2.xi d then t else σ.reg r⟩

def Sym.bin (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) (op : VBinOp) (d a b : XReg) : Option VG.Proof.Poly1305.X86_64.Avx2.Sym :=
  let A := σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)
  let B := σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpmuludq => some (σ.set d (.mul A B))
  | .vpand => some (σ.set d (.and A B))
  | .vpandn => some (σ.set d (.andn A B))
  | .vpor => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.shift (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Option VG.Proof.Poly1305.X86_64.Avx2.Sym :=
  if n.toNat < 64 then
    match op with
    | .psllq => some (σ.set d (.shl (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)) n.toNat))
    | .psrlq => some (σ.set d (.shr (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)) n.toNat))
    | _ => none
  else none

def Sym.vop (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) : VOp → Option VG.Proof.Poly1305.X86_64.Avx2.Sym
  | .vbin op .l256 d a b => σ.bin op d a b
  | .vshift op .l256 d a n => σ.shift op d a n
  | .vmovdqa .l256 d a => some (σ.set d (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)))
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)) (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a))))
  | .vmovq d r => some (σ.set d (.lane0 (.gpr r)))
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)) o.toNat))
  | _ => none

/-- A load of 32 bytes at `rsi + 8 i` (for `i` 0 or 4). -/
def ldIdx (m : MemOp) : Option Nat :=
  if m.base = .rsi ∧ m.index = none then
    if m.disp = 0 then some 0 else if m.disp = 32 then some 4 else none
  else none

/-- One instruction; loads only if `ld`. -/
def Sym.step (ld : Bool) (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) : Instr → Option VG.Proof.Poly1305.X86_64.Avx2.Sym
  | .vop o => σ.vop o
  | .vmovdquLoad .l256 d m => if ld then (VG.Proof.Poly1305.X86_64.Avx2.ldIdx m).map fun i => σ.set d (.ld i) else none
  | _ => none

def Sym.run (ld : Bool) (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) : List Instr → Option VG.Proof.Poly1305.X86_64.Avx2.Sym
  | [] => some σ
  | i :: is => (σ.step ld i).bind fun σ' => σ'.run ld is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers of `s`. -/
def vec (s₀ s : State) : State := { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi }

theorem vec_vop {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) (o : VOp) : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vec_setV {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    VG.Proof.Poly1305.X86_64.Avx2.vec s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem vec_trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s₁ = s₁) (h₂ : VG.Proof.Poly1305.X86_64.Avx2.vec s₁ s₂ = s₂) : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s₂ = s₂ := by
  rw [← h₂, ← h₁]; rfl

theorem vec_gpr {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) : s.gpr = s₀.gpr := by rw [← h]; rfl
theorem vec_mem {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) : s.mem = s₀.mem := by rw [← h]; rfl
theorem vec_rd {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) : s.rd = s₀.rd := by rw [← h]; rfl
theorem vec_wr {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s) : s.wr = s₀.wr := by rw [← h]; rfl

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure SRel (σ : VG.Proof.Poly1305.X86_64.Avx2.Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → VG.Proof.Poly1305.X86_64.Avx2.qw s r k = (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi r)).eval s₀ k
  eq : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s = s

theorem SRel.gpr {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem SRel.mem {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem SRel.rd {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl

theorem SRel.init (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx2.SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, Q.eval, VG.Proof.Poly1305.X86_64.Avx2.xr_xi], rfl⟩

theorem SRel.set {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) {d : XReg} {t : VG.Proof.Poly1305.X86_64.Avx2.Q} {s' : State}
    (hv : ∀ r k, k < 4 → VG.Proof.Poly1305.X86_64.Avx2.qw s' r k = if r = d then t.eval s₀ k else VG.Proof.Poly1305.X86_64.Avx2.qw s r k)
    (he : VG.Proof.Poly1305.X86_64.Avx2.vec s₀ s' = s') : VG.Proof.Poly1305.X86_64.Avx2.SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he⟩
  rw [hv r k hk]
  simp only [Sym.set, VG.Proof.Poly1305.X86_64.Avx2.xi_inj]
  split
  · rfl
  · exact h.reg r k hk


/-- What the loads may read: 64 bytes at `rsi`. -/
def Ctx (s₀ : State) : Prop :=
  ∀ i, i = 0 ∨ i = 4 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 32

theorem ldIdx_ok {m : MemOp} {i : Nat} (h : VG.Proof.Poly1305.X86_64.Avx2.ldIdx m = some i) :
    (i = 0 ∨ i = 4) ∧ ∀ s : State, s.ea m = s.gpr .rsi + BitVec.ofNat 64 (8 * i) := by
  unfold VG.Proof.Poly1305.X86_64.Avx2.ldIdx at h
  split at h
  · rename_i hb
    split at h
    · cases h
      refine ⟨.inl rfl, fun s => ?_⟩
      simp only [State.ea, hb.2, hb.1, *]; rfl
    · split at h
      · cases h
        refine ⟨.inr rfl, fun s => ?_⟩
        simp only [State.ea, hb.2, hb.1, *]; rfl
      · cases h
  · cases h

theorem hv_of {s s' : State} {d : XReg} {f : Nat → BitVec 64} (hd : ∀ k, k < 4 → VG.Proof.Poly1305.X86_64.Avx2.qw s' d k = f k)
    (ho : ∀ r, r ≠ d → ∀ k, k < 4 → VG.Proof.Poly1305.X86_64.Avx2.qw s' r k = VG.Proof.Poly1305.X86_64.Avx2.qw s r k) :
    ∀ r k, k < 4 → VG.Proof.Poly1305.X86_64.Avx2.qw s' r k = if r = d then f k else VG.Proof.Poly1305.X86_64.Avx2.qw s r k := by
  intro r k hk
  by_cases hr : r = d
  · subst hr; rw [ite_eq_left rfl]; exact hd k hk
  · rw [ite_eq_right hr]; exact ho r hr k hk

theorem mod2_lt (k : Nat) : k % 2 < 2 := Nat.mod_lt _ (by decide)

theorem sstep_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx2.Ctx s₀) {σ σ' : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s : State}
    (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) {i : Instr} (e : σ.step ld i = some σ') : ∃ s', exec i s = some s' ∧ VG.Proof.Poly1305.X86_64.Avx2.SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi a)).eval s₀ k = VG.Proof.Poly1305.X86_64.Avx2.qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := VG.Proof.Poly1305.X86_64.Avx2.vec_vop h.eq o
    unfold Sym.vop at e
    split at e
    · rename_i op d a b
      unfold Sym.bin at e
      split at e <;> cases e <;>
        refine h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => ?_) (fun r hr k _ => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vbin, ite_eq_right hr])) he <;>
        rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vbin, ite_eq_left rfl] <;> simp only [VBinOp.sse, Q.eval]
      · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_paddq _ _ (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk, hR b k hk]
      · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_pmuludq _ _ (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, VG.Proof.Poly1305.X86_64.Avx2.qword_and, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, VG.Proof.Poly1305.X86_64.Avx2.qword_andn _ _ (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, VG.Proof.Poly1305.X86_64.Avx2.qword_or, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk, hR b k hk]
      · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_punpcklqdq _ _ (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, VG.Proof.Poly1305.X86_64.Avx2.qw, h0]
        · rw [hR b (k - 1) (by omega), VG.Proof.Poly1305.X86_64.Avx2.qw, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_punpckhqdq _ _ (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), VG.Proof.Poly1305.X86_64.Avx2.qw, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, VG.Proof.Poly1305.X86_64.Avx2.qw, show k % 2 = 1 by omega]
    · rename_i op d a n
      unfold Sym.shift at e
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => ?_) (fun r hr k _ => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vshift, ite_eq_right hr])) he <;>
          rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vshift, ite_eq_left rfl] <;> simp only [Q.eval]
        · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_psllq _ hn (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk]
        · rw [VG.Proof.Poly1305.X86_64.Avx2.qword_psrlq _ hn (VG.Proof.Poly1305.X86_64.Avx2.mod2_lt k), VG.Proof.Poly1305.X86_64.Avx2.qw_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vmovdqa _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vmovdqa _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a b n
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => by
          rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k _ => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpbroadcastq, ite_eq_right hr])) he
    · rename_i d g
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, h.gpr])
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a o
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => by
          rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval]; rw [hR a _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _)])
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he
    · cases e
  · rename_i d m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hi, hea⟩ := VG.Proof.Poly1305.X86_64.Avx2.ldIdx_ok hs
    have ea : s.ea m = s₀.gpr .rsi + BitVec.ofNat 64 (8 * i) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 32 := by
      rw [h.rd, h.wr]; exact hc hld i hi
    refine ⟨s.setV .l256 d ((s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 256).extractLsb' 0 128)
      ((s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_⟩
    refine h.set (VG.Proof.Poly1305.X86_64.Avx2.hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, ite_eq_right hr]))
      (VG.Proof.Poly1305.X86_64.Avx2.vec_setV h.eq _ _ _ _)
    rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, ite_eq_left rfl, h.mem, Offset.add_add]; simp only [Q.eval, Nat.mul_add]
  · cases e

/-- A block of instructions. -/
theorem srun_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx2.Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s : State}, VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s → σ.run ld is = some σ' →
      WP isa (.block is) s (VG.Proof.Poly1305.X86_64.Avx2.SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := VG.Proof.Poly1305.X86_64.Avx2.sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, VG.Proof.Poly1305.X86_64.Avx2.srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx2.Ctx s₀) {is : List Instr} {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym}
    (e : Sym.init.run ld is = some σ) : WP isa (.block is) s₀ (VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀) :=
  VG.Proof.Poly1305.X86_64.Avx2.srun_ok hc is (SRel.init s₀) e

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Bound`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: terms as numbers

The limbs the code computes stay far below `2⁶⁴`, so its additions, products
and shifts never wrap. `Q.bnd` bounds each term from bounds on the registers
it starts from, `Q.ok` checks that its additions and left shifts do not wrap
under those bounds, and `Q.nat` is its value as a number, with the reductions
modulo `2⁶⁴` (and to the low doubleword, for products) left out. `nat_ok`
proves that a term is `Q.nat` and within `Q.bnd` where the kernel evaluates
`Q.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of `Limbs26` by definition. `Q.natw`
is the value with every reduction kept, which `natw_ok` proves exact for any
term, for the blocks that shift bits out on purpose.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64

/-- Bounds on the registers a block starts from: on each vector register's
quadwords (`v`) and their low doublewords (`lo`), and on the general-purpose
registers. -/
structure Bnds where
  v : XReg → Nat
  lo : XReg → Nat
  g : Reg → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat

def envOf (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx2.Env :=
  ⟨fun r k => (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ (VG.Proof.Poly1305.X86_64.Avx2.xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun j => (s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64).toNat⟩

def capW (x : Nat) : Nat := if x < 2 ^ 64 then x else 2 ^ 64 - 1

/-- A bound on `x ||| y` for `x ≤ a`, `y ≤ b`. -/
def orB (a b : Nat) : Nat := VG.Proof.Poly1305.X86_64.Avx2.capW (2 ^ max (a.log2 + 1) (b.log2 + 1) - 1)

/-- A bound on the low doubleword of `t`, whose bound is `b`. -/
def loB (B : VG.Proof.Poly1305.X86_64.Avx2.Bnds) (t : VG.Proof.Poly1305.X86_64.Avx2.Q) (b : Nat) : Nat :=
  match t with
  | .reg r => min (B.lo (VG.Proof.Poly1305.X86_64.Avx2.xr r)) (min b (2 ^ 32 - 1))
  | _ => min b (2 ^ 32 - 1)

def Q.bnd (B : VG.Proof.Poly1305.X86_64.Avx2.Bnds) : VG.Proof.Poly1305.X86_64.Avx2.Q → Nat → Nat
  | .reg r, _ => min (B.v (VG.Proof.Poly1305.X86_64.Avx2.xr r)) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld _, _ => 2 ^ 64 - 1
  | .add a b, k => VG.Proof.Poly1305.X86_64.Avx2.capW (a.bnd B k + b.bnd B k)
  | .mul a b, k => VG.Proof.Poly1305.X86_64.Avx2.loB B a (a.bnd B k) * VG.Proof.Poly1305.X86_64.Avx2.loB B b (b.bnd B k)
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .andn _ b, k => b.bnd B k
  | .or a b, k => VG.Proof.Poly1305.X86_64.Avx2.orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => VG.Proof.Poly1305.X86_64.Avx2.capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .perm a o, k => a.bnd B (VG.Proof.Poly1305.X86_64.Avx2.sel4 o k)
  | .blend _ _ _, _ => 2 ^ 64 - 1

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `Q.ok` holds. -/
def Q.nat (E : VG.Proof.Poly1305.X86_64.Avx2.Env) : VG.Proof.Poly1305.X86_64.Avx2.Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld i, k => E.m (i + k)
  | .add a b, k => a.nat E k + b.nat E k
  | .mul a b, k => a.nat E k % 2 ^ 32 * (b.nat E k % 2 ^ 32)
  | .and a b, k => a.nat E k &&& b.nat E k
  | .andn a b, k => (2 ^ 64 - 1 - a.nat E k) &&& b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .perm a o, k => a.nat E (VG.Proof.Poly1305.X86_64.Avx2.sel4 o k)
  | .blend a b sel, k =>
    (VG.Proof.Poly1305.X86_64.Avx2.pick2 (BitVec.ofNat 64 (a.nat E k)) (BitVec.ofNat 64 (b.nat E k)) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1))).toNat

/-- The value of a term as a number, reduced as the code does: exact
whatever the bounds (`natw_ok`), for the blocks that shift bits out on
purpose. -/
def Q.natw (E : VG.Proof.Poly1305.X86_64.Avx2.Env) : VG.Proof.Poly1305.X86_64.Avx2.Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.natw E 0 else 0
  | .bc a, _ => a.natw E 0
  | .ld i, k => E.m (i + k)
  | .add a b, k => (a.natw E k + b.natw E k) % 2 ^ 64
  | .mul a b, k => a.natw E k % 2 ^ 32 * (b.natw E k % 2 ^ 32)
  | .and a b, k => a.natw E k &&& b.natw E k
  | .andn a b, k => (2 ^ 64 - 1 - a.natw E k) &&& b.natw E k
  | .or a b, k => a.natw E k ||| b.natw E k
  | .shl a n, k => a.natw E k * 2 ^ n % 2 ^ 64
  | .shr a n, k => a.natw E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.natw E k else b.natw E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.natw E (k + 1) else b.natw E k
  | .perm a o, k => a.natw E (VG.Proof.Poly1305.X86_64.Avx2.sel4 o k)
  | .blend a b sel, k =>
    (VG.Proof.Poly1305.X86_64.Avx2.pick2 (BitVec.ofNat 64 (a.natw E k)) (BitVec.ofNat 64 (b.natw E k)) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1))).toNat

/-- No addition or left shift in `t` wraps, by the bounds `B`. -/
def Q.ok (B : VG.Proof.Poly1305.X86_64.Avx2.Bnds) : VG.Proof.Poly1305.X86_64.Avx2.Q → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .mul a b, k | .and a b, k | .andn a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .perm a o, k => a.ok B (VG.Proof.Poly1305.X86_64.Avx2.sel4 o k)
  | .blend a b _, k => a.ok B k && b.ok B k

/-- The registers `s₀` starts from are within `B`. -/
structure EnvOK (s₀ : State) (B : VG.Proof.Poly1305.X86_64.Avx2.Bnds) : Prop where
  v : ∀ r k, k < 4 → (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ r k).toNat ≤ B.v r
  lo : ∀ r k, k < 4 → (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ r k).toNat % 2 ^ 32 ≤ B.lo r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g

theorem capW_ge {x y : Nat} (h : x ≤ y) (hx : x < 2 ^ 64) : x ≤ VG.Proof.Poly1305.X86_64.Avx2.capW y := by
  unfold VG.Proof.Poly1305.X86_64.Avx2.capW; split <;> omega

theorem orB_ge {x y a b : Nat} (ha : x ≤ a) (hb : y ≤ b) (hx : x ||| y < 2 ^ 64) : x ||| y ≤ VG.Proof.Poly1305.X86_64.Avx2.orB a b := by
  apply VG.Proof.Poly1305.X86_64.Avx2.capW_ge _ hx
  have h₁ : x < 2 ^ max (a.log2 + 1) (b.log2 + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt ha Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have h₂ : y < 2 ^ max (a.log2 + 1) (b.log2 + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hb Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  have := Nat.or_lt_two_pow h₁ h₂
  omega

theorem lo32_toNat (x : BitVec 64) : (VG.Proof.Poly1305.X86_64.Avx2.lo32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.lo32, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

theorem loB_ge {s₀ : State} {B : VG.Proof.Poly1305.X86_64.Avx2.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx2.EnvOK s₀ B) {t : VG.Proof.Poly1305.X86_64.Avx2.Q} {k : Nat} (hk : k < 4) {b : Nat}
    (hb : (t.eval s₀ k).toNat ≤ b) : (t.eval s₀ k).toNat % 2 ^ 32 ≤ VG.Proof.Poly1305.X86_64.Avx2.loB B t b := by
  unfold VG.Proof.Poly1305.X86_64.Avx2.loB
  split
  · rename_i r
    have := hE.lo (VG.Proof.Poly1305.X86_64.Avx2.xr r) k hk
    have h₁ := Nat.mod_le (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ (VG.Proof.Poly1305.X86_64.Avx2.xr r) k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ (VG.Proof.Poly1305.X86_64.Avx2.xr r) k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [Q.eval] at hb ⊢
    omega
  · have h₁ := Nat.mod_le (t.eval s₀ k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (t.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    omega

theorem nat_ok {s₀ : State} {B : VG.Proof.Poly1305.X86_64.Avx2.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx2.EnvOK s₀ B) :
    ∀ (t : VG.Proof.Poly1305.X86_64.Avx2.Q) {k : Nat}, k < 4 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.v (VG.Proof.Poly1305.X86_64.Avx2.xr r) k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ih (by decide) ho
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld i =>
    intro k _ _
    refine ⟨?_, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩
    simp only [Q.eval, Q.nat, VG.Proof.Poly1305.X86_64.Avx2.envOf, Nat.mul_add]
  | add a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    exact ⟨Nat.mod_eq_of_lt (by omega), VG.Proof.Poly1305.X86_64.Avx2.capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | mul a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have la := VG.Proof.Poly1305.X86_64.Avx2.loB_ge hE hk ba
    have lb := VG.Proof.Poly1305.X86_64.Avx2.loB_ge hE hk bb
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_mul, VG.Proof.Poly1305.X86_64.Avx2.lo32_toNat]
    rw [← ea, ← eb]
    have p₁ := Nat.mod_lt (a.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have hp : (a.eval s₀ k).toNat % 2 ^ 32 * ((b.eval s₀ k).toNat % 2 ^ 32) < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt hp]
    exact ⟨rfl, Nat.mul_le_mul la lb⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩⟩
  | andn a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, _⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and, BitVec.toNat_not]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_trans Nat.and_le_right bb⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, VG.Proof.Poly1305.X86_64.Avx2.orB_ge ba bb this⟩
  | shl a n ih =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), VG.Proof.Poly1305.X86_64.Avx2.capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba⟩ := ih hk ho
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha hk ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (by omega) ho
  | unph a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (by omega) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb hk ho
  | perm a o ih =>
    intro k _ ho
    exact ih (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) ho
  | blend a b sel iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, _⟩ := iha hk ho.1
    obtain ⟨eb, _⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd]
    rw [← ea, ← eb, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]
    exact ⟨rfl, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩

theorem natw_ok (s₀ : State) : ∀ (t : VG.Proof.Poly1305.X86_64.Avx2.Q) (k : Nat), (t.eval s₀ k).toNat = t.natw (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k := by
  intro t
  induction t with
  | reg r => intro k; rfl
  | gpr g => intro k; rfl
  | lane0 a ih =>
    intro k
    simp only [Q.eval, Q.natw]
    split
    · exact ih 0
    · rfl
  | bc a ih => intro k; exact ih 0
  | ld i => intro k; simp only [Q.eval, Q.natw, VG.Proof.Poly1305.X86_64.Avx2.envOf, Nat.mul_add]
  | add a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_add, iha, ihb]
  | mul a b iha ihb =>
    intro k
    simp only [Q.eval, Q.natw, BitVec.toNat_mul, VG.Proof.Poly1305.X86_64.Avx2.lo32_toNat, iha, ihb]
    have p₁ := Nat.mod_lt (a.natw (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.natw (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide))
  | and a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, iha, ihb]
  | andn a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, BitVec.toNat_not, iha, ihb]
  | or a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_or, iha, ihb]
  | shl a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ih]
  | shr a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ih]
  | unpl a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha k
    · exact ihb _
  | unph a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb k
  | perm a o ih => intro k; exact ih _
  | blend a b sel iha ihb =>
    intro k
    simp only [Q.eval, Q.natw]
    rw [← iha, ← ihb, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem SRel.nat {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) {B : VG.Proof.Poly1305.X86_64.Avx2.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx2.EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 4) (ho : (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi r)).ok B k = true) :
    (VG.Proof.Poly1305.X86_64.Avx2.qw s r k).toNat = (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi r)).nat (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k ∧ (VG.Proof.Poly1305.X86_64.Avx2.qw s r k).toNat ≤ (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi r)).bnd B k := by
  rw [h.reg r k hk]; exact VG.Proof.Poly1305.X86_64.Avx2.nat_ok hE _ hk ho

theorem SRel.natw {σ : VG.Proof.Poly1305.X86_64.Avx2.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.SRel σ s₀ s) (r : XReg) {k : Nat} (hk : k < 4) :
    (VG.Proof.Poly1305.X86_64.Avx2.qw s r k).toNat = (σ.reg (VG.Proof.Poly1305.X86_64.Avx2.xi r)).natw (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀) k := by
  rw [h.reg r k hk]; exact VG.Proof.Poly1305.X86_64.Avx2.natw_ok s₀ _ k

theorem envOf_v (s₀ : State) (r : XReg) (k : Nat) : (VG.Proof.Poly1305.X86_64.Avx2.envOf s₀).v (VG.Proof.Poly1305.X86_64.Avx2.xi r) k = (VG.Proof.Poly1305.X86_64.Avx2.qw s₀ r k).toNat := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.envOf, VG.Proof.Poly1305.X86_64.Avx2.xr_xi]

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Mul`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: the product

`mul` multiplies the four lanes of the accumulator `H` by the low doublewords
of `Y`, lane by lane, and carries: `Limbs26.mul`, with the limbs small enough
that nothing wraps.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2

/-- Limb `i` of lane `k` of `H`, and of the low doublewords of `Y`. -/
def hv (s : State) (k i : Nat) : Nat := (VG.Proof.Poly1305.X86_64.Avx2.qw s (hreg i) k).toNat
def yl (s : State) (k i : Nat) : Nat := (VG.Proof.Poly1305.X86_64.Avx2.qw s (yreg i) k).toNat % 2 ^ 32

def mulB : VG.Proof.Poly1305.X86_64.Avx2.Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 28 - 1
    | _ => 2 ^ 64 - 1,
   fun r => match r with
    | .xmm11 | .xmm12 | .xmm13 | .xmm14 | .xmm15 => 2 ^ 27 - 1
    | _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1⟩

def mulS : VG.Proof.Poly1305.X86_64.Avx2.Sym := (Sym.init.run false mul).get (by decide +kernel)

theorem mulS_eq : Sym.init.run false mul = some VG.Proof.Poly1305.X86_64.Avx2.mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 5, ∀ k < 4,
    (mulS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx2.mulB k = true ∧ (mulS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg i))).bnd VG.Proof.Poly1305.X86_64.Avx2.mulB k < 2 ^ 27 := by
  decide +kernel

theorem mulS_y : ∀ i < 5, mulS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) = .reg (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) := by decide +kernel

/-- The limbs `mul` computes, from the registers it starts with. -/
theorem mulS_nat (E : VG.Proof.Poly1305.X86_64.Avx2.Env) (k : Nat) : ∀ i < 5, (mulS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg i))).nat E k =
    Limbs26.carry (Limbs26.pd (fun i => E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg i)) k % 2 ^ 32)
      (fun i => E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) k % 2 ^ 32)) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

structure MulPre (s : State) : Prop where
  r8 : s.gpr .r8 = 0x3ffffff
  h : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.hv s k i < 2 ^ 28
  y : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.yl s k i < 2 ^ 27

theorem MulPre.env {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.MulPre s) : VG.Proof.Poly1305.X86_64.Avx2.EnvOK s VG.Proof.Poly1305.X86_64.Avx2.mulB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (VG.Proof.Poly1305.X86_64.Avx2.qw s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (VG.Proof.Poly1305.X86_64.Avx2.qw s r k).toNat (show 2 ^ 32 > 0 by decide)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.y k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 4 (by decide))
  · have := BitVec.isLt (s.gpr g)
    simp only [VG.Proof.Poly1305.X86_64.Avx2.mulB]
    split
    · subst g; rw [hp.r8]; decide
    · omega

/-- What `mul` leaves: `H` times the low doublewords of `Y`, carried, and the
rest but the products and `tP` as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : VG.Proof.Poly1305.X86_64.Avx2.vec s s' = s'
  y : ∀ i < 5, ∀ k < 4, VG.Proof.Poly1305.X86_64.Avx2.qw s' (yreg i) k = VG.Proof.Poly1305.X86_64.Avx2.qw s (yreg i) k
  h : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.hv s' k i = Limbs26.mul (VG.Proof.Poly1305.X86_64.Avx2.hv s k) (VG.Proof.Poly1305.X86_64.Avx2.yl s k) i
  hb : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.hv s' k i < 2 ^ 27

theorem hreg_ge : ∀ {j : Nat}, 4 ≤ j → hreg j = hreg 4
  | _ + 4, _ => rfl

theorem yreg_ge : ∀ {j : Nat}, 4 ≤ j → yreg j = yreg 4
  | _ + 4, _ => rfl

theorem hv_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx2.hv s k j = VG.Proof.Poly1305.X86_64.Avx2.hv s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.hv, VG.Proof.Poly1305.X86_64.Avx2.hreg_ge h]

theorem yl_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx2.yl s k j = VG.Proof.Poly1305.X86_64.Avx2.yl s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.yl, VG.Proof.Poly1305.X86_64.Avx2.yreg_ge h]

theorem hv_mod {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.MulPre s) {k : Nat} (hk : k < 4) :
    (fun i => (VG.Proof.Poly1305.X86_64.Avx2.envOf s).v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg i)) k % 2 ^ 32) = VG.Proof.Poly1305.X86_64.Avx2.hv s k := by
  funext i
  rw [VG.Proof.Poly1305.X86_64.Avx2.envOf_v]
  by_cases hi : i < 5
  · exact Nat.mod_eq_of_lt (Nat.lt_trans (hp.h k hk i hi) (by decide))
  · rw [VG.Proof.Poly1305.X86_64.Avx2.hreg_ge (by omega)]
    rw [VG.Proof.Poly1305.X86_64.Avx2.hv_ge s k (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (hp.h k hk 4 (by decide)) (by decide))

theorem yl_eq (s : State) (k : Nat) : (fun i => (VG.Proof.Poly1305.X86_64.Avx2.envOf s).v (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) k % 2 ^ 32) = VG.Proof.Poly1305.X86_64.Avx2.yl s k := by
  funext i; rw [VG.Proof.Poly1305.X86_64.Avx2.envOf_v]; rfl

theorem mul_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.MulPre s) : WP isa (.block mul) s (VG.Proof.Poly1305.X86_64.Avx2.MulPost s) := by
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx2.mulS_y i hi]; simp only [Q.eval, VG.Proof.Poly1305.X86_64.Avx2.xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx2.mulS_ok i hi k hk).1
    simp only [VG.Proof.Poly1305.X86_64.Avx2.hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx2.mulS_nat _ _ i hi, Limbs26.mul, VG.Proof.Poly1305.X86_64.Avx2.hv_mod hp hk, VG.Proof.Poly1305.X86_64.Avx2.yl_eq]
    simp only [VG.Proof.Poly1305.X86_64.Avx2.envOf, hp.r8]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx2.mulS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (VG.Proof.Poly1305.X86_64.Avx2.mulS_ok i hi k hk).2

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: loading blocks, `r` and the accumulator

`addGroup` splits the four blocks at `rsi` into limbs (block `k` in lane `k`)
and adds them, with the pad bit, to `H`; `loadR` and `loadH` split `r` and the
accumulator the same way.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2

def addS : VG.Proof.Poly1305.X86_64.Avx2.Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some VG.Proof.Poly1305.X86_64.Avx2.addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 5, addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) = .reg (VG.Proof.Poly1305.X86_64.Avx2.xi (yreg i)) := by decide +kernel

section
variable (E : VG.Proof.Poly1305.X86_64.Avx2.Env)

theorem addS_0 : ∀ k < 4, (addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 0))).natw E k =
    (E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 0)) k + E.m (2 * k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 4, (addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 1))).natw E k =
    (E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 1)) k + E.m (2 * k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 4, (addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 2))).natw E k =
    (E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 2)) k + (E.m (2 * k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_3 : ∀ k < 4, (addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 3))).natw E k =
    (E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 3)) k + E.m (2 * k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_4 : ∀ k < 4, (addS.reg (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 4))).natw E k =
    (E.v (VG.Proof.Poly1305.X86_64.Avx2.xi (hreg 4)) k + (E.m (2 * k + 1) / 2 ^ 40 ||| E.g .r9)) % 2 ^ 64 := by
  intro k hk; rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

end

/-- The words of block `k` of the group at `rsi`. -/
def blo (s : State) (k : Nat) : Nat := (VG.Proof.Poly1305.X86_64.Avx2.envOf s).m (2 * k)
def bhi (s : State) (k : Nat) : Nat := (VG.Proof.Poly1305.X86_64.Avx2.envOf s).m (2 * k + 1)

theorem envOf_m_lt (s : State) (j : Nat) : (VG.Proof.Poly1305.X86_64.Avx2.envOf s).m j < 2 ^ 64 := BitVec.isLt _

theorem or_pad {x : Nat} (hx : x < 2 ^ 24) : (x ||| 0x1000000) = x + 2 ^ 24 := by
  rw [Nat.or_comm, show (0x1000000 : Nat) = 2 ^ 24 * 1 by decide, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

structure AddPre (s : State) : Prop where
  r9 : s.gpr .r9 = 0x1000000
  ctx : VG.Proof.Poly1305.X86_64.Avx2.Ctx s
  h : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.hv s k i < 2 ^ 27

/-- What `addGroup` leaves: block `k`, with its pad bit, added to lane `k`
of `H`, and `Y` as it was. -/
structure AddPost (s s' : State) : Prop where
  vec : VG.Proof.Poly1305.X86_64.Avx2.vec s s' = s'
  y : ∀ i < 5, ∀ k < 4, VG.Proof.Poly1305.X86_64.Avx2.qw s' (yreg i) k = VG.Proof.Poly1305.X86_64.Avx2.qw s (yreg i) k
  h : ∀ k < 4, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx2.hv s' k) = Limbs26.val (VG.Proof.Poly1305.X86_64.Avx2.hv s k) + (VG.Proof.Poly1305.X86_64.Avx2.blo s k + 2 ^ 64 * VG.Proof.Poly1305.X86_64.Avx2.bhi s k + 2 ^ 128)
  hb : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.hv s' k i < 2 ^ 28

theorem addGroup_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.AddPre s) : WP isa (.block addGroup) s (VG.Proof.Poly1305.X86_64.Avx2.AddPost s) := by
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.run_ok (fun _ => hp.ctx) VG.Proof.Poly1305.X86_64.Avx2.addS_eq) fun s' h => ?_
  have H : ∀ k < 4, VG.Proof.Poly1305.X86_64.Avx2.hv s' k 0 = VG.Proof.Poly1305.X86_64.Avx2.hv s k 0 + VG.Proof.Poly1305.X86_64.Avx2.blo s k * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx2.hv s' k 1 = VG.Proof.Poly1305.X86_64.Avx2.hv s k 1 + VG.Proof.Poly1305.X86_64.Avx2.blo s k * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx2.hv s' k 2 = VG.Proof.Poly1305.X86_64.Avx2.hv s k 2 + (2 ^ 12 * (VG.Proof.Poly1305.X86_64.Avx2.bhi s k % 2 ^ 14) + VG.Proof.Poly1305.X86_64.Avx2.blo s k / 2 ^ 52) ∧
      VG.Proof.Poly1305.X86_64.Avx2.hv s' k 3 = VG.Proof.Poly1305.X86_64.Avx2.hv s k 3 + VG.Proof.Poly1305.X86_64.Avx2.bhi s k * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx2.hv s' k 4 = VG.Proof.Poly1305.X86_64.Avx2.hv s k 4 + (VG.Proof.Poly1305.X86_64.Avx2.bhi s k / 2 ^ 40 + 2 ^ 24) := by
    intro k hk
    have hl := VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k)
    have hh := VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k + 1)
    have b0 := hp.h k hk 0 (by decide)
    have b1 := hp.h k hk 1 (by decide)
    have b2 := hp.h k hk 2 (by decide)
    have b3 := hp.h k hk 3 (by decide)
    have b4 := hp.h k hk 4 (by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx2.hv] at b0 b1 b2 b3 b4 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.addS_0 _ k hk, VG.Proof.Poly1305.X86_64.Avx2.addS_1 _ k hk,
      VG.Proof.Poly1305.X86_64.Avx2.addS_2 _ k hk, VG.Proof.Poly1305.X86_64.Avx2.addS_3 _ k hk, VG.Proof.Poly1305.X86_64.Avx2.addS_4 _ k hk, VG.Proof.Poly1305.X86_64.Avx2.envOf_v, VG.Proof.Poly1305.X86_64.Avx2.envOf_v, VG.Proof.Poly1305.X86_64.Avx2.envOf_v, VG.Proof.Poly1305.X86_64.Avx2.envOf_v, VG.Proof.Poly1305.X86_64.Avx2.envOf_v,
      Limbs26.split_or hl]
    have r9 : (s.gpr .r9).toNat = 0x1000000 := by rw [hp.r9]; rfl
    simp only [VG.Proof.Poly1305.X86_64.Avx2.envOf, r9, VG.Proof.Poly1305.X86_64.Avx2.blo, VG.Proof.Poly1305.X86_64.Avx2.bhi] at hl hh ⊢
    rw [VG.Proof.Poly1305.X86_64.Avx2.or_pad (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx2.addS_y i hi]; simp only [Q.eval, VG.Proof.Poly1305.X86_64.Avx2.xr_xi]
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have := Limbs26.split_val (VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k)) (VG.Proof.Poly1305.X86_64.Avx2.bhi s k)
    rw [Limbs26.split_or (VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k))] at this
    simp only [Limbs26.val, e0, e1, e2, e3, e4]
    simp only [VG.Proof.Poly1305.X86_64.Avx2.blo] at this ⊢
    omega
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have hl := VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k)
    have hh := VG.Proof.Poly1305.X86_64.Avx2.envOf_m_lt s (2 * k + 1)
    have b := hp.h k hk
    simp only [VG.Proof.Poly1305.X86_64.Avx2.blo, VG.Proof.Poly1305.X86_64.Avx2.bhi] at e0 e1 e2 e3 e4
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega
    · rw [e1]; have := b 1 (by decide); omega
    · rw [e2]; have := b 2 (by decide); omega
    · rw [e3]; have := b 3 (by decide); omega
    · rw [e4]; have := b 4 (by decide); omega

end VG.Proof.Poly1305.X86_64.Avx2

end
