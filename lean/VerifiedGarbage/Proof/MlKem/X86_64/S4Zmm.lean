module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Wide
public import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on x86-64: `vg_mlkem16_sample_ntt4_avx512`, thirty-two candidates at once

The AVX-512 step of the sampling (`Sample4.zcand`, `Sample4.zputL`) on the 48
bytes at `rsi`: of the 64 bytes it loads, `vpermw` puts bytes `12 l` to
`12 l + 11` at the bottom of lane `l` (`perm_byte`); `vpshufb`, `vpsrlvw` and
`vpandq` make candidate `8 l + i` of `SampleNTT` word `i` of lane `l`
(`zcand_word`); `vpcmpltuw` gives the mask of the candidates less than `q`,
lane `l`'s in byte `l` (`zmask_toNat`); the static's mask of each byte moves
its lane's candidates to the bottom of the lane, as `vputA` does
(`pshufb_idxV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (idxV idxQ setBits)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

/-! ## The constants -/

/-- Index `j` of `vpermw`: words `6 l` to `6 l + 5` to words 0 to 5 of lane `l`. -/
def permI (j : Nat) : Nat := if j % 8 < 6 then 6 * (j / 8) + j % 8 else 0

/-- Lane `l` of the indices of `vpermw` (`zmm12`). -/
def permL (l : Nat) : BitVec 128 := ofWords fun i => BitVec.ofNat 16 (permI (8 * l + i))

/-- The counts of `vpsrlvw` (`zmm13`): 0 in the even words and 4 in the odd ones. -/
def cntW : BitVec 128 := 0x00040000000400000004000000040000#128

/-- The constants of the AVX-512 code in `zmm9` to `zmm13`, and those of the
AVX2 code. -/
structure ZC (s : State) : Prop where
  vc : VC s
  c9 : ∀ l < 4, s.zlane .xmm9 l = fffW
  c10 : ∀ l < 4, s.zlane .xmm10 l = qW
  c11 : ∀ l < 4, s.zlane .xmm11 l = shufW 0
  c12 : ∀ l < 4, s.zlane .xmm12 l = permL l
  c13 : ∀ l < 4, s.zlane .xmm13 l = cntW

theorem permI_lt {j : Nat} (hj : j < 32) : permI j < 32 := by
  unfold permI; split <;> omega_arith

theorem zword_permL {s : State} (hc : ∀ l < 4, s.zlane .xmm12 l = permL l) {j : Nat} (hj : j < 32) :
    (s.zword .xmm12 j).toNat % 32 = permI j := by
  have h1 : permI j < 32 := permI_lt hj
  rw [State.zword, hc _ (by omega_arith), permL, word_ofWords _ (Nat.mod_lt _ (by decide)), BitVec.toNat_ofNat,
    show 8 * (j / 8) + j % 8 = j by omega_arith, Nat.mod_eq_of_lt (show permI j < 2 ^ 16 by omega_arith),
    Nat.mod_eq_of_lt h1]

theorem word_cntW {i : Nat} (hi : i < 8) : word cntW i = if i % 2 = 1 then 4#16 else 0#16 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem word_fffW {i : Nat} (hi : i < 8) : word fffW i = 0xfff#16 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem word_qW {i : Nat} (hi : i < 8) : word qW i = 0x0d01#16 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The candidates -/

/-- Byte `k` of a 512-bit value. -/
abbrev byteZ (X : BitVec 512) (k : Nat) : BitVec 8 := X.extractLsb' (8 * k) 8

/-- Word `j` of a 512-bit value. -/
abbrev wordZ (X : BitVec 512) (j : Nat) : BitVec 16 := X.extractLsb' (16 * j) 16

/-- Lane `l` after `vpermw`: words `6 l` to `6 l + 5`, then word 0 twice. -/
def zpermL (X : BitVec 512) (l : Nat) : BitVec 128 := ofWords fun k => wordZ X (permI (8 * l + k))

theorem byte_ofWords (f : Nat → BitVec 16) {m : Nat} (hm : m < 16) :
    byte (ofWords f) m = (f (m / 2)).extractLsb' (8 * (m % 2)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  rw [show 8 * m + r = 16 * (m / 2) + (8 * (m % 2) + r) by omega_arith,
    getLsbD_ofWords _ (by omega_arith) (by omega_arith)]

/-- Byte `m < 12` of lane `l` after `vpermw` is byte `12 l + m` of the 48. -/
theorem perm_byte (X : BitVec 512) {l m : Nat} (hm : m < 12) :
    byte (zpermL X l) m = byteZ X (12 * l + m) := by
  rw [zpermL, byte_ofWords _ (by omega_arith), permI, itT (show (8 * l + m / 2) % 8 < 6 by omega_arith),
    show 6 * ((8 * l + m / 2) / 8) + (8 * l + m / 2) % 8 = 6 * l + m / 2 by omega_arith]
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
    show 8 * (m % 2) + r < 16 by omega_arith, decide_true]
  congr 1; omega_arith

/-- Lane `l` after `vpshufb`, `vpsrlvw` and `vpandq`. -/
def zcandP (X : BitVec 512) (l : Nat) : BitVec 128 :=
  let P := XBinOp.eval .pshufb (zpermL X l) (shufW 0)
  XBinOp.eval .pand (ofWords fun k => let c := (word cntW k).toNat; if c < 16 then word P k >>> c else 0) fffW

/-- Lane `l` of the candidates: word `i` is candidate `8 l + i`. -/
def zcandW (X : BitVec 512) (l : Nat) : BitVec 128 :=
  ofWords fun i => BitVec.ofNat 16 (candN (fun k => (byteZ X k).toNat) (8 * l + i))

theorem zcand_word (X : BitVec 512) {l i : Nat} (hi : i < 8) :
    (word (zcandP X l) i).toNat = candN (fun k => (byteZ X k).toNat) (8 * l + i) := by
  have hb : ∀ k, (byteZ X k).toNat < 256 := fun k => (byteZ X k).isLt
  have hcb : cb (8 * l + i) = 12 * l + cb i := by simp only [cb]; omega_arith
  have hP : (word (XBinOp.eval .pshufb (zpermL X l) (shufW 0)) i).toNat =
      (byteZ X (cb (8 * l + i))).toNat + 256 * (byteZ X (cb (8 * l + i) + 1)).toNat := by
    have e0 : cb (2 * i / 2) + 4 * 0 + 2 * i % 2 = cb i := by simp only [cb]; omega_arith
    have e1 : cb ((2 * i + 1) / 2) + 4 * 0 + (2 * i + 1) % 2 = cb i + 1 := by simp only [cb]; omega_arith
    rw [pshufb_shufW _ (by decide), toNat_word_ofBytes _ hi, e0, e1,
      perm_byte X (by simp only [cb]; omega_arith), perm_byte X (by simp only [cb]; omega_arith), hcb,
      show 12 * l + (cb i + 1) = 12 * l + cb i + 1 from (Nat.add_assoc _ _ _).symm]
  simp only [zcandP]
  rw [word_pand, BitVec.toNat_and, word_fffW hi, show (0xfff#16).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, word_ofWords _ hi, word_cntW hi]
  have b0 := hb (cb (8 * l + i)); have b1 := hb (cb (8 * l + i) + 1)
  by_cases h : i % 2 = 1
  · rw [itT h, show (4#16).toNat = 4 from rfl, itT (show 4 < 16 by decide), BitVec.toNat_ushiftRight, hP,
      Nat.shiftRight_eq_div_pow, candN, itF (show ¬ (8 * l + i) % 2 = 0 by omega_arith)]
    omega_arith
  · rw [itF h, show (0#16).toNat = 0 from rfl, itT (show 0 < 16 by decide), BitVec.toNat_ushiftRight, hP,
      Nat.shiftRight_eq_div_pow, candN, itT (show (8 * l + i) % 2 = 0 by omega_arith)]
    omega_arith

theorem candZ_lt (X : BitVec 512) (k : Nat) : candN (fun k => (byteZ X k).toNat) k < 4096 :=
  candN_lt _ (fun i => (byteZ X i).isLt) k

theorem zcandP_eq (X : BitVec 512) (l : Nat) : zcandP X l = zcandW X l :=
  ext_word fun i hi => BitVec.eq_of_toNat_eq (by
    rw [zcand_word X hi, zcandW, word_ofWords _ hi, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := candZ_lt X (8 * l + i); omega_arith)])

theorem zcandW_word (X : BitVec 512) {l i : Nat} (hi : i < 8) :
    (word (zcandW X l) i).toNat = candN (fun k => (byteZ X k).toNat) (8 * l + i) := by
  rw [zcandW, word_ofWords _ hi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := candZ_lt X (8 * l + i); omega_arith)]

/-! ## The mask -/

/-- The mask of the candidates less than `q` of lane `l`. -/
def zmaskL (X : BitVec 512) (l : Nat) : Nat :=
  bsum (fun i => decide (candN (fun k => (byteZ X k).toNat) (8 * l + i) < 3329)) 8

theorem zmaskL_lt (X : BitVec 512) (l : Nat) : zmaskL X l < 256 := bsum_lt _ 8

/-- The fold of `cmpltuMask` is `bsum`. -/
theorem foldl_bsum {f : Nat → Prop} [DecidablePred f] (p : Nat → Bool) :
    ∀ n, (∀ j < n, f j ↔ p j = true) →
      (List.range n).foldl (fun acc j => if f j then acc + 2 ^ j else acc) 0 = bsum p n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_bsum p n (fun j hj => h j (by omega_arith)), List.foldl_cons,
      List.foldl_nil, bsum]
    by_cases hp : p n = true
    · rw [itT ((h n (by omega_arith)).mpr hp), hp]; simp
    · rw [itF (fun e => hp ((h n (by omega_arith)).mp e)), Bool.eq_false_iff.mpr hp]; simp

/-- The mask, lane `l`'s in byte `l`. -/
theorem zmask_bsum (X : BitVec 512) :
    bsum (fun j => decide (candN (fun k => (byteZ X k).toNat) j < 3329)) 32 =
      zmaskL X 0 + 256 * zmaskL X 1 + 65536 * zmaskL X 2 + 16777216 * zmaskL X 3 := by
  generalize hg : (fun j => decide (candN (fun k => (byteZ X k).toNat) j < 3329)) = g
  have B : ∀ l, bsum (fun i => g (8 * l + i)) 8 = zmaskL X l := fun l => by rw [← hg]; rfl
  have b0 : bsum g 8 = zmaskL X 0 := by
    rw [← B 0]; exact bsum_congr fun i _ => by rw [Nat.mul_zero, Nat.zero_add]
  rw [show (32 : Nat) = 24 + 8 from rfl, bsum_chunk, show (24 : Nat) = 16 + 8 from rfl, bsum_chunk,
    show (16 : Nat) = 8 + 8 from rfl, bsum_chunk, b0, ← B 1, ← B 2, ← B 3]

/-! ## The instructions, lane by lane -/

/-- `s'` is `s` with the four lanes of `d` set to `v 0` to `v 3`. -/
structure ZUpd (s s' : State) (d : XReg) (v : Nat → BitVec 128) : Prop where
  val : ∀ l < 4, s'.zlane d l = v l
  other : ∀ r, r ≠ d → ∀ l < 4, s'.zlane r l = s.zlane r l
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem ZUpd.setZ (s : State) (d : XReg) (f : Nat → BitVec 128) :
    ZUpd s (s.setZ d (f 0) (f 1) (f 2) (f 3)) d f :=
  ⟨fun l hl => by rw [State.zlane_setZ _ _ _ _ _ _ _ hl, ite_eq_left rfl, pick4_lanes f hl],
    fun r hr l hl => by rw [State.zlane_setZ _ _ _ _ _ _ _ hl, ite_eq_right hr],
    State.setZ_gpr .., State.setZ_mem .., State.setZ_rd .., State.setZ_wr .., rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_zld {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 64)
    (k : ∀ s', ZUpd s s' d (fun l => (s.mem.readW a 512).extractLsb' (128 * l) 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdqu32Load d m :: is)) s Q :=
  WP.cons (s' := s.setZ d ((s.mem.readW a 512).extractLsb' (128 * 0) 128) ((s.mem.readW a 512).extractLsb' (128 * 1) 128)
    ((s.mem.readW a 512).extractLsb' (128 * 2) 128) ((s.mem.readW a 512).extractLsb' (128 * 3) 128))
    (by simp [exec, ha, State.load512, hin])
    (k _ (ZUpd.setZ s d (fun l => (s.mem.readW a 512).extractLsb' (128 * l) 128)))

theorem wp_zpermw {d a b : XReg}
    (k : ∀ s', ZUpd s s' d (fun l => ofWords fun j => s.permWord a b (8 * l + j)) → WP isa (.block is) s' Q) :
    WP isa (.block (.zop (.vpermw d a b) :: is)) s Q :=
  WP.cons rfl (k _ (ZUpd.setZ s d (fun l => ofWords fun j => s.permWord a b (8 * l + j))))

theorem wp_zsrlvw {d a b : XReg}
    (k : ∀ s', ZUpd s s' d (fun l => ofWords fun j => s.srlvWord a b (8 * l + j)) → WP isa (.block is) s' Q) :
    WP isa (.block (.zop (.vpsrlvw d a b) :: is)) s Q :=
  WP.cons rfl (k _ (ZUpd.setZ s d (fun l => ofWords fun j => s.srlvWord a b (8 * l + j))))

theorem wp_zbin {op : ZBinOp} {d a b : XReg}
    (k : ∀ s', ZUpd s s' d (fun l => op.sse.eval (s.zlane a l) (s.zlane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.zop (.zbin op d a b) :: is)) s Q :=
  WP.cons rfl (k _ (ZUpd.setZ s d (fun l => op.sse.eval (s.zlane a l) (s.zlane b l))))

theorem wp_zshuf {d a b : XReg} {n : BitVec 8}
    (k : ∀ s', ZUpd s s' d (shuf4Lanes (s.zlane a) (s.zlane b) n) → WP isa (.block is) s' Q) :
    WP isa (.block (.zop (.vshufi32x4 d a b n) :: is)) s Q :=
  WP.cons rfl (k _ (ZUpd.setZ s d (shuf4Lanes (s.zlane a) (s.zlane b) n)))

theorem wp_zext {d r : XReg} {n : BitVec 8}
    (k : ∀ s', ZUpd s s' d (fun l => if l = 0 then s.zlane r (n.toNat % 4) else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.zop (.vextracti32x4 d r n) :: is)) s Q :=
  WP.cons rfl (k _ (ZUpd.setZ s d (fun l => if l = 0 then s.zlane r (n.toNat % 4) else 0)))

/-- `vpcmpltuw`: the mask to `d`, zero-extended. -/
theorem wp_zcmplt {d : Reg} {a b : XReg}
    (k : ∀ s', s'.gpr d = (cmpltuMask s a b).setWidth 64 → (∀ r, r ≠ d → s'.gpr r = s.gpr r) →
      (∀ r l, s'.zlane r l = s.zlane r l) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vpcmpltuw d a b :: is)) s Q :=
  WP.cons (s' := s.setReg32 d (cmpltuMask s a b)) rfl
    (k _ (by simp [State.setReg32, State.setReg]) (fun r hr => by simp [State.setReg32, State.setReg, hr])
      (fun _ _ => rfl) rfl rfl rfl rfl)

end

/-- `VC` of a state whose lanes of `zmm8` to `zmm10` are those of `s`. -/
theorem VC.zsame {s s' : State} (h : VC s) (hl : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10], ∀ l < 2, s'.zlane r l = s.zlane r l) :
    VC s' :=
  ⟨fun l hl' => by rw [← s'.zlane_lt2 _ hl', hl _ (by simp) l hl', s.zlane_lt2 _ hl']; exact h.c8 l hl',
   fun l hl' => by rw [← s'.zlane_lt2 _ hl', hl _ (by simp) l hl', s.zlane_lt2 _ hl']; exact h.c9 l hl',
   fun l hl' => by rw [← s'.zlane_lt2 _ hl', hl _ (by simp) l hl', s.zlane_lt2 _ hl']; exact h.c10 l hl'⟩

/-- `ZC` of a state whose lanes of `zmm8` to `zmm13` are those of `s`. -/
theorem ZC.same {s s' : State} (h : ZC s)
    (hl : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13], ∀ l < 4, s'.zlane r l = s.zlane r l) : ZC s' :=
  ⟨h.vc.zsame fun r hr l hl' => hl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp) l
      (by omega_arith),
    fun l h' => by rw [hl _ (by simp) l h']; exact h.c9 l h', fun l h' => by rw [hl _ (by simp) l h']; exact h.c10 l h',
    fun l h' => by rw [hl _ (by simp) l h']; exact h.c11 l h', fun l h' => by rw [hl _ (by simp) l h']; exact h.c12 l h',
    fun l h' => by rw [hl _ (by simp) l h']; exact h.c13 l h'⟩

/-- `ZC` after an update of a register other than `zmm8` to `zmm13`. -/
theorem ZC.zupd {s s' : State} (h : ZC s) {d : XReg} {v : Nat → BitVec 128} (hu : ZUpd s s' d v)
    (hd : d ∉ [XReg.xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13] := by decide) : ZC s' :=
  h.same fun r hr l hl => hu.other r (fun e => hd (e ▸ hr)) l hl

theorem zlane_load (X : BitVec 512) (j : Nat) :
    word (X.extractLsb' (128 * (j / 8)) 128) (j % 8) = wordZ X j := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [word, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
    show 16 * (j % 8) + r < 128 by omega_arith, decide_true]
  congr 1; omega_arith

/-- The 32 candidates of the 48 bytes at `rsi`, in the lanes of `zmm0`, and their mask in `eax`. -/
theorem zcand_ok {s : State} (hc : ZC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 64) :
    WP isa (.block Impl.MlKem.X86_64.Sample4.zcand) s fun s' =>
      (s'.gpr .rax).toNat = zmaskL (s.mem.readW (s.gpr .rsi) 512) 0 + 256 * zmaskL (s.mem.readW (s.gpr .rsi) 512) 1 +
        65536 * zmaskL (s.mem.readW (s.gpr .rsi) 512) 2 + 16777216 * zmaskL (s.mem.readW (s.gpr .rsi) 512) 3 ∧
      (∀ l < 4, s'.zlane .xmm0 l = zcandW (s.mem.readW (s.gpr .rsi) 512) l) ∧ ZC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  generalize hX : s.mem.readW (s.gpr .rsi) 512 = X
  refine wp_zld (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 =>
    wp_zpermw fun s2 u2 => wp_zbin fun s3 u3 => wp_zsrlvw fun s4 u4 => wp_zbin fun s5 u5 =>
    wp_zcmplt fun s6 r6 g6 z6 m6 rd6 wr6 y6 => WP.block_nil ?_
  have c1 := hc.zupd u1
  have c2 := c1.zupd u2
  have c3 := c2.zupd u3
  have c4 := c3.zupd u4
  have c5 := c4.zupd u5
  have w1 : ∀ j < 32, s1.zword .xmm0 j = wordZ X j := fun j hj => by
    rw [State.zword, u1.val _ (by omega_arith), hX, zlane_load X j]
  have l2 : ∀ l < 4, s2.zlane .xmm0 l = zpermL X l := fun l hl => by
    rw [u2.val l hl, zpermL]
    exact ext_word fun k hk => by
      rw [word_ofWords _ hk, word_ofWords _ hk, State.permWord, zword_permL c1.c12 (by omega_arith),
        w1 _ (permI_lt (by omega_arith))]
  have l3 : ∀ l < 4, s3.zlane .xmm0 l = XBinOp.eval .pshufb (zpermL X l) (shufW 0) := fun l hl => by
    rw [u3.val l hl, l2 l hl, c2.c11 l hl]; rfl
  have l4 : ∀ l < 4, s4.zlane .xmm0 l = ofWords fun k => let c := (word cntW k).toNat
      if c < 16 then word (XBinOp.eval .pshufb (zpermL X l) (shufW 0)) k >>> c else 0 := fun l hl => by
    rw [u4.val l hl]
    exact ext_word fun k hk => by
      rw [word_ofWords _ hk, word_ofWords _ hk, State.srlvWord, State.zword, State.zword,
        show (8 * l + k) / 8 = l by omega_arith, show (8 * l + k) % 8 = k by omega_arith, l3 l hl, c3.c13 l hl]
  have l5 : ∀ l < 4, s5.zlane .xmm0 l = zcandW X l := fun l hl => by
    rw [u5.val l hl, l4 l hl, c4.c9 l hl, ← zcandP_eq X l]; rfl
  have hw : ∀ j < 32, (s5.zword .xmm0 j).toNat < (s5.zword .xmm10 j).toNat ↔
      candN (fun k => (byteZ X k).toNat) j < 3329 := fun j hj => by
    rw [State.zword, State.zword, l5 _ (by omega_arith), c5.c10 _ (by omega_arith), word_qW (Nat.mod_lt _ (by decide)),
      zcandW_word X (Nat.mod_lt _ (by decide)), show 8 * (j / 8) + j % 8 = j by omega_arith]
    rfl
  have hm : (cmpltuMask s5 .xmm0 .xmm10).toNat = bsum (fun j => decide (candN (fun k => (byteZ X k).toNat) j < 3329)) 32 := by
    rw [cmpltuMask, BitVec.toNat_ofNat, foldl_bsum _ 32 fun j hj => (hw j hj).trans decide_eq_true_iff.symm]
    exact Nat.mod_eq_of_lt (bsum_lt _ 32)
  have g5 : s5.gpr = s.gpr := by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine ⟨?_, fun l hl => by rw [z6, l5 l hl], c5.same fun r _ l _ => z6 r l, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [r6, BitVec.toNat_setWidth, hm, zmask_bsum, Nat.mod_eq_of_lt (by
      have := zmaskL_lt X 0; have := zmaskL_lt X 1; have := zmaskL_lt X 2; have := zmaskL_lt X 3; omega_arith)]
  · rw [m6, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [rd6, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [wr6, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [y6, u5.syms, u4.syms, u3.syms, u2.syms, u1.syms]
  · rw [g6 r hr, g5]

/-! ## The compaction of a lane -/

theorem State.zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) {i : Nat} (hi4 : i < 4) :
    (s.setV .l256 d lo hi).zlane r i =
      if r = d then (if i = 0 then lo else if i = 1 then hi else 0) else s.zlane r i := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp
  · simp [h]

theorem ZUpd.setV256 (s : State) (d : XReg) (lo hi : BitVec 128) :
    ZUpd s (s.setV .l256 d lo hi) d fun l => if l = 0 then lo else if l = 1 then hi else 0 :=
  ⟨fun l hl => by rw [State.zlane_setV256 _ _ _ _ _ hl, ite_eq_left rfl],
    fun r hr l hl => by rw [State.zlane_setV256 _ _ _ _ _ hl, ite_eq_right hr], rfl, rfl, rfl, rfl, rfl⟩

theorem ZUpd.setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    ZUpd s (s.setV .l128 d lo hi) d fun l => if l = 0 then lo else 0 :=
  ⟨fun l hl => by rw [State.zlane_setV128 _ _ _ _ _ hl, ite_eq_left rfl],
    fun r hr l hl => by rw [State.zlane_setV128 _ _ _ _ _ hl, ite_eq_right hr], rfl, rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `wp_vtbl`, lane by lane of the `zmm` registers. -/
theorem wp_vtblZ {d : XReg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o + 4 ≤ ws.length)
    (k : ∀ s', ZUpd s s' d (fun l => if l = 0 then ws.getD (o + 1) 0 ++ ws.getD o 0
      else if l = 1 then ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquTbl d m name ws :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (ws.getD (o + 1) 0 ++ ws.getD o 0) (ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0))
    ?_ (k _ (ZUpd.setV256 _ _ _ _))
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, Nat.add_zero]

theorem wp_vbin128Z {op : VBinOp} {d a b : XReg}
    (k : ∀ s', ZUpd s s' d (fun l => if l = 0 then op.sse.eval (s.lane a 0) (s.lane b 0) else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l128 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l128 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (ZUpd.setV128 s d _ _))

theorem wp_vst128Z {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.zlane x l = s.zlane x l) → s'.mem = s.mem.writeW a (s.xmm r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

theorem wp_addTblZ {d : Reg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o < ws.length)
    (k : ∀ s', GUpd s s' d (s.gpr d + ws.getD o 0) → (∀ x l, s'.zlane x l = s.zlane x l) → WP isa (.block is) s' Q) :
    WP isa (.block (.aluTbl .add d m name ws :: is)) s Q := by
  let a := s.gpr d
  let b := ws.getD o 0
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 64 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    (a + b)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _) fun _ _ => rfl)
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, execAluW, a, b]

end

open VG.Proof.MlKem.X86_64 (WP.keep Keep) in
/-- `rdx := 2 (E >> 8 l) mod 256`, for `E` in `eax`. -/
theorem zidx_ok {s : State} {l E : Nat} (hl : l < 4) (hE : (s.gpr .rax).toNat = E) (hE32 : E < 2 ^ 32) :
    WP isa (.block (Impl.MlKem.X86_64.Sample4.zidx l)) s fun s' =>
      ((s'.gpr .rdx).toNat = 2 * (E / 256 ^ l % 256) ∧ s'.mem = s.mem ∧ s'.syms = s.syms ∧
        ∀ x i, s'.zlane x i = s.zlane x i) ∧ Keep [.rdx] s s' := by
  have h255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals
    refine WP.keep _ ?_ (by decide)
    simp only [Impl.MlKem.X86_64.Sample4.zidx, Nat.reduceMul, ↓reduceIte, List.nil_append, List.cons_append,
      show ¬ (1 : Nat) = 0 by decide, show ¬ (2 : Nat) = 0 by decide,
      show ¬ (3 : Nat) = 0 by decide, show ¬ (0 : Nat) = 3 by decide, show ¬ (1 : Nat) = 3 by decide,
      show ¬ (2 : Nat) = 3 by decide]
    xrun
    refine ⟨?_, rfl, fun _ _ => rfl⟩
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight, hE,
      show (255 : BitVec 32).toNat = 255 from rfl, h255, Nat.shiftRight_eq_div_pow]
    omega_arith

/-- Lane `l` after the compaction: the candidates less than `q` at its bottom. -/
abbrev zcompW (X : BitVec 512) (l : Nat) : BitVec 128 := XBinOp.eval .pshufb (zcandW X l) (idxV (zmaskL X l))

/-- The number of candidates less than `q` of lane `l`. -/
abbrev zcntL (X : BitVec 512) (l : Nat) : Nat := (setBits (zmaskL X l)).length

theorem zcntL_le (X : BitVec 512) (l : Nat) : zcntL X l ≤ 8 := by
  unfold zcntL setBits; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Byte `l` of the mask is lane `l`'s. -/
theorem zmask_byte (X : BitVec 512) {l : Nat} (hl : l < 4) :
    (zmaskL X 0 + 256 * zmaskL X 1 + 65536 * zmaskL X 2 + 16777216 * zmaskL X 3) / 256 ^ l % 256 = zmaskL X l := by
  have := zmaskL_lt X 0; have := zmaskL_lt X 1; have := zmaskL_lt X 2; have := zmaskL_lt X 3
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow] <;> omega_arith

/-- The state after `zputL l` from `s`, with the candidates of `X`. -/
structure ZPL (X : BitVec 512) (l : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) (zcompW X l)
  rdi : (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + zcntL X l
  z0 : ∀ i < 4, s'.zlane .xmm0 i = s.zlane .xmm0 i
  zc : ZC s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  gpr : ∀ r, r ≠ .rdx → r ≠ .rdi → s'.gpr r = s.gpr r

section
open VG.Impl.MlKem.X86_64.Sample4 (zputL zidx tblName tblWords idxE numE aJ16)
open VG.Proof.MlKem.X86_64 (Keep)

/-- After the mask's lane `l` is in `xmm1`: the store and the count. -/
theorem ztail_ok {s s₁ : State} {X : BitVec 512} {l : Nat}
    (h1 : s₁.lane .xmm1 0 = zcompW X l) (hz : ∀ i < 4, s₁.zlane .xmm0 i = s.zlane .xmm0 i) (hc : ZC s₁)
    (hdx : (s₁.gpr .rdx).toNat = 2 * zmaskL X l) (hg : ∀ r, r ≠ .rdx → s₁.gpr r = s.gpr r) (hm : s₁.mem = s.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hsy : s₁.syms = s.syms)
    (ht : s.gpr .r11 = s.syms tblName) (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) 16) :
    WP isa (.block [.vmovdquStore .l128 aJ16 .xmm1, .aluTbl .add .rdi (numE .rdx) tblName tblWords]) s₁ (ZPL X l s) := by
  have hm0 : zmaskL X l < 256 := zmaskL_lt X l
  have c0 := zcntL_le X l
  have bp : s₁.gpr .rbp = s.gpr .rbp := hg _ (by decide)
  have di : s₁.gpr .rdi = s.gpr .rdi := hg _ (by decide)
  refine wp_vst128Z (a := s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) (by rw [ea_aJ16, bp, di])
    (by rw [hwr]; exact hout) fun s6 g6 l6 m6 r6 w6 y6 => ?_
  have t6 : s6.gpr .r11 = s6.syms tblName := by rw [g6, y6, hg _ (by decide), hsy]; exact ht
  refine wp_addTblZ (o := 524 + zmaskL X l) t6 (ea_numE (by rw [g6]; exact hdx) hm0 t6)
    (by rw [tblWords_length]; omega_arith) fun s7 u7 z7 => WP.block_nil ?_
  refine ⟨?_, ?_, fun i hi => by rw [z7, l6, hz i hi], hc.same fun r _ i _ => by rw [z7, l6], ?_, ?_, ?_,
    fun r h1 h2 => ?_⟩
  · rw [u7.mem, m6, show s₁.xmm .xmm1 = s₁.lane .xmm1 0 from rfl, h1, hm]
  · rw [u7.gpr, BitVec.toNat_add, tblWords_cnt hm0, g6, di, BitVec.toNat_ofNat]
    simp only [zcntL] at c0 ⊢; omega_arith
  · rw [u7.rd, r6, hrd]
  · rw [u7.wr, w6, hwr]
  · rw [u7.syms, y6, hsy]
  · rw [u7.other r h2, g6, hg r h1]

/-- The candidates less than `q` of lane `l` to `a[j..]`, and `j` advanced by their number. -/
theorem zputL_ok {s : State} (hc : ZC s) {X : BitVec 512} {l : Nat} (hl : l < 4)
    (h0 : ∀ i < 4, s.zlane .xmm0 i = zcandW X i)
    (hrax : (s.gpr .rax).toNat = zmaskL X 0 + 256 * zmaskL X 1 + 65536 * zmaskL X 2 + 16777216 * zmaskL X 3)
    (ht : s.gpr .r11 = s.syms tblName) (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) 16) :
    WP isa (.block (zputL l)) s (ZPL X l s) := by
  have hm0 : zmaskL X l < 256 := zmaskL_lt X l
  have hE32 : zmaskL X 0 + 256 * zmaskL X 1 + 65536 * zmaskL X 2 + 16777216 * zmaskL X 3 < 2 ^ 32 := by
    have := zmaskL_lt X 0; have := zmaskL_lt X 1; have := zmaskL_lt X 2; have := zmaskL_lt X 3; omega_arith
  rw [zputL, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zidx_ok hl hrax hE32) fun s1 ⟨⟨hdx, hm, hsy, hz⟩, k1⟩ => ?_
  rw [zmask_byte X hl] at hdx
  have t1 : s1.gpr .r11 = s1.syms tblName := by rw [k1.gpr (by decide), hsy]; exact ht
  refine wp_vtblZ (o := 2 * zmaskL X l) t1 (ea_idxE hdx hm0 t1) (by rw [tblWords_length]; omega_arith) fun s2 u2 => ?_
  have i0 : s2.lane .xmm2 0 = idxV (zmaskL X l) := by
    rw [← s2.zlane_lt2 _ (by decide), u2.val 0 (by decide), ite_eq_left rfl, tblWords_idx hm0 (by decide),
      tblWords_idx0 hm0, idxQ_pair]
  have c2 : ZC s2 := (hc.same fun r _ i _ => hz r i).zupd u2
  have x2 : ∀ i < 4, s2.zlane .xmm0 i = zcandW X i := fun i hi => by rw [u2.other _ (by decide) i hi, hz, h0 i hi]
  have g2 : ∀ r, r ≠ .rdx → s2.gpr r = s.gpr r := fun r hr => by rw [u2.gpr, k1.gpr (by simp [hr])]
  have tail : ∀ s₃ : State, s₃.lane .xmm1 0 = zcompW X l → (∀ i < 4, s₃.zlane .xmm0 i = s2.zlane .xmm0 i) → ZC s₃ →
      s₃.gpr = s2.gpr → s₃.mem = s2.mem → s₃.rd = s2.rd → s₃.wr = s2.wr → s₃.syms = s2.syms →
      WP isa (.block [.vmovdquStore .l128 aJ16 .xmm1, .aluTbl .add .rdi (numE .rdx) tblName tblWords]) s₃ (ZPL X l s) :=
    fun s₃ h1 hz3 c3 g3 m3 rd3 wr3 y3 =>
      ztail_ok h1 (fun i hi => by rw [hz3 i hi, x2 i hi, h0 i hi]) c3 (by rw [g3, u2.gpr]; exact hdx)
        (fun r hr => by rw [g3, g2 r hr]) (by rw [m3, u2.mem, hm]) (by rw [rd3, u2.rd, k1.2.1])
        (by rw [wr3, u2.wr, k1.2.2]) (by rw [y3, u2.syms, hsy]) ht hdi hout
  by_cases hl0 : l = 0
  · subst hl0
    rw [ite_eq_left rfl, List.cons_append, List.nil_append]
    refine wp_vbin128Z fun s3 u3 => tail s3 ?_ (fun i hi => u3.other _ (by decide) i hi) (c2.zupd u3) u3.gpr u3.mem
      u3.rd u3.wr u3.syms
    rw [← s3.zlane_lt2 _ (by decide), u3.val 0 (by decide), ite_eq_left rfl, i0, ← s2.zlane_lt2 _ (by decide),
      x2 0 (by decide)]
    rfl
  · rw [ite_eq_right hl0, List.cons_append, List.cons_append, List.nil_append]
    refine wp_zext fun s3 u3 => wp_vbin128Z fun s4 u4 =>
      tail s4 ?_ (fun i hi => by rw [u4.other _ (by decide) i hi, u3.other _ (by decide) i hi])
        ((c2.zupd u3).zupd u4) (by rw [u4.gpr, u3.gpr]) (by rw [u4.mem, u3.mem]) (by rw [u4.rd, u3.rd])
        (by rw [u4.wr, u3.wr]) (by rw [u4.syms, u3.syms])
    have e3 : s3.lane .xmm1 0 = zcandW X l := by
      rw [← s3.zlane_lt2 _ (by decide), u3.val 0 (by decide), ite_eq_left rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show l < 2 ^ 8 by omega_arith), Nat.mod_eq_of_lt hl, x2 l hl]
    have j3 : s3.lane .xmm2 0 = idxV (zmaskL X l) := by
      rw [← s3.zlane_lt2 _ (by decide), u3.other _ (by decide) 0 (by decide), s2.zlane_lt2 _ (by decide), i0]
    rw [← s4.zlane_lt2 _ (by decide), u4.val 0 (by decide), ite_eq_left rfl, e3, j3]
    rfl

end

end VG.Proof.MlKem.X86_64.S4
