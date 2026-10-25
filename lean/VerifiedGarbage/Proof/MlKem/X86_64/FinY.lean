module
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.X86_64.AddSub

import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: the AVX2 accumulator added to a polynomial

`finAccY` (`Impl/MlKem/X86_64/KpkeAccY.lean`) adds the accumulator in words
at `rsi` to the `u32`s at `rdi`, 32 coefficients an iteration. Of the two
registers of words it loads, `vpunpcklwd` and `vpunpckhwd` (`L` and `H`)
put coefficient `8q + 4l + e` of the 32 (`q < 4`, `e < 4`) at word
`4(q mod 2) + e` of lane `l` of `L` (`q < 2`) or `H`: the accumulator's word
`srcF q l e` (`srcF_ok`). `vpunpcklwd` or `vpunpckhwd` with zero extends
those four words to doublewords (`dword_unpk0`), and `vg_mlkem_add_avx2`'s
arithmetic adds them to the eight `u32`s at `rdi + 32q` (`finQ_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

namespace FinY

/-- The word of an iteration's 32 (of the accumulator) whose coefficient is
`8q + 4l + e`. -/
def srcF (q l e : Nat) : Nat := 16 * (e % 2) + 8 * l + 2 * q + e / 2

theorem srcF_ok : ∀ q < 4, ∀ l < 2, ∀ e < 4, srcF q l e < 32 ∧ accIdx (srcF q l e) = 8 * q + 4 * l + e := by
  decide +kernel

theorem word_zero128 {i : Nat} : word (0 : BitVec 128) i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [getLsbD_word]

/-- Doubleword `e` of `vpunpcklwd` (`h = 0`) or `vpunpckhwd` (`h = 1`) of `a`
and zero: word `4h + e` of `a`. -/
theorem dword_unpk0 (a : BitVec 128) {h : Nat} (hh : h < 2) {e : Nat} (he : e < 4) :
    (dword (XBinOp.eval (if h = 0 then .punpcklwd else .punpckhwd) a 0) e).toNat = (word a (4 * h + e)).toNat := by
  rw [dword_eq_words _ he]
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
  · simp (disch := omega_arith) only [word_punpcklwd, Nat.mul_mod_right, Nat.add_mod, Nat.mul_zero, Nat.zero_add,
      Nat.one_mod, ↓reduceIte]
    simp only [Nat.one_ne_zero, ite_false, word_zero128, show 2 * e / 2 = e by omega_arith,
      show BitVec.toNat (0 : BitVec 16) = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · simp (disch := omega_arith) only [Nat.one_ne_zero, word_punpckhwd, Nat.mul_mod_right, Nat.add_mod, Nat.zero_add,
      Nat.one_mod, ↓reduceIte]
    simp only [word_zero128, show 4 + 2 * e / 2 = 4 * 1 + e by omega_arith,
      show BitVec.toNat (0 : BitVec 16) = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- In a lane: a word of `w` unpacked with `xmm14` (`op`), added to `xmm0` with
`vg_mlkem_add`'s arithmetic. -/
theorem unpkAdd_ok (w : XReg) (op : XBinOp) (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block ([xb .movdqa .xmm1 w, xb op .xmm1 .xmm14] ++ addArith)) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j =
        cadd32 (dword (s.xmm .xmm0) j + dword (XBinOp.eval op (s.xmm w) (s.xmm .xmm14)) j - 3329#32)) ∧
      XOnly [.xmm1, .xmm0, .xmm1] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.xmm .xmm1 = XBinOp.eval op (s.xmm w) (s.xmm .xmm14) ∧ XOnly [.xmm1] s s1)
    (by
      simp only [xb]
      vrun [eval_movdqa]
      exact ⟨trivial, by xonly⟩) fun s1 ⟨h1, o1⟩ => ?_
  refine WP.mono (addArith_ok s1 (by rw [o1.xmm _ (by decide), hq])) fun s2 ⟨h2, o2⟩ =>
    ⟨fun j hj => ?_, o1.trans o2⟩
  rw [h2 j hj, h1, o1.xmm _ (by decide)]

/-- `finQ w op off`: the eight `u32`s at `rdi + off` plus the words of `w`
unpacked with `xmm14` (`op`), by `vg_mlkem_add_avx2`'s arithmetic, stored back. -/
theorem finQ_ok {w : XReg} (hw0 : w ≠ .xmm0) {op : VBinOp} {xop : XBinOp}
    (hl : laneSseBlock ([yb op .xmm1 w .xmm14] ++ toY addArith) =
      some ([xb .movdqa .xmm1 w, xb xop .xmm1 .xmm14] ++ addArith))
    {off : Nat} {s : State} (hq : ∀ l < 2, s.lane .xmm15 l = qD)
    (hin : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 off) 32) :
    WP isa (.block (finQ w op off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 off) (s'.ymm .xmm0) ∧
      (∀ l < 2, ∀ e < 4, dword (s'.lane .xmm0 l) e =
        cadd32 (dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e +
          dword (XBinOp.eval xop (s.lane w l) (s.lane .xmm14 l)) e - 3329#32)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧
      ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, s'.lane r l = s.lane r l := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 off) 32 :=
    let ⟨r, hr, hc⟩ := hin; ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show finQ w op off = [.vmovdquLoad .l256 .xmm0 (at_ .rdi off)] ++
      (([yb op .xmm1 w .xmm14] ++ toY addArith) ++ [.vmovdquStore .l256 (at_ .rdi off) .xmm0]) from rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok hin') fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hl (P := fun l t => ∀ j < 4, dword (t.xmm .xmm0) j =
      cadd32 (dword ((s1.proj l).xmm .xmm0) j +
        dword (XBinOp.eval xop ((s1.proj l).xmm w) ((s1.proj l).xmm .xmm14)) j - 3329#32))
    fun l hl' => unpkAdd_ok w xop _ (by rw [State.proj_xmm, o1.lane _ (by decide) l hl']; exact hq l hl'))
    fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  refine WP.mono (yst_ok (h := .xmm0) (by rw [o12.wr, o12.gpr]; exact hin)) fun s3 e3 => ?_
  subst e3
  refine ⟨by simp only [State.setMem_mem, State.setMem_ymm]; rw [o12.mem, o12.gpr], fun l hl' e he => ?_,
    by simp only [State.setMem_gpr]; exact o12.gpr, by simp only [State.setMem_rd]; exact o12.rd,
    by simp only [State.setMem_wr]; exact o12.wr, ?_, fun r hr l hl' => ?_⟩
  · simp only [State.setMem_lane]
    rw [← State.proj_xmm, L2 l hl' e he, State.proj_xmm, State.proj_xmm, State.proj_xmm, L1 l hl',
      o1.lane _ (by simpa using hw0) l hl', o1.lane _ (by decide) l hl']
  · rw [show (s2.setMem _).mxcsr = s2.mxcsr by cases s2; rfl]; exact o12.mxcsr
  · simp only [State.setMem_lane]; exact o12.lane r (by simpa [or_comm, or_left_comm] using hr) l hl'

/-- The first `8j` coefficients at `tP` are those of `E + F`, and the others
those of `m₀`. -/
def MemOk (m₀ : Mem) (tP : Addr) (E F : Poly) (j : Nat) (m : Mem) : Prop :=
  ∀ c < 256, (c < 8 * j → (coeffAt m tP c).toNat = ((add E F)[c]!).val) ∧
    (8 * j ≤ c → coeffAt m tP c = coeffAt m₀ tP c)

/-- `finQ` on the coefficients `8j, …, 8j + 7`. -/
theorem finQ_step {tP : Addr} {m₀ : Mem} {E F : Poly}
    (hE : ∀ c < 256, (coeffAt m₀ tP c).toNat < q ∧ (E[c]!).val = (coeffAt m₀ tP c).toNat)
    {w : XReg} (hw0 : w ≠ .xmm0) {op : VBinOp} {xop : XBinOp}
    (hl : laneSseBlock ([yb op .xmm1 w .xmm14] ++ toY addArith) =
      some ([xb .movdqa .xmm1 w, xb xop .xmm1 .xmm14] ++ addArith)) {h : Nat}
    (hop : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval xop a 0) e).toNat = (word a (4 * h + e)).toNat)
    {j off : Nat} (hj : j < 32) {u : State}
    (hrdi : u.gpr .rdi + BitVec.ofNat 64 off = coeffAddr tP (8 * j))
    (hq : ∀ l < 2, u.lane .xmm15 l = qD) (hz : ∀ l < 2, u.lane .xmm14 l = 0)
    (hwv : ∀ l < 2, ∀ e < 4, (word (u.lane w l) (4 * h + e)).toNat = (F[8 * j + 4 * l + e]!).val)
    (hin : InRegions u.wr (coeffAddr tP (8 * j)) 32) (hM : MemOk m₀ tP E F j u.mem) :
    WP isa (.block (finQ w op off)) u fun u' => MemOk m₀ tP E F (j + 1) u'.mem ∧
      u'.mem = u.mem.writeW (coeffAddr tP (8 * j)) (u'.ymm .xmm0) ∧ u'.gpr = u.gpr ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧ ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, u'.lane r l = u.lane r l := by
  refine WP.mono (finQ_ok hw0 hl hq (by rw [hrdi]; exact hin))
    fun u' ⟨hm, hd, hg, hrd, hwr, hmx, hlane⟩ => ⟨fun c hc => ?_, by rw [hm, hrdi], hg, hrd, hwr, hmx, hlane⟩
  rw [hm, hrdi, coeffAt_write256 _ _ (by omega_arith) _ hc]
  split
  · rename_i hr
    obtain ⟨l, e, hl', he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ c = 8 * j + 4 * l + e :=
      ⟨(c - 8 * j) / 4, (c - 8 * j) % 4, by omega_arith, by omega_arith, by omega_arith⟩
    refine ⟨fun _ => ?_, fun h' => absurd h' (by omega_arith)⟩
    have hrest := (hM _ hc).2 (by omega_arith)
    have ha : (dword (u.mem.readW (u.gpr .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e).toNat =
        (coeffAt m₀ tP (8 * j + 4 * l + e)).toNat := by
      rw [hrdi, YAddSub.lane_coeff _ _ _ _ _ he, hrest]
    have hb : (dword (XBinOp.eval xop (u.lane w l) (u.lane .xmm14 l)) e).toNat = (F[8 * j + 4 * l + e]!).val := by
      rw [hz l hl', hop _ e he, hwv l hl' e he]
    rw [show 8 * (4 * (8 * j + 4 * l + e - 8 * j)) = 8 * (16 * l + 4 * e) by omega_arith, extract_ymm _ _ hl' he,
      hd l hl' e he, add_lane (by rw [ha]; exact (hE _ hc).1) (by rw [hb]; exact (F[8 * j + 4 * l + e]!).isLt), ha, hb,
      add_get _ _ (by rw [n_eq]; exact hc), val_add, (hE _ hc).2]
  · rename_i hr
    exact ⟨fun h' => (hM c hc).1 (by omega_arith), fun h' => (hM c hc).2 (by omega_arith)⟩

/-- `vpunpcklwd ymm10, ymm8, ymm9` and `vpunpckhwd ymm11, ymm8, ymm9`, in a lane. -/
theorem unpk2_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm10 .xmm8, xb .punpcklwd .xmm10 .xmm9, xb .movdqa .xmm11 .xmm8,
        xb .punpckhwd .xmm11 .xmm9]) t fun t' =>
      (t'.xmm .xmm10 = XBinOp.eval .punpcklwd (t.xmm .xmm8) (t.xmm .xmm9) ∧
        t'.xmm .xmm11 = XBinOp.eval .punpckhwd (t.xmm .xmm8) (t.xmm .xmm9)) ∧ XOnly [.xmm10, .xmm11] t t' := by
  simp only [xb]
  vrun [eval_movdqa]
  exact ⟨trivial, by xonly⟩

theorem lane_unpk2 : laneSseBlock [yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] =
    some [xb .movdqa .xmm10 .xmm8, xb .punpcklwd .xmm10 .xmm9, xb .movdqa .xmm11 .xmm8,
      xb .punpckhwd .xmm11 .xmm9] := by
  decide +kernel

/-- Word `4(q mod 2) + e` of `L` (`q < 2`) or `H`, the `vpunpck{l,h}wd` of
lanes `A` and `B` holding the words of the accumulator's coefficients of
iteration `i` (`accIdx`): coefficient `8(4i + q) + 4l + e`. -/
theorem wv_of_w {F : Poly} {i : Nat} {A B : BitVec 128} {l : Nat} (hl : l < 2)
    (hw : ∀ h < 2, ∀ k < 8, (word (if h = 0 then A else B) k).toNat = (F[accIdx (32 * i + 16 * h + 8 * l + k)]!).val)
    {q : Nat} (hq : q < 4) {e : Nat} (he : e < 4) :
    (word (if q < 2 then XBinOp.eval .punpcklwd A B else XBinOp.eval .punpckhwd A B) (4 * (q % 2) + e)).toNat =
      (F[8 * (4 * i + q) + 4 * l + e]!).val := by
  have hs := srcF_ok q hq l hl e he
  have hidx : 32 * i + 16 * (e % 2) + 8 * l + (2 * q + e / 2) = 32 * i + srcF q l e := by unfold srcF; omega_arith
  have hacc : accIdx (32 * i + srcF q l e) = 8 * (4 * i + q) + 4 * l + e := by
    rw [accIdx_add32 hs.1, hs.2]; omega_arith
  by_cases hq2 : q < 2
  · rw [ifp hq2]
    simp (disch := omega_arith) only [word_punpcklwd]
    have h1 : (if (4 * (q % 2) + e) % 2 = 0 then word A ((4 * (q % 2) + e) / 2) else word B ((4 * (q % 2) + e) / 2)) =
        word (if e % 2 = 0 then A else B) (2 * q + e / 2) := by
      rcases (by omega_arith : e % 2 = 0 ∨ e % 2 = 1) with h | h
      · rw [ifp (by omega_arith), ifp h]; exact congrArg _ (by omega_arith)
      · rw [ifn (by omega_arith), ifn (by omega_arith)]; exact congrArg _ (by omega_arith)
    rw [h1, hw _ (by omega_arith) _ (by omega_arith), hidx, hacc]
  · rw [ifn hq2]
    simp (disch := omega_arith) only [word_punpckhwd]
    have h1 : (if (4 * (q % 2) + e) % 2 = 0 then word A (4 + (4 * (q % 2) + e) / 2)
        else word B (4 + (4 * (q % 2) + e) / 2)) = word (if e % 2 = 0 then A else B) (2 * q + e / 2) := by
      rcases (by omega_arith : e % 2 = 0 ∨ e % 2 = 1) with h | h
      · rw [ifp (by omega_arith), ifp h]; exact congrArg _ (by omega_arith)
      · rw [ifn (by omega_arith), ifn (by omega_arith)]; exact congrArg _ (by omega_arith)
    rw [h1, hw _ (by omega_arith) _ (by omega_arith), hidx, hacc]

/-- Word `4(q mod 2) + e` of lane `l` of `L` (`q < 2`) or `H`, from the two
loads of iteration `i`: the accumulator's word of coefficient
`8(4i + q) + 4l + e`. -/
theorem wv_of {m : Mem} {aP : Addr} {F : Poly} (hF : Acc16 m aP F) {i : Nat} (hi : i < 8) {A B : BitVec 128}
    {l : Nat} (hl : l < 2)
    (hA : A = m.readW (wAddr aP (32 * i) + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
    (hB : B = m.readW (wAddr aP (32 * i) + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
    {q : Nat} (hq : q < 4) {e : Nat} (he : e < 4) :
    (word (if q < 2 then XBinOp.eval .punpcklwd A B else XBinOp.eval .punpckhwd A B) (4 * (q % 2) + e)).toNat =
      (F[8 * (4 * i + q) + 4 * l + e]!).val :=
  wv_of_w hl (fun h hh k hk => by
    rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
    · rw [ifp rfl, hA, show (BitVec.ofNat 64 0 : BitVec 64) = BitVec.ofNat 64 (32 * 0) from rfl,
        acc_word _ _ _ _ _ hk]; exact hF _ (by omega_arith)
    · rw [ifn (by decide), hB, show (BitVec.ofNat 64 32 : BitVec 64) = BitVec.ofNat 64 (32 * 1) from rfl,
        acc_word _ _ _ _ _ hk]; exact hF _ (by omega_arith)) hq he

theorem rdi_q (p : Addr) (i q off : Nat) (h : off = 32 * q) :
    coeffAddr p (32 * i) + BitVec.ofNat 64 off = coeffAddr p (8 * (4 * i + q)) := by
  subst h; rw [show 32 * q = 4 * (8 * q) by omega_arith, coeffAddr_off]; exact congrArg _ (by omega_arith)

/-- After `i` iterations, with `F` the accumulator. -/
structure Inv (s₀ : State) (F : Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (32 * i)
  rsi : s.gpr .rsi = wAddr (s₀.gpr .rsi) (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qD
  z : ∀ l < 2, s.lane .xmm14 l = 0
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  mem : MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F (4 * i) s.mem

section
variable {s₀ : State} (hp : (finK accY).pre s₀) {F : Poly} (hF : Acc16 s₀.mem (s₀.gpr .rsi) F)
include hp hF

omit hF in
theorem hE : ∀ c < 256, (coeffAt s₀.mem (s₀.gpr .rdi) c).toNat < q ∧
    ((polyAt s₀.mem (s₀.gpr .rdi))[c]!).val = (coeffAt s₀.mem (s₀.gpr .rdi) c).toNat := fun c hc =>
  ⟨hp.2.2.2.2.2.1 c (by rw [n_eq]; exact hc), polyAt_val hp.2.2.2.2.2.1 (by rw [n_eq]; exact hc)⟩

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ F i s) :
    WP isa (.block (finAccBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ F (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hwT : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hrA : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have hFs : Acc16 s.mem (s₀.gpr .rsi) F :=
    accY.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.2.2.1.symm) hF
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 0) 32 :=
    ⟨_, hrA, by rw [hI.rsi, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 32) 32 :=
    ⟨_, hrA, by rw [hI.rsi, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [show finAccBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [.vmovdquLoad .l256 .xmm8 (at_ .rsi 0)] ++ ([.vmovdquLoad .l256 .xmm9 (at_ .rsi 32)] ++
        ([yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] ++
        (finQ .xmm10 .vpunpcklwd 0 ++ (finQ .xmm10 .vpunpckhwd 32 ++ (finQ .xmm11 .vpunpcklwd 64 ++
        (finQ .xmm11 .vpunpckhwd 96 ++ ([.alu .add .rsi (.imm 64), .alu .add .rdi (.imm 128),
          .alu .sub .rcx (.imm 1)] : List Instr))))))) from rfl, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L8, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L9, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_unpk2 (P := fun l t =>
      t.xmm .xmm10 = XBinOp.eval .punpcklwd ((s2.proj l).xmm .xmm8) ((s2.proj l).xmm .xmm9) ∧
      t.xmm .xmm11 = XBinOp.eval .punpckhwd ((s2.proj l).xmm .xmm8) ((s2.proj l).xmm .xmm9))
    fun l _ => unpk2_ok _) fun s3 ⟨U3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  -- the words of `L` and `H`
  have hLH : ∀ q < 4, ∀ l < 2, ∀ e < 4,
      (word (if q < 2 then s3.lane .xmm10 l else s3.lane .xmm11 l) (4 * (q % 2) + e)).toNat =
        (F[8 * (4 * i + q) + 4 * l + e]!).val := by
    intro q hq l hl e he
    have e10 : s3.lane .xmm10 l = XBinOp.eval .punpcklwd (s2.lane .xmm8 l) (s2.lane .xmm9 l) := by
      rw [← State.proj_xmm, (U3 l hl).1, State.proj_xmm, State.proj_xmm]
    have e11 : s3.lane .xmm11 l = XBinOp.eval .punpckhwd (s2.lane .xmm8 l) (s2.lane .xmm9 l) := by
      rw [← State.proj_xmm, (U3 l hl).2, State.proj_xmm, State.proj_xmm]
    have hA : s2.lane .xmm8 l = s.mem.readW (wAddr (s₀.gpr .rsi) (32 * i) + BitVec.ofNat 64 0 +
        BitVec.ofNat 64 (16 * l)) 128 := by rw [o2.lane _ (by decide) l hl, L8 l hl, hI.rsi]
    have hB : s2.lane .xmm9 l = s.mem.readW (wAddr (s₀.gpr .rsi) (32 * i) + BitVec.ofNat 64 32 +
        BitVec.ofNat 64 (16 * l)) 128 := by rw [L9 l hl, o1.mem, o1.gpr, hI.rsi]
    have := wv_of hFs hi hl hA hB hq he
    by_cases hq2 : q < 2
    · rw [ifp hq2] at this ⊢; rw [e10]; exact this
    · rw [ifn hq2] at this ⊢; rw [e11]; exact this
  have hz3 : ∀ l < 2, s3.lane .xmm14 l = 0 := fun l hl => by rw [o13.lane _ (by decide) l hl]; exact hI.z l hl
  have hq3 : ∀ l < 2, s3.lane .xmm15 l = qD := fun l hl => by rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  have hrdi3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (32 * i) := by rw [o13.gpr, hI.rdi]
  have hw3 : s3.wr = s₀.wr := by rw [o13.wr, hI.wr]
  have hM3 : MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F (4 * i + 0) s3.mem := by
    rw [o13.mem]; exact hI.mem
  have inT : ∀ q < 4, InRegions s₀.wr (coeffAddr (s₀.gpr .rdi) (8 * (4 * i + q))) 32 := fun q hq => by
    rw [hp.2.1]; exact YAddSub.in32 (List.mem_singleton_self _) (by omega_arith)
  have hop0 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpcklwd a 0) e).toNat = (word a (4 * 0 + e)).toNat :=
    fun a e he => by have := dword_unpk0 a (h := 0) (by decide) he; rwa [ifp rfl] at this
  have hop1 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpckhwd a 0) e).toNat = (word a (4 * 1 + e)).toNat :=
    fun a e he => by have := dword_unpk0 a (h := 1) (by decide) he; rwa [ifn (by decide)] at this
  -- coefficients `32i, …, 32i + 7`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm10) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * i + 0) (by omega_arith) (by rw [hrdi3]; exact rdi_q _ _ _ _ rfl) hq3 hz3
    (fun l hl e he => by have := hLH 0 (by decide) l hl e he; rwa [ifp (by decide)] at this)
    (by rw [hw3]; exact inT 0 (by decide)) hM3) fun s4 ⟨M4, m4, g4, rd4, wr4, x4, ln4⟩ => ?_
  -- `32i + 8, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm10) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * i + 1) (by omega_arith) (by rw [g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 1 (by decide) l hl e he; rw [ifp (by decide)] at this; rw [ln4 _ (by decide) l hl]; exact this)
    (by rw [wr4, hw3]; exact inT 1 (by decide)) M4) fun s5 ⟨M5, m5, g5, rd5, wr5, x5, ln5⟩ => ?_
  -- `32i + 16, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm11) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * i + 2) (by omega_arith) (by rw [g5, g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 2 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact this)
    (by rw [wr5, wr4, hw3]; exact inT 2 (by decide)) M5) fun s6 ⟨M6, m6, g6, rd6, wr6, x6, ln6⟩ => ?_
  -- `32i + 24, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm11) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * i + 3) (by omega_arith) (by rw [g6, g5, g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 3 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact this)
    (by rw [wr6, wr5, wr4, hw3]; exact inT 3 (by decide)) M6) fun s7 ⟨M7, m7, g7, rd7, wr7, x7, ln7⟩ => ?_
  have g37 : s7.gpr = s.gpr := by rw [g7, g6, g5, g4, o13.gpr]
  have l37 : ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, s7.lane r l = s3.lane r l := fun r hr l hl => by
    rw [ln7 r hr l hl, ln6 r hr l hl, ln5 r hr l hl, ln4 r hr l hl]
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  have cT : ∀ q < 4, (pR (s₀.gpr .rdi)).Contains (coeffAddr (s₀.gpr .rdi) (8 * (4 * i + q))) 32 := fun q hq =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  vrunm [sx64, sx128]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g37, hI.rdi, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g37, hI.rsi, wAddr_add, Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [rd7, rd6, rd5, rd4, o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [wr7, wr6, wr5, wr4, hw3]
  · simp only [lane_setReg, lane_setFlags]; rw [l37 _ (by decide) l hl]; exact hq3 l hl
  · simp only [lane_setReg, lane_setFlags]; rw [l37 _ (by decide) l hl]; exact hz3 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m7, m6, m5, m4, o13.mem]
    exact (((hI.frame.writeW (List.mem_singleton_self _) _ (cT 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cT 1 (by decide))).writeW (List.mem_singleton_self _) _
      (cT 2 (by decide))).writeW (List.mem_singleton_self _) _ (cT 3 (by decide))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [show 4 * (i + 1) = 4 * i + 3 + 1 by omega_arith]; exact M7
  · rw [g37]
  · rw [g37]

end

/-- `pxor xmm14, xmm14`. -/
theorem zero14_ok (t : State) :
    WP isa (.block [xb .pxor .xmm14 .xmm14]) t fun t' => t'.xmm .xmm14 = 0 ∧ XOnly [.xmm14] t t' := by
  simp only [xb]
  vrun
  exact ⟨pxor_self _, by xonly⟩

end FinY

theorem finAccY_correct (s₀ : State) (hs : (finK accY).pre s₀) :
    ∃ t s', Exec isa finAccY s₀ t s' ∧ abiPreserved s₀ s' ∧ (finK accY).post s₀ s' := by
  obtain ⟨F0, hF0⟩ := hs.2.2.2.2.2.2
  have hW : WP isa finAccY s₀ fun s' => Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧
      FinY.MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F0 (4 * 8) s'.mem := by
    unfold finAccY
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, lo⟩ => ?_
    refine WP.mono (ylanes (vs := [yb .vpxor .xmm14 .xmm14 .xmm14]) (by decide +kernel)
      (P := fun _ t => t.xmm .xmm14 = 0) fun l _ => FinY.zero14_ok _) fun w2 ⟨Z2, o2⟩ => ?_
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (FinY.Inv s₀ F0) (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), o2.gpr, k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.gpr (by decide), o2.gpr, k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, o2.rd, k1.2.1], by rw [o.keep.2.2, o2.wr, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w2.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy],
            o2.lane _ (by decide) l hl, lq l hl]; decide,
        fun l hl => by
          rw [show u.lane .xmm14 l = w2.lane .xmm14 l by simp only [State.lane]; rw [o.xmm, hy],
            ← State.proj_xmm]; exact Z2 l hl,
        by rw [o.mem, o2.mem, m1]; exact Frame.refl _ _,
        fun c _ => ⟨fun h => absurd h (by omega_arith), fun _ => by rw [o.mem, o2.mem, m1]⟩⟩)
      fun i hi u hI => FinY.step hs hF0 hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, hI.mem⟩
  obtain ⟨t, s', he, ⟨hf, hM⟩, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rcx] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_),
    fun F hF => ?_⟩
  · simpa using hs.2.2.2.1
  · rw [acc16_unique hF hF0]
    exact polyIs_of_toNat fun c hc => (hM c (by rw [n_eq] at hc; exact hc)).1 (by rw [n_eq] at hc; omega_arith)


end VG.Proof.MlKem.X86_64
