import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.Blake2.Lanes
import VerifiedGarbage.Impl.Blake2.X86_64.Avx2

/-!
# BLAKE2b on x86-64 with AVX2: a round

The rows of the work vector are in `ymm0`–`ymm3` (`words`, as for Argon2's
`GB`). Each message vector is gathered into `ymm5` (`msg_ok`), each half of
`G` runs on the four quadwords at once (`half1_cols`, `half2_cols`), and the
diagonals are rotated into columns and back (`diag_words`, `undiag_words`);
`round_ok` composes them into `Spec.Blake2.round` through `round_lanes`.
-/

namespace VG.Proof.Blake2.X86_64.Avx2

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx2
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Argon2.X86_64.Avx2 (vrun runBlock_vops vrun_append Masks xorRot32Ops xorRot24Ops
  xorRot16Ops xorRot63Ops xorRot32_qw xorRot24_qw xorRot16_qw xorRot63_qw words words_get
  cases_div4 x0 x1 x2 x3 qw_vpshufd qword_readW128 vrun_gpr vrun_mem vrun_rd vrun_wr)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword_paddq qw_vbin qw_lane qw_vpermq sel4 qw_vpblendd pick2
  qw_setV256 qword_eq qword_ofDwords)
open VG.Proof.Blake2 (mix mixCols rotIn rotOut mixCols_get rotIn_get rotOut_get round_lanes)

abbrev W := BitVec 64

/-! ## The two halves of `G` -/

/-- `a += x + b; d = (d ^ a) >>> 32; c += d; b = (b ^ c) >>> 24`. -/
def H1 (v : W × W × W × W) (x : W) : W × W × W × W :=
  let a := v.1 + x + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight 32
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight 24
  (a, b, c, d)

/-- `a += y + b; d = (d ^ a) >>> 16; c += d; b = (b ^ c) >>> 63`. -/
def H2 (v : W × W × W × W) (y : W) : W × W × W × W :=
  let a := v.1 + y + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight 16
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight 63
  (a, b, c, d)

theorem add_right_comm' (a b c : W) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc]

theorem mix_eq (va vb vc vd x y : W) :
    mix Spec.Blake2.b va vb vc vd x y = H2 (H1 (va, vb, vc, vd) x) y := by
  simp only [mix, H1, H2, Spec.Blake2.b, add_right_comm' va vb x]
  rw [add_right_comm' _ _ y]

/-- The quadwords `k` of the four rows. -/
def cols (s : State) (k : Nat) : W × W × W × W := (qw s x0 k, qw s x1 k, qw s x2 k, qw s x3 k)

def half1Ops : List VOp :=
  [.vbin .vpaddq .l256 x0 x0 .xmm5, .vbin .vpaddq .l256 x0 x0 x1] ++
    (xorRot32Ops x3 x0 ++ ([.vbin .vpaddq .l256 x2 x2 x3] ++ xorRot24Ops x1 x2))

def half2Ops : List VOp :=
  [.vbin .vpaddq .l256 x0 x0 .xmm5, .vbin .vpaddq .l256 x0 x0 x1] ++
    (xorRot16Ops x3 x0 ++ ([.vbin .vpaddq .l256 x2 x2 x3] ++ xorRot63Ops x1 x2))

theorem half1_eq : half1 = half1Ops.map .vop := rfl
theorem qw_add (s : State) (d a b r : XReg) (k : Nat) :
    qw ((VOp.vbin .vpaddq .l256 d a b).exec s) r k = if r = d then qw s a k + qw s b k else qw s r k := by
  rw [qw_vbin]
  split
  · simp only [VBinOp.sse, qword_paddq _ _ (Nat.mod_lt k (by decide)), qw_lane]
  · rfl

theorem vrun_cons_nil (o : VOp) (s : State) : vrun [o] s = o.exec s := rfl
theorem vrun_pair (o o' : VOp) (s : State) : vrun [o, o'] s = o'.exec (o.exec s) := rfl

theorem half1_cols {s : State} (h : Masks s) {k : Nat} (hk : k < 4) :
    cols (vrun half1Ops s) k = H1 (cols s k) (qw s .xmm5 k) := by
  have m3 : Masks ((VOp.vbin .vpaddq .l256 x2 x2 x3).exec (vrun (xorRot32Ops x3 x0)
      ((VOp.vbin .vpaddq .l256 x0 x0 x1).exec ((VOp.vbin .vpaddq .l256 x0 x0 .xmm5).exec s)))) :=
    (Masks.xorRot32 ((h.vbin (by decide) (by decide)).vbin (by decide) (by decide)) (by decide)
      (by decide)).vbin (by decide) (by decide)
  simp only [half1Ops, vrun_append, vrun_cons_nil, vrun_pair]
  simp (disch := decide) only [cols, xorRot24_qw (d := x1) (by decide) _ m3 _ hk, xorRot32_qw,
    qw_add, ↓reduceIte, reduceCtorEq]
  rfl

theorem half2_cols {s : State} (h : Masks s) {k : Nat} (hk : k < 4) :
    cols (vrun half2Ops s) k = H2 (cols s k) (qw s .xmm5 k) := by
  have m3 : Masks ((VOp.vbin .vpaddq .l256 x0 x0 x1).exec ((VOp.vbin .vpaddq .l256 x0 x0 .xmm5).exec s)) :=
    (h.vbin (by decide) (by decide)).vbin (by decide) (by decide)
  simp only [half2Ops, vrun_append, vrun_cons_nil, vrun_pair]
  simp (disch := decide) only [cols, xorRot63_qw (d := x1) (by decide), xorRot16_qw (d := x3)
    (by decide) _ m3 _ hk, qw_add, ↓reduceIte, reduceCtorEq]
  rfl

/-! ## The registers each block leaves alone -/

/-- The lanes of `r` are those of `s`. -/
def Keeps (r : XReg) (s t : State) : Prop := ∀ l, t.lane r l = s.lane r l

theorem keeps_vpermq {r d : XReg} (h : r ≠ d) (a : XReg) (o : BitVec 8) (s : State) :
    Keeps r s ((VOp.vpermq d a o).exec s) := fun _ =>
  VG.Proof.Argon2.X86_64.Avx2.lane_vpermq _ _ _ _ _ h

theorem Keeps.trans {r : XReg} {s t u : State} (h : Keeps r s t) (h' : Keeps r t u) : Keeps r s u :=
  fun l => (h' l).trans (h l)

/-- The registers `half1Ops` and `half2Ops` write. -/
def halfRegs : List XReg := [x0, x1, x2, x3, .xmm4]

theorem half1_keeps {r : XReg} (hr : r ∉ halfRegs) (s : State) : Keeps r s (vrun half1Ops s) := by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, -⟩ := hr
  intro l
  simp only [half1Ops, xorRot32Ops, xorRot24Ops, List.cons_append, List.nil_append, vrun,
    lane_vbin256, lane_vpshufd256, h0, h1, h2, h3, ite_false]

theorem half2_keeps {r : XReg} (hr : r ∉ halfRegs) (s : State) : Keeps r s (vrun half2Ops s) := by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  intro l
  simp only [half2Ops, xorRot16Ops, xorRot63Ops, List.cons_append, List.nil_append, vrun,
    lane_vbin256, lane_vshift256, h0, h1, h2, h3, h4, ite_false]

/-! ## Diagonals -/

def diagOps : List VOp := [.vpermq x0 x0 0x93, .vpermq x2 x2 0x39, .vpermq x3 x3 0x4e]
def undiagOps : List VOp := [.vpermq x0 x0 0x39, .vpermq x2 x2 0x93, .vpermq x3 x3 0x4e]

theorem sel4_39 {k : Nat} (hk : k < 4) : sel4 (0x39 : BitVec 8).toNat k = (k + 1) % 4 := by
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_4e {k : Nat} (hk : k < 4) : sel4 (0x4e : BitVec 8).toNat k = (k + 2) % 4 := by
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_93 {k : Nat} (hk : k < 4) : sel4 (0x93 : BitVec 8).toNat k = (k + 3) % 4 := by
  rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem diag_words (s : State) : words (vrun diagOps s) = rotIn (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotIn_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) % 4 = (j % 4 + j / 4 + 3) % 4 by omega]
  simp only [diagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [Impl.Argon2.X86_64.Avx2.vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93,
      ↓reduceIte, reduceCtorEq, Nat.add_zero] <;> congr 1 <;> omega

theorem undiag_words (s : State) : words (vrun undiagOps s) = rotOut (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotOut_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) % 4 = (j % 4 + 3 * (j / 4) + 1) % 4 by omega]
  simp only [undiagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [Impl.Argon2.X86_64.Avx2.vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93,
      ↓reduceIte, reduceCtorEq] <;> congr 1 <;> omega

theorem diag_keeps {r : XReg} (h0 : r ≠ x0) (h2 : r ≠ x2) (h3 : r ≠ x3) (s : State) :
    Keeps r s (vrun diagOps s) :=
  ((keeps_vpermq h0 _ _ s).trans (keeps_vpermq h2 _ _ _)).trans (keeps_vpermq h3 _ _ _)

theorem undiag_keeps {r : XReg} (h0 : r ≠ x0) (h2 : r ≠ x2) (h3 : r ≠ x3) (s : State) :
    Keeps r s (vrun undiagOps s) :=
  ((keeps_vpermq h0 _ _ s).trans (keeps_vpermq h2 _ _ _)).trans (keeps_vpermq h3 _ _ _)

/-! ## Columns as words -/

/-- The rows after `G` on each quadword are `mixCols` of the rows before. -/
theorem words_of_cols {s t : State} {x y : Nat → W}
    (h : ∀ k < 4, cols t k = H2 (H1 (cols s k) (x k)) (y k)) : words t = mixCols x y (words s) := by
  apply Vector.ext
  intro j hj
  have g := h (j % 4) (Nat.mod_lt _ (by decide))
  rw [← mix_eq] at g
  simp only [cols] at g
  rw [words_get _ _ hj, mixCols_get _ _ _ _ hj, words_get _ _ (by omega),
    words_get _ _ (by omega), words_get _ _ (by omega), words_get _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [Impl.Argon2.X86_64.Avx2.vreg, VG.Proof.Argon2.mixAt] <;> rw [← g]

/-! ## Gathering the message words -/

theorem src_ok : ∀ j < 16, ∀ q < 4, (src j q).1 ≤ 14 ∧
    (src j q).1 + (if (src j q).2 then 1 - q % 2 else q % 2) = j := by decide

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem qword_shuf_4e (x : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (shufDwords x 0x4e) i = qword x (1 - i) := by
  have e : shufDwords x 0x4e = ofDwords (dword x 2) (dword x 3) (dword x 0) (dword x 1) := by
    simp only [shufDwords]; rfl
  rw [e, qword_ofDwords _ _ _ _ hi, qword_eq]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

/-- What a block of vector code leaves: everything but the vector registers
`rs`. -/
abbrev VF (rs : List XReg) (s t : State) : Prop := YFrame rs s t

theorem lane_same {x : BitVec 128} {q : Nat} :
    (if q / 2 = 0 then x else x) = x := by split <;> rfl

theorem bcast_ok {d : XReg} {j q : Nat} (hj : j < 16) (hq : q < 4) {s : State} {p : Addr}
    (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) :
    WP isa (.block (bcast d j q)) s fun t =>
      qw t d q = s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64 ∧ VF [d] s t := by
  obtain ⟨hb, he⟩ := src_ok j hj q hq
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold bcast
  generalize src j q = sp at hb he
  obtain ⟨b, sw⟩ := sp
  simp only at hb he
  have ld := hrd b hb
  have hea : s.ea (at_ .rsi (8 * b)) = p + BitVec.ofNat 64 (8 * b) := by
    simp only [State.ea, at_, hp, ofInt_natCast]
  have hq' : ∀ i, b + i = j → i < 2 →
      s.mem.readW (p + BitVec.ofNat 64 (8 * b) + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64 := fun i hi _ => by
    rw [Offset.add_add, ← hi, Nat.mul_add]
  cases sw <;> simp only [Bool.false_eq_true, ite_true, ite_false] at he ⊢ <;>
  apply WP.of_runBlock <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, hea, ld, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr l _ => ?_⟩⟩
    · rw [qw_setV256, ite_eq_left_of_eq_true _ _ (eq_true rfl), lane_same, qword_readW128 _ _ h2]
      exact hq' _ he h2
    · simp only [List.mem_singleton] at hr
      simp only [State.lane_setV256, hr, ite_false]
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr l _ => ?_⟩⟩
    · rw [qw_vpshufd, ite_eq_left_of_eq_true _ _ (eq_true rfl), State.lane_setV256,
        ite_eq_left_of_eq_true _ _ (eq_true rfl), lane_same, qword_shuf_4e _ h2,
        qword_readW128 _ _ (by omega)]
      exact hq' _ he (by omega)
    · simp only [List.mem_singleton] at hr
      simp only [lane_vpshufd256, State.lane_setV256, hr, ite_false]

theorem pick2_ff (a b : W) : pick2 a b false false = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pick2, Bool.false_eq_true, ite_false, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

theorem pick2_tt (a b : W) : pick2 a b true true = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pick2, ite_true, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

theorem qw_blend_a (d a b : XReg) (n : BitVec 8) (s : State) {q : Nat} (hq : q < 4)
    (h1 : n.toNat.testBit (2 * q) = false) (h2 : n.toNat.testBit (2 * q + 1) = false) :
    qw ((VOp.vpblendd .l256 d a b n).exec s) d q = qw s a q := by
  simp only [qw_vpblendd _ _ _ _ _ _ hq, ↓reduceIte, h1, h2, pick2_ff]

theorem qw_blend_b (d a b : XReg) (n : BitVec 8) (s : State) {q : Nat} (hq : q < 4)
    (h1 : n.toNat.testBit (2 * q) = true) (h2 : n.toNat.testBit (2 * q + 1) = true) :
    qw ((VOp.vpblendd .l256 d a b n).exec s) d q = qw s b q := by
  simp only [qw_vpblendd _ _ _ _ _ _ hq, ↓reduceIte, h1, h2, pick2_tt]

theorem lane_blend (d a b r : XReg) (n : BitVec 8) (s : State) (hr : r ≠ d) (l : Nat) :
    ((VOp.vpblendd .l256 d a b n).exec s).lane r l = s.lane r l := by
  simp only [VOp.exec, State.lane_setV256, hr, ite_false]

/-- `vpblendd` writes only its destination. -/
theorem VF.blend {rs : List XReg} {d : XReg} (hd : d ∈ rs) (a b : XReg) (n : BitVec 8) (s : State) :
    VF rs s ((VOp.vpblendd .l256 d a b n).exec s) :=
  ⟨VOp.exec_gpr _ s, VOp.exec_mem _ s, VOp.exec_rd _ s, VOp.exec_wr _ s,
    fun r hr l _ => lane_blend _ _ _ _ _ _ (fun h => hr (by subst h; exact hd)) l⟩

theorem qw_eq_of_vf {rs : List XReg} {s t : State} (h : VF rs s t) {r : XReg} (hr : r ∉ rs) {k : Nat}
    (hk : k < 4) : qw t r k = qw s r k := by
  simp only [qw, h.lane r hr (k / 2) (by omega)]

theorem VF.trans {rs : List XReg} {s t u : State} (h : VF rs s t) (h' : VF rs t u) : VF rs s u :=
  YFrame.trans h h'

theorem VF.of_mem {rs rs' : List XReg} {s t : State} (h : VF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    VF rs' s t := YFrame.mono h hs

theorem VF.regs {rs : List XReg} {s t : State} (h : VF rs s t) {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) :
    t.gpr .rsi = p ∧ ∀ i ≤ 14, InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 (8 * i)) 16 :=
  ⟨by rw [h.gpr]; exact hp, by rw [h.rd, h.wr]; exact hrd⟩

/-- The registers `msg` writes. -/
abbrev msgRegs : List XReg := [.xmm5, .xmm6, .xmm7, .xmm8]

theorem blend_ok (d a b : XReg) (n : BitVec 8) (s : State) {Q : State → Prop}
    (h : Q ((VOp.vpblendd .l256 d a b n).exec s)) :
    WP isa (.block [.vop (.vpblendd .l256 d a b n)]) s Q := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact h

/-- Message vector `k` of round `r`, in `ymm5`. -/
theorem msg_ok (r k : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) :
    WP isa (.block (msg r k)) s fun t =>
      (∀ q < 4, qw t .xmm5 q = s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64) ∧
      VF msgRegs s t := by
  have hw : ∀ q, msgWord r k q < 16 := fun q => (Spec.Blake2.sigmaAt _ _).isLt
  simp only [msg, List.append_assoc]
  apply WP.block_append
  refine (bcast_ok (d := .xmm5) (q := 0) (hw 0) (by decide) hp hrd).mono fun t1 h1 => ?_
  obtain ⟨q0, f1⟩ := h1
  obtain ⟨e1, r1⟩ := f1.regs hp hrd
  apply WP.block_append
  refine (bcast_ok (d := .xmm6) (q := 1) (hw 1) (by decide) e1 r1).mono fun t2 h2 => ?_
  obtain ⟨q1, f2⟩ := h2
  obtain ⟨e2, r2⟩ := f2.regs e1 r1
  rw [← List.singleton_append]
  apply WP.block_append
  refine blend_ok _ _ _ _ t2 ?_
  have f3 := VF.blend (rs := [.xmm5]) (List.mem_singleton_self _) .xmm5 .xmm6 0x0c t2
  obtain ⟨e3, r3⟩ := f3.regs e2 r2
  apply WP.block_append
  refine (bcast_ok (d := .xmm7) (q := 2) (hw 2) (by decide) e3 r3).mono fun t4 h4 => ?_
  obtain ⟨q2, f4⟩ := h4
  obtain ⟨e4, r4⟩ := f4.regs e3 r3
  apply WP.block_append
  refine (bcast_ok (d := .xmm8) (q := 3) (hw 3) (by decide) e4 r4).mono fun t5 h5 => ?_
  obtain ⟨q3, f5⟩ := h5
  rw [← List.singleton_append]
  apply WP.block_append
  refine blend_ok _ _ _ _ t5 ?_
  refine blend_ok _ _ _ _ _ ?_
  have f6 := VF.blend (rs := [.xmm7]) (List.mem_singleton_self _) .xmm7 .xmm8 0xc0 t5
  have f7 := VF.blend (rs := [.xmm5]) (List.mem_singleton_self _) .xmm5 .xmm7 0xf0
    ((VOp.vpblendd .l256 .xmm7 .xmm7 .xmm8 0xc0).exec t5)
  have m1 : t1.mem = s.mem := f1.mem
  have m2 : t2.mem = s.mem := f2.mem.trans m1
  have m4 : t4.mem = s.mem := f4.mem.trans (f3.mem.trans m2)
  rw [m1] at q1
  rw [m4] at q3
  rw [f3.mem, m2] at q2
  refine ⟨fun q hq => ?_, ?_⟩
  · rcases VG.Proof.Poly1305.X86_64.Avx2.cases4 hq with rfl | rfl | rfl | rfl
    · rw [qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        qw_eq_of_vf f6 (by decide) (by decide), qw_eq_of_vf f5 (by decide) (by decide),
        qw_eq_of_vf f4 (by decide) (by decide), qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        qw_eq_of_vf f2 (by decide) (by decide), q0]
    · rw [qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        qw_eq_of_vf f6 (by decide) (by decide), qw_eq_of_vf f5 (by decide) (by decide),
        qw_eq_of_vf f4 (by decide) (by decide), qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        q1]
    · rw [qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide), qw_eq_of_vf f5 (by decide) (by decide),
        q2]
    · rw [qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide), q3]
  · exact ((((((f1.of_mem (by decide)).trans (f2.of_mem (by decide))).trans (f3.of_mem (by decide))).trans
      (f4.of_mem (by decide))).trans (f5.of_mem (by decide))).trans (f6.of_mem (by decide))).trans
      (f7.of_mem (by decide))

/-! ## A round -/

/-- The registers a round writes. -/
abbrev roundRegs : List XReg := [x0, x1, x2, x3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8]

theorem block_vops_ok (os : List VOp) (s : State) {Q : State → Prop} (h : Q (vrun os s)) :
    WP isa (.block (os.map .vop)) s Q :=
  WP.of_runBlock ⟨_, runBlock_vops os s, h⟩

theorem VF.vrun {os : List VOp} {rs : List XReg} {s : State}
    (h : ∀ r, r ∉ rs → ∀ l, (vrun os s).lane r l = s.lane r l) : VF rs s (vrun os s) :=
  ⟨vrun_gpr os s, vrun_mem os s, vrun_rd os s, vrun_wr os s, fun r hr l _ => h r hr l⟩

theorem not_mem_half {r : XReg} (h : r ∉ roundRegs) : r ∉ halfRegs := fun h' => h (by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem half1_vf (s : State) : VF roundRegs s (vrun half1Ops s) :=
  VF.vrun fun _ hr => half1_keeps (not_mem_half hr) s

theorem half2_vf (s : State) : VF roundRegs s (vrun half2Ops s) :=
  VF.vrun fun _ hr => half2_keeps (not_mem_half hr) s

theorem ne_of_not_round {r : XReg} (hr : r ∉ roundRegs) : r ≠ x0 ∧ r ≠ x2 ∧ r ≠ x3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)

theorem diag_vf (s : State) : VF roundRegs s (vrun diagOps s) :=
  VF.vrun fun _ hr => diag_keeps (ne_of_not_round hr).1 (ne_of_not_round hr).2.1
    (ne_of_not_round hr).2.2 s

theorem undiag_vf (s : State) : VF roundRegs s (vrun undiagOps s) :=
  VF.vrun fun _ hr => undiag_keeps (ne_of_not_round hr).1 (ne_of_not_round hr).2.1
    (ne_of_not_round hr).2.2 s

theorem masks_of_vf {rs : List XReg} {s t : State} (h : Masks s) (hv : VF rs s t)
    (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Masks t := fun l hl => by
  rw [hv.lane _ h14 l hl, hv.lane _ h15 l hl]; exact h l hl

theorem cols_of_vf {rs : List XReg} {s t : State} (hv : VF rs s t) (h0 : x0 ∉ rs) (h1 : x1 ∉ rs)
    (h2 : x2 ∉ rs) (h3 : x3 ∉ rs) {k : Nat} (hk : k < 4) : cols t k = cols s k := by
  simp only [cols, qw_eq_of_vf hv h0 hk, qw_eq_of_vf hv h1 hk, qw_eq_of_vf hv h2 hk,
    qw_eq_of_vf hv h3 hk]

/-- Word `msgWord r k q` of the block. -/
theorem msg_word (m : Mem) (p : Addr) (r k q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * lane k q + k % 2)) := by
  rw [Proof.Blake2.blockAt_word m p _ (Fin.isLt _), msgWord]

theorem lane_lo {k q : Nat} (hk : k < 2) : lane k q = q := by simp only [lane, hk, ite_true]
theorem lane_hi {k q : Nat} (hk : ¬ k < 2) : lane k q = (q + 3) % 4 := by
  simp only [lane, hk, ite_false]

/-- The first half of `G` on the four quadwords, with the message vector `x`,
and the message vector `y` loaded for the second half, before `D`. -/
theorem g_ok {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s)
    (r k : Nat) (x y : Nat → W)
    (hx : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64 = x q)
    (hy : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r (k + 1) q)) 64 = y q)
    {D : Prog isa} {Q : State → Prop}
    (hD : ∀ s3, VF roundRegs s s3 → Masks s3 → (∀ q < 4, cols s3 q = H1 (cols s q) (x q)) →
      (∀ q < 4, qw s3 .xmm5 q = y q) → WP isa D s3 Q) :
    WP isa (.seq (.block (msg r k)) (.seq (.block half1) (.seq (.block (msg r (k + 1))) D))) s Q := by
  refine WP.seq ((msg_ok r k hp hrd).mono fun s1 ⟨m1, f1⟩ => ?_)
  have hm1 := masks_of_vf hm f1 (by decide) (by decide)
  rw [half1_eq]
  refine WP.seq (block_vops_ok _ _ ?_)
  generalize hs2 : vrun half1Ops s1 = s2
  have f2 : VF roundRegs s1 s2 := hs2 ▸ half1_vf s1
  have c2 : ∀ k < 4, cols s2 k = H1 (cols s1 k) (qw s1 .xmm5 k) := fun k hk => hs2 ▸ half1_cols hm1 hk
  obtain ⟨e2, r2⟩ := VF.regs (VF.trans (f1.of_mem (rs' := roundRegs) (by decide)) f2) hp hrd
  refine WP.seq ((msg_ok r (k + 1) e2 r2).mono fun s3 ⟨m3, f3⟩ => ?_)
  refine hD s3 (((f1.of_mem (by decide)).trans f2).trans (f3.of_mem (by decide)))
    (masks_of_vf (masks_of_vf hm1 f2 (by decide) (by decide)) f3 (by decide) (by decide))
    (fun q hq => ?_) (fun q hq => ?_)
  · rw [cols_of_vf f3 (by decide) (by decide) (by decide) (by decide) hq, c2 q hq,
      cols_of_vf f1 (by decide) (by decide) (by decide) (by decide) hq, m1 q hq, hx q hq]
  · rw [m3 q hq, f2.mem, f1.mem, hy q hq]

/-- The second half of `G`, after `g_ok`. -/
theorem h2_words {s s3 : State} {x y : Nat → W} (hm : Masks s3)
    (hc : ∀ q < 4, cols s3 q = H1 (cols s q) (x q)) (hy : ∀ q < 4, qw s3 .xmm5 q = y q) :
    words (vrun half2Ops s3) = mixCols x y (words s) :=
  words_of_cols fun q hq => by rw [half2_cols hm hq, hc q hq, hy q hq]

theorem half2_diag_eq : half2 ++ diagonalize = (half2Ops ++ diagOps).map .vop := by
  rw [List.map_append]; rfl

theorem half2_undiag_eq : half2 ++ undiagonalize = (half2Ops ++ undiagOps).map .vop := by
  rw [List.map_append]; rfl

theorem msg_lo (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r 0 q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (2 * q)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_lo1 (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r (0 + 1) q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (2 * q + 1)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r 2 q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi1 (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r (2 + 1) q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

/-- Round `r` on the rows in `ymm0`–`ymm3`, with the block at `rsi`. -/
theorem round_ok (r : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s) :
    WP isa (round r) s fun t =>
      words t = Spec.Blake2.round Spec.Blake2.b (Spec.Blake2.blockAt 64 s.mem p) (words s) r ∧
      VF roundRegs s t ∧ Masks t := by
  unfold round
  refine g_ok hp hrd hm r 0 _ _ (fun q _ => msg_lo _ _ r q) (fun q _ => msg_lo1 _ _ r q)
    fun s3 f3 hm3 hc3 hy3 => ?_
  rw [half2_diag_eq]
  refine WP.seq (block_vops_ok _ _ ?_)
  generalize hs4 : vrun (half2Ops ++ diagOps) s3 = s4
  have f4 : VF roundRegs s s4 := by
    rw [← hs4, vrun_append]; exact (f3.trans (half2_vf s3)).trans (diag_vf _)
  have hm4 : Masks s4 := masks_of_vf hm f4 (by decide) (by decide)
  have w4 : words s4 = rotIn (mixCols (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q)))
      (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q + 1))) (words s)) := by
    rw [← hs4, vrun_append, diag_words, h2_words hm3 hc3 hy3]
  obtain ⟨e4, r4⟩ := f4.regs hp hrd
  refine g_ok e4 r4 hm4 r 2
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))))
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))))
    (fun q _ => by rw [f4.mem]; exact msg_hi _ _ r q) (fun q _ => by rw [f4.mem]; exact msg_hi1 _ _ r q)
    fun s7 f7 hm7 hc7 hy7 => ?_
  rw [half2_undiag_eq]
  refine block_vops_ok _ _ ⟨?_, ?_, ?_⟩
  · rw [vrun_append, undiag_words, h2_words hm7 hc7 hy7, w4, round_lanes]
  · rw [vrun_append]; exact ((f4.trans f7).trans (half2_vf s7)).trans (undiag_vf _)
  · rw [vrun_append]
    exact masks_of_vf hm (((f4.trans f7).trans (half2_vf s7)).trans (undiag_vf _)) (by decide) (by decide)

/-- Rounds `0 … n-1`. -/
theorem rounds_ok (n : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s) :
    WP isa (rounds n) s fun t =>
      words t = (List.range n).foldl (Spec.Blake2.round Spec.Blake2.b
        (Spec.Blake2.blockAt 64 s.mem p)) (words s) ∧ VF roundRegs s t ∧ Masks t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _, hm⟩
  | succ n ih =>
    refine WP.seq (ih.mono fun t ⟨wt, ft, mt⟩ => ?_)
    obtain ⟨et, rt⟩ := ft.regs hp hrd
    refine (round_ok n et rt mt).mono fun u ⟨wu, fu, mu⟩ => ⟨?_, ft.trans fu, mu⟩
    rw [wu, wt, ft.mem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Blake2.X86_64.Avx2
