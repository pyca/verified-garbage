import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Blake2.X86_64.Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Blake2.X86_64.Stream
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.X86_64.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Backend

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Round`. -/
section

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
def H1 (v : VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W) (x : VG.Proof.Blake2.X86_64.Avx2.W) : VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W :=
  let a := v.1 + x + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight 32
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight 24
  (a, b, c, d)

/-- `a += y + b; d = (d ^ a) >>> 16; c += d; b = (b ^ c) >>> 63`. -/
def H2 (v : VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W) (y : VG.Proof.Blake2.X86_64.Avx2.W) : VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W :=
  let a := v.1 + y + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight 16
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight 63
  (a, b, c, d)

theorem add_right_comm' (a b c : VG.Proof.Blake2.X86_64.Avx2.W) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc]

theorem mix_eq (va vb vc vd x y : VG.Proof.Blake2.X86_64.Avx2.W) :
    mix Spec.Blake2.b va vb vc vd x y = VG.Proof.Blake2.X86_64.Avx2.H2 (VG.Proof.Blake2.X86_64.Avx2.H1 (va, vb, vc, vd) x) y := by
  simp only [mix, VG.Proof.Blake2.X86_64.Avx2.H1, VG.Proof.Blake2.X86_64.Avx2.H2, Spec.Blake2.b, VG.Proof.Blake2.X86_64.Avx2.add_right_comm' va vb x]
  rw [VG.Proof.Blake2.X86_64.Avx2.add_right_comm' _ _ y]

/-- The quadwords `k` of the four rows. -/
def cols (s : State) (k : Nat) : VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W × VG.Proof.Blake2.X86_64.Avx2.W := (qw s x0 k, qw s x1 k, qw s x2 k, qw s x3 k)

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

theorem vrun_cons_nil (o : VOp) (s : State) : VG.Proof.Argon2.X86_64.Avx2.vrun [o] s = o.exec s := rfl
theorem vrun_pair (o o' : VOp) (s : State) : VG.Proof.Argon2.X86_64.Avx2.vrun [o, o'] s = o'.exec (o.exec s) := rfl

theorem half1_cols {s : State} (h : Masks s) {k : Nat} (hk : k < 4) :
    VG.Proof.Blake2.X86_64.Avx2.cols (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half1Ops s) k = VG.Proof.Blake2.X86_64.Avx2.H1 (VG.Proof.Blake2.X86_64.Avx2.cols s k) (qw s .xmm5 k) := by
  have m3 : Masks ((VOp.vbin .vpaddq .l256 x2 x2 x3).exec (VG.Proof.Argon2.X86_64.Avx2.vrun (xorRot32Ops x3 x0)
      ((VOp.vbin .vpaddq .l256 x0 x0 x1).exec ((VOp.vbin .vpaddq .l256 x0 x0 .xmm5).exec s)))) :=
    (Masks.xorRot32 ((h.vbin (by decide) (by decide)).vbin (by decide) (by decide)) (by decide)
      (by decide)).vbin (by decide) (by decide)
  simp only [VG.Proof.Blake2.X86_64.Avx2.half1Ops, vrun_append, VG.Proof.Blake2.X86_64.Avx2.vrun_cons_nil, VG.Proof.Blake2.X86_64.Avx2.vrun_pair]
  simp (disch := decide) only [VG.Proof.Blake2.X86_64.Avx2.cols, xorRot24_qw (d := x1) (by decide) _ m3 _ hk, xorRot32_qw,
    VG.Proof.Blake2.X86_64.Avx2.qw_add, ↓reduceIte, reduceCtorEq]
  rfl

theorem half2_cols {s : State} (h : Masks s) {k : Nat} (hk : k < 4) :
    VG.Proof.Blake2.X86_64.Avx2.cols (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half2Ops s) k = VG.Proof.Blake2.X86_64.Avx2.H2 (VG.Proof.Blake2.X86_64.Avx2.cols s k) (qw s .xmm5 k) := by
  have m3 : Masks ((VOp.vbin .vpaddq .l256 x0 x0 x1).exec ((VOp.vbin .vpaddq .l256 x0 x0 .xmm5).exec s)) :=
    (h.vbin (by decide) (by decide)).vbin (by decide) (by decide)
  simp only [VG.Proof.Blake2.X86_64.Avx2.half2Ops, vrun_append, VG.Proof.Blake2.X86_64.Avx2.vrun_cons_nil, VG.Proof.Blake2.X86_64.Avx2.vrun_pair]
  simp (disch := decide) only [VG.Proof.Blake2.X86_64.Avx2.cols, xorRot63_qw (d := x1) (by decide), xorRot16_qw (d := x3)
    (by decide) _ m3 _ hk, VG.Proof.Blake2.X86_64.Avx2.qw_add, ↓reduceIte, reduceCtorEq]
  rfl

/-! ## The registers each block leaves alone -/

/-- The lanes of `r` are those of `s`. -/
def Keeps (r : XReg) (s t : State) : Prop := ∀ l, t.lane r l = s.lane r l

theorem keeps_vpermq {r d : XReg} (h : r ≠ d) (a : XReg) (o : BitVec 8) (s : State) :
    VG.Proof.Blake2.X86_64.Avx2.Keeps r s ((VOp.vpermq d a o).exec s) := fun _ =>
  VG.Proof.Argon2.X86_64.Avx2.lane_vpermq _ _ _ _ _ h

theorem Keeps.trans {r : XReg} {s t u : State} (h : VG.Proof.Blake2.X86_64.Avx2.Keeps r s t) (h' : VG.Proof.Blake2.X86_64.Avx2.Keeps r t u) : VG.Proof.Blake2.X86_64.Avx2.Keeps r s u :=
  fun l => (h' l).trans (h l)

/-- The registers `half1Ops` and `half2Ops` write. -/
def halfRegs : List XReg := [x0, x1, x2, x3, .xmm4]

theorem half1_keeps {r : XReg} (hr : r ∉ VG.Proof.Blake2.X86_64.Avx2.halfRegs) (s : State) : VG.Proof.Blake2.X86_64.Avx2.Keeps r s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half1Ops s) := by
  simp only [VG.Proof.Blake2.X86_64.Avx2.halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, -⟩ := hr
  intro l
  simp only [VG.Proof.Blake2.X86_64.Avx2.half1Ops, xorRot32Ops, xorRot24Ops, List.cons_append, List.nil_append, VG.Proof.Argon2.X86_64.Avx2.vrun,
    lane_vbin256, lane_vpshufd256, h0, h1, h2, h3, ite_false]

theorem half2_keeps {r : XReg} (hr : r ∉ VG.Proof.Blake2.X86_64.Avx2.halfRegs) (s : State) : VG.Proof.Blake2.X86_64.Avx2.Keeps r s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half2Ops s) := by
  simp only [VG.Proof.Blake2.X86_64.Avx2.halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  intro l
  simp only [VG.Proof.Blake2.X86_64.Avx2.half2Ops, xorRot16Ops, xorRot63Ops, List.cons_append, List.nil_append, VG.Proof.Argon2.X86_64.Avx2.vrun,
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

theorem diag_words (s : State) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.diagOps s) = rotIn (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotIn_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) % 4 = (j % 4 + j / 4 + 3) % 4 by omega]
  simp only [VG.Proof.Blake2.X86_64.Avx2.diagOps, VG.Proof.Argon2.X86_64.Avx2.vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [Impl.Argon2.X86_64.Avx2.vreg, qw_vpermq, VG.Proof.Blake2.X86_64.Avx2.sel4_39, VG.Proof.Blake2.X86_64.Avx2.sel4_4e, VG.Proof.Blake2.X86_64.Avx2.sel4_93,
      ↓reduceIte, reduceCtorEq, Nat.add_zero] <;> congr 1 <;> omega

theorem undiag_words (s : State) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.undiagOps s) = rotOut (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotOut_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) % 4 = (j % 4 + 3 * (j / 4) + 1) % 4 by omega]
  simp only [VG.Proof.Blake2.X86_64.Avx2.undiagOps, VG.Proof.Argon2.X86_64.Avx2.vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [Impl.Argon2.X86_64.Avx2.vreg, qw_vpermq, VG.Proof.Blake2.X86_64.Avx2.sel4_39, VG.Proof.Blake2.X86_64.Avx2.sel4_4e, VG.Proof.Blake2.X86_64.Avx2.sel4_93,
      ↓reduceIte, reduceCtorEq] <;> congr 1 <;> omega

theorem diag_keeps {r : XReg} (h0 : r ≠ x0) (h2 : r ≠ x2) (h3 : r ≠ x3) (s : State) :
    VG.Proof.Blake2.X86_64.Avx2.Keeps r s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.diagOps s) :=
  ((VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h0 _ _ s).trans (VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h2 _ _ _)).trans (VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h3 _ _ _)

theorem undiag_keeps {r : XReg} (h0 : r ≠ x0) (h2 : r ≠ x2) (h3 : r ≠ x3) (s : State) :
    VG.Proof.Blake2.X86_64.Avx2.Keeps r s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.undiagOps s) :=
  ((VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h0 _ _ s).trans (VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h2 _ _ _)).trans (VG.Proof.Blake2.X86_64.Avx2.keeps_vpermq h3 _ _ _)

/-! ## Columns as words -/

/-- The rows after `G` on each quadword are `mixCols` of the rows before. -/
theorem words_of_cols {s t : State} {x y : Nat → VG.Proof.Blake2.X86_64.Avx2.W}
    (h : ∀ k < 4, VG.Proof.Blake2.X86_64.Avx2.cols t k = VG.Proof.Blake2.X86_64.Avx2.H2 (VG.Proof.Blake2.X86_64.Avx2.H1 (VG.Proof.Blake2.X86_64.Avx2.cols s k) (x k)) (y k)) : VG.Proof.Argon2.X86_64.Avx2.words t = mixCols x y (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have g := h (j % 4) (Nat.mod_lt _ (by decide))
  rw [← VG.Proof.Blake2.X86_64.Avx2.mix_eq] at g
  simp only [VG.Proof.Blake2.X86_64.Avx2.cols] at g
  rw [words_get _ _ hj, mixCols_get _ _ _ _ hj, words_get _ _ (by omega),
    words_get _ _ (by omega), words_get _ _ (by omega), words_get _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [Impl.Argon2.X86_64.Avx2.vreg, VG.Proof.Argon2.mixAt] <;> rw [← g]

/-! ## Gathering the message words -/

theorem src_ok : ∀ j < 16, ∀ q < 4, (VG.Impl.Blake2.X86_64.Avx2.src j q).1 ≤ 14 ∧
    (VG.Impl.Blake2.X86_64.Avx2.src j q).1 + (if (VG.Impl.Blake2.X86_64.Avx2.src j q).2 then 1 - q % 2 else q % 2) = j := by decide

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
      qw t d q = s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64 ∧ VG.Proof.Blake2.X86_64.Avx2.VF [d] s t := by
  obtain ⟨hb, he⟩ := VG.Proof.Blake2.X86_64.Avx2.src_ok j hj q hq
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold bcast
  generalize VG.Impl.Blake2.X86_64.Avx2.src j q = sp at hb he
  obtain ⟨b, sw⟩ := sp
  simp only at hb he
  have ld := hrd b hb
  have hea : s.ea (VG.Impl.Blake2.X86_64.at_ .rsi (8 * b)) = p + BitVec.ofNat 64 (8 * b) := by
    simp only [State.ea, VG.Impl.Blake2.X86_64.at_, hp, VG.Proof.Blake2.X86_64.Avx2.ofInt_natCast]
  have hq' : ∀ i, b + i = j → i < 2 →
      s.mem.readW (p + BitVec.ofNat 64 (8 * b) + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64 := fun i hi _ => by
    rw [Offset.add_add, ← hi, Nat.mul_add]
  cases sw <;> simp only [Bool.false_eq_true, ite_true, ite_false] at he ⊢ <;>
  apply WP.of_runBlock <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, hea, ld, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr l _ => ?_⟩⟩
    · rw [qw_setV256, ite_eq_left_of_eq_true _ _ (eq_true rfl), VG.Proof.Blake2.X86_64.Avx2.lane_same, qword_readW128 _ _ h2]
      exact hq' _ he h2
    · simp only [List.mem_singleton] at hr
      simp only [State.lane_setV256, hr, ite_false]
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr l _ => ?_⟩⟩
    · rw [qw_vpshufd, ite_eq_left_of_eq_true _ _ (eq_true rfl), State.lane_setV256,
        ite_eq_left_of_eq_true _ _ (eq_true rfl), VG.Proof.Blake2.X86_64.Avx2.lane_same, VG.Proof.Blake2.X86_64.Avx2.qword_shuf_4e _ h2,
        qword_readW128 _ _ (by omega)]
      exact hq' _ he (by omega)
    · simp only [List.mem_singleton] at hr
      simp only [lane_vpshufd256, State.lane_setV256, hr, ite_false]

theorem pick2_ff (a b : VG.Proof.Blake2.X86_64.Avx2.W) : pick2 a b false false = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pick2, Bool.false_eq_true, ite_false, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

theorem pick2_tt (a b : VG.Proof.Blake2.X86_64.Avx2.W) : pick2 a b true true = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pick2, ite_true, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

theorem qw_blend_a (d a b : XReg) (n : BitVec 8) (s : State) {q : Nat} (hq : q < 4)
    (h1 : n.toNat.testBit (2 * q) = false) (h2 : n.toNat.testBit (2 * q + 1) = false) :
    qw ((VOp.vpblendd .l256 d a b n).exec s) d q = qw s a q := by
  simp only [qw_vpblendd _ _ _ _ _ _ hq, ↓reduceIte, h1, h2, VG.Proof.Blake2.X86_64.Avx2.pick2_ff]

theorem qw_blend_b (d a b : XReg) (n : BitVec 8) (s : State) {q : Nat} (hq : q < 4)
    (h1 : n.toNat.testBit (2 * q) = true) (h2 : n.toNat.testBit (2 * q + 1) = true) :
    qw ((VOp.vpblendd .l256 d a b n).exec s) d q = qw s b q := by
  simp only [qw_vpblendd _ _ _ _ _ _ hq, ↓reduceIte, h1, h2, VG.Proof.Blake2.X86_64.Avx2.pick2_tt]

theorem lane_blend (d a b r : XReg) (n : BitVec 8) (s : State) (hr : r ≠ d) (l : Nat) :
    ((VOp.vpblendd .l256 d a b n).exec s).lane r l = s.lane r l := by
  simp only [VOp.exec, State.lane_setV256, hr, ite_false]

/-- `vpblendd` writes only its destination. -/
theorem VF.blend {rs : List XReg} {d : XReg} (hd : d ∈ rs) (a b : XReg) (n : BitVec 8) (s : State) :
    VG.Proof.Blake2.X86_64.Avx2.VF rs s ((VOp.vpblendd .l256 d a b n).exec s) :=
  ⟨VOp.exec_gpr _ s, VOp.exec_mem _ s, VOp.exec_rd _ s, VOp.exec_wr _ s,
    fun r hr l _ => VG.Proof.Blake2.X86_64.Avx2.lane_blend _ _ _ _ _ _ (fun h => hr (by subst h; exact hd)) l⟩

theorem qw_eq_of_vf {rs : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.VF rs s t) {r : XReg} (hr : r ∉ rs) {k : Nat}
    (hk : k < 4) : qw t r k = qw s r k := by
  simp only [qw, h.lane r hr (k / 2) (by omega)]

theorem VF.trans {rs : List XReg} {s t u : State} (h : VG.Proof.Blake2.X86_64.Avx2.VF rs s t) (h' : VG.Proof.Blake2.X86_64.Avx2.VF rs t u) : VG.Proof.Blake2.X86_64.Avx2.VF rs s u :=
  YFrame.trans h h'

theorem VF.of_mem {rs rs' : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.VF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Blake2.X86_64.Avx2.VF rs' s t := YFrame.mono h hs

theorem VF.regs {rs : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.VF rs s t) {p : Addr} (hp : s.gpr .rsi = p)
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
      VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.msgRegs s t := by
  have hw : ∀ q, msgWord r k q < 16 := fun q => (Spec.Blake2.sigmaAt _ _).isLt
  simp only [msg, List.append_assoc]
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.bcast_ok (d := .xmm5) (q := 0) (hw 0) (by decide) hp hrd).mono fun t1 h1 => ?_
  obtain ⟨q0, f1⟩ := h1
  obtain ⟨e1, r1⟩ := f1.regs hp hrd
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.bcast_ok (d := .xmm6) (q := 1) (hw 1) (by decide) e1 r1).mono fun t2 h2 => ?_
  obtain ⟨q1, f2⟩ := h2
  obtain ⟨e2, r2⟩ := f2.regs e1 r1
  rw [← List.singleton_append]
  apply WP.block_append
  refine VG.Proof.Blake2.X86_64.Avx2.blend_ok _ _ _ _ t2 ?_
  have f3 := VF.blend (rs := [.xmm5]) (List.mem_singleton_self _) .xmm5 .xmm6 0x0c t2
  obtain ⟨e3, r3⟩ := f3.regs e2 r2
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.bcast_ok (d := .xmm7) (q := 2) (hw 2) (by decide) e3 r3).mono fun t4 h4 => ?_
  obtain ⟨q2, f4⟩ := h4
  obtain ⟨e4, r4⟩ := f4.regs e3 r3
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.bcast_ok (d := .xmm8) (q := 3) (hw 3) (by decide) e4 r4).mono fun t5 h5 => ?_
  obtain ⟨q3, f5⟩ := h5
  rw [← List.singleton_append]
  apply WP.block_append
  refine VG.Proof.Blake2.X86_64.Avx2.blend_ok _ _ _ _ t5 ?_
  refine VG.Proof.Blake2.X86_64.Avx2.blend_ok _ _ _ _ _ ?_
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
    · rw [VG.Proof.Blake2.X86_64.Avx2.qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f6 (by decide) (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f5 (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f4 (by decide) (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f2 (by decide) (by decide), q0]
    · rw [VG.Proof.Blake2.X86_64.Avx2.qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f6 (by decide) (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f5 (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f4 (by decide) (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        q1]
    · rw [VG.Proof.Blake2.X86_64.Avx2.qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_blend_a _ _ _ _ _ (by decide) (by decide) (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf f5 (by decide) (by decide),
        q2]
    · rw [VG.Proof.Blake2.X86_64.Avx2.qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.X86_64.Avx2.qw_blend_b _ _ _ _ _ (by decide) (by decide) (by decide), q3]
  · exact ((((((f1.of_mem (by decide)).trans (f2.of_mem (by decide))).trans (f3.of_mem (by decide))).trans
      (f4.of_mem (by decide))).trans (f5.of_mem (by decide))).trans (f6.of_mem (by decide))).trans
      (f7.of_mem (by decide))

/-! ## A round -/

/-- The registers a round writes. -/
abbrev roundRegs : List XReg := [x0, x1, x2, x3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8]

theorem block_vops_ok (os : List VOp) (s : State) {Q : State → Prop} (h : Q (VG.Proof.Argon2.X86_64.Avx2.vrun os s)) :
    WP isa (.block (os.map .vop)) s Q :=
  WP.of_runBlock ⟨_, runBlock_vops os s, h⟩

theorem VF.vrun {os : List VOp} {rs : List XReg} {s : State}
    (h : ∀ r, r ∉ rs → ∀ l, (VG.Proof.Argon2.X86_64.Avx2.vrun os s).lane r l = s.lane r l) : VG.Proof.Blake2.X86_64.Avx2.VF rs s (VG.Proof.Argon2.X86_64.Avx2.vrun os s) :=
  ⟨vrun_gpr os s, vrun_mem os s, vrun_rd os s, vrun_wr os s, fun r hr l _ => h r hr l⟩

theorem not_mem_half {r : XReg} (h : r ∉ VG.Proof.Blake2.X86_64.Avx2.roundRegs) : r ∉ VG.Proof.Blake2.X86_64.Avx2.halfRegs := fun h' => h (by
  simp only [VG.Proof.Blake2.X86_64.Avx2.halfRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem half1_vf (s : State) : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half1Ops s) :=
  VF.vrun fun _ hr => VG.Proof.Blake2.X86_64.Avx2.half1_keeps (VG.Proof.Blake2.X86_64.Avx2.not_mem_half hr) s

theorem half2_vf (s : State) : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half2Ops s) :=
  VF.vrun fun _ hr => VG.Proof.Blake2.X86_64.Avx2.half2_keeps (VG.Proof.Blake2.X86_64.Avx2.not_mem_half hr) s

theorem ne_of_not_round {r : XReg} (hr : r ∉ VG.Proof.Blake2.X86_64.Avx2.roundRegs) : r ≠ x0 ∧ r ≠ x2 ∧ r ≠ x3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)

theorem diag_vf (s : State) : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.diagOps s) :=
  VF.vrun fun _ hr => VG.Proof.Blake2.X86_64.Avx2.diag_keeps (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).1 (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).2.1
    (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).2.2 s

theorem undiag_vf (s : State) : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.undiagOps s) :=
  VF.vrun fun _ hr => VG.Proof.Blake2.X86_64.Avx2.undiag_keeps (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).1 (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).2.1
    (VG.Proof.Blake2.X86_64.Avx2.ne_of_not_round hr).2.2 s

theorem masks_of_vf {rs : List XReg} {s t : State} (h : Masks s) (hv : VG.Proof.Blake2.X86_64.Avx2.VF rs s t)
    (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Masks t := fun l hl => by
  rw [hv.lane _ h14 l hl, hv.lane _ h15 l hl]; exact h l hl

theorem cols_of_vf {rs : List XReg} {s t : State} (hv : VG.Proof.Blake2.X86_64.Avx2.VF rs s t) (h0 : x0 ∉ rs) (h1 : x1 ∉ rs)
    (h2 : x2 ∉ rs) (h3 : x3 ∉ rs) {k : Nat} (hk : k < 4) : VG.Proof.Blake2.X86_64.Avx2.cols t k = VG.Proof.Blake2.X86_64.Avx2.cols s k := by
  simp only [VG.Proof.Blake2.X86_64.Avx2.cols, VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h0 hk, VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h1 hk, VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h2 hk,
    VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h3 hk]

/-- Word `msgWord r k q` of the block. -/
theorem msg_word (m : Mem) (p : Addr) (r k q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * VG.Impl.Blake2.X86_64.Avx2.lane k q + k % 2)) := by
  rw [Proof.Blake2.blockAt_word m p _ (Fin.isLt _), msgWord]

theorem lane_lo {k q : Nat} (hk : k < 2) : VG.Impl.Blake2.X86_64.Avx2.lane k q = q := by simp only [VG.Impl.Blake2.X86_64.Avx2.lane, hk, ite_true]
theorem lane_hi {k q : Nat} (hk : ¬ k < 2) : VG.Impl.Blake2.X86_64.Avx2.lane k q = (q + 3) % 4 := by
  simp only [VG.Impl.Blake2.X86_64.Avx2.lane, hk, ite_false]

/-- The first half of `G` on the four quadwords, with the message vector `x`,
and the message vector `y` loaded for the second half, before `D`. -/
theorem g_ok {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s)
    (r k : Nat) (x y : Nat → VG.Proof.Blake2.X86_64.Avx2.W)
    (hx : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64 = x q)
    (hy : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r (k + 1) q)) 64 = y q)
    {D : Prog isa} {Q : State → Prop}
    (hD : ∀ s3, VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s s3 → Masks s3 → (∀ q < 4, VG.Proof.Blake2.X86_64.Avx2.cols s3 q = VG.Proof.Blake2.X86_64.Avx2.H1 (VG.Proof.Blake2.X86_64.Avx2.cols s q) (x q)) →
      (∀ q < 4, qw s3 .xmm5 q = y q) → WP isa D s3 Q) :
    WP isa (.seq (.block (msg r k)) (.seq (.block half1) (.seq (.block (msg r (k + 1))) D))) s Q := by
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.msg_ok r k hp hrd).mono fun s1 ⟨m1, f1⟩ => ?_)
  have hm1 := VG.Proof.Blake2.X86_64.Avx2.masks_of_vf hm f1 (by decide) (by decide)
  rw [VG.Proof.Blake2.X86_64.Avx2.half1_eq]
  refine WP.seq (VG.Proof.Blake2.X86_64.Avx2.block_vops_ok _ _ ?_)
  generalize hs2 : VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half1Ops s1 = s2
  have f2 : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s1 s2 := hs2 ▸ VG.Proof.Blake2.X86_64.Avx2.half1_vf s1
  have c2 : ∀ k < 4, VG.Proof.Blake2.X86_64.Avx2.cols s2 k = VG.Proof.Blake2.X86_64.Avx2.H1 (VG.Proof.Blake2.X86_64.Avx2.cols s1 k) (qw s1 .xmm5 k) := fun k hk => hs2 ▸ VG.Proof.Blake2.X86_64.Avx2.half1_cols hm1 hk
  obtain ⟨e2, r2⟩ := VF.regs (VF.trans (f1.of_mem (rs' := VG.Proof.Blake2.X86_64.Avx2.roundRegs) (by decide)) f2) hp hrd
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.msg_ok r (k + 1) e2 r2).mono fun s3 ⟨m3, f3⟩ => ?_)
  refine hD s3 (((f1.of_mem (by decide)).trans f2).trans (f3.of_mem (by decide)))
    (VG.Proof.Blake2.X86_64.Avx2.masks_of_vf (VG.Proof.Blake2.X86_64.Avx2.masks_of_vf hm1 f2 (by decide) (by decide)) f3 (by decide) (by decide))
    (fun q hq => ?_) (fun q hq => ?_)
  · rw [VG.Proof.Blake2.X86_64.Avx2.cols_of_vf f3 (by decide) (by decide) (by decide) (by decide) hq, c2 q hq,
      VG.Proof.Blake2.X86_64.Avx2.cols_of_vf f1 (by decide) (by decide) (by decide) (by decide) hq, m1 q hq, hx q hq]
  · rw [m3 q hq, f2.mem, f1.mem, hy q hq]

/-- The second half of `G`, after `g_ok`. -/
theorem h2_words {s s3 : State} {x y : Nat → VG.Proof.Blake2.X86_64.Avx2.W} (hm : Masks s3)
    (hc : ∀ q < 4, VG.Proof.Blake2.X86_64.Avx2.cols s3 q = VG.Proof.Blake2.X86_64.Avx2.H1 (VG.Proof.Blake2.X86_64.Avx2.cols s q) (x q)) (hy : ∀ q < 4, qw s3 .xmm5 q = y q) :
    VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.half2Ops s3) = mixCols x y (VG.Proof.Argon2.X86_64.Avx2.words s) :=
  VG.Proof.Blake2.X86_64.Avx2.words_of_cols fun q hq => by rw [VG.Proof.Blake2.X86_64.Avx2.half2_cols hm hq, hc q hq, hy q hq]

theorem half2_diag_eq : half2 ++ diagonalize = (VG.Proof.Blake2.X86_64.Avx2.half2Ops ++ VG.Proof.Blake2.X86_64.Avx2.diagOps).map .vop := by
  rw [List.map_append]; rfl

theorem half2_undiag_eq : half2 ++ undiagonalize = (VG.Proof.Blake2.X86_64.Avx2.half2Ops ++ VG.Proof.Blake2.X86_64.Avx2.undiagOps).map .vop := by
  rw [List.map_append]; rfl

theorem msg_lo (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r 0 q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (2 * q)) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.msg_word, VG.Proof.Blake2.X86_64.Avx2.lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_lo1 (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r (0 + 1) q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (2 * q + 1)) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.msg_word, VG.Proof.Blake2.X86_64.Avx2.lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r 2 q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.msg_word, VG.Proof.Blake2.X86_64.Avx2.lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi1 (m : Mem) (p : Addr) (r q : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * msgWord r (2 + 1) q)) 64 =
      Spec.Blake2.blockAt 64 m p (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.msg_word, VG.Proof.Blake2.X86_64.Avx2.lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

/-- Round `r` on the rows in `ymm0`–`ymm3`, with the block at `rsi`. -/
theorem round_ok (r : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s) :
    WP isa (VG.Impl.Blake2.X86_64.Avx2.round r) s fun t =>
      VG.Proof.Argon2.X86_64.Avx2.words t = Spec.Blake2.round Spec.Blake2.b (Spec.Blake2.blockAt 64 s.mem p) (VG.Proof.Argon2.X86_64.Avx2.words s) r ∧
      VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s t ∧ Masks t := by
  unfold VG.Impl.Blake2.X86_64.Avx2.round
  refine VG.Proof.Blake2.X86_64.Avx2.g_ok hp hrd hm r 0 _ _ (fun q _ => VG.Proof.Blake2.X86_64.Avx2.msg_lo _ _ r q) (fun q _ => VG.Proof.Blake2.X86_64.Avx2.msg_lo1 _ _ r q)
    fun s3 f3 hm3 hc3 hy3 => ?_
  rw [VG.Proof.Blake2.X86_64.Avx2.half2_diag_eq]
  refine WP.seq (VG.Proof.Blake2.X86_64.Avx2.block_vops_ok _ _ ?_)
  generalize hs4 : VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Blake2.X86_64.Avx2.half2Ops ++ VG.Proof.Blake2.X86_64.Avx2.diagOps) s3 = s4
  have f4 : VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s s4 := by
    rw [← hs4, vrun_append]; exact (f3.trans (VG.Proof.Blake2.X86_64.Avx2.half2_vf s3)).trans (VG.Proof.Blake2.X86_64.Avx2.diag_vf _)
  have hm4 : Masks s4 := VG.Proof.Blake2.X86_64.Avx2.masks_of_vf hm f4 (by decide) (by decide)
  have w4 : VG.Proof.Argon2.X86_64.Avx2.words s4 = rotIn (mixCols (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q)))
      (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q + 1))) (VG.Proof.Argon2.X86_64.Avx2.words s)) := by
    rw [← hs4, vrun_append, VG.Proof.Blake2.X86_64.Avx2.diag_words, VG.Proof.Blake2.X86_64.Avx2.h2_words hm3 hc3 hy3]
  obtain ⟨e4, r4⟩ := f4.regs hp hrd
  refine VG.Proof.Blake2.X86_64.Avx2.g_ok e4 r4 hm4 r 2
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))))
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))))
    (fun q _ => by rw [f4.mem]; exact VG.Proof.Blake2.X86_64.Avx2.msg_hi _ _ r q) (fun q _ => by rw [f4.mem]; exact VG.Proof.Blake2.X86_64.Avx2.msg_hi1 _ _ r q)
    fun s7 f7 hm7 hc7 hy7 => ?_
  rw [VG.Proof.Blake2.X86_64.Avx2.half2_undiag_eq]
  refine VG.Proof.Blake2.X86_64.Avx2.block_vops_ok _ _ ⟨?_, ?_, ?_⟩
  · rw [vrun_append, VG.Proof.Blake2.X86_64.Avx2.undiag_words, VG.Proof.Blake2.X86_64.Avx2.h2_words hm7 hc7 hy7, w4, round_lanes]
  · rw [vrun_append]; exact ((f4.trans f7).trans (VG.Proof.Blake2.X86_64.Avx2.half2_vf s7)).trans (VG.Proof.Blake2.X86_64.Avx2.undiag_vf _)
  · rw [vrun_append]
    exact VG.Proof.Blake2.X86_64.Avx2.masks_of_vf hm (((f4.trans f7).trans (VG.Proof.Blake2.X86_64.Avx2.half2_vf s7)).trans (VG.Proof.Blake2.X86_64.Avx2.undiag_vf _)) (by decide) (by decide)

/-- Rounds `0 … n-1`. -/
theorem rounds_ok (n : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) (hm : Masks s) :
    WP isa (VG.Impl.Blake2.X86_64.Avx2.rounds n) s fun t =>
      VG.Proof.Argon2.X86_64.Avx2.words t = (List.range n).foldl (Spec.Blake2.round Spec.Blake2.b
        (Spec.Blake2.blockAt 64 s.mem p)) (VG.Proof.Argon2.X86_64.Avx2.words s) ∧ VG.Proof.Blake2.X86_64.Avx2.VF VG.Proof.Blake2.X86_64.Avx2.roundRegs s t ∧ Masks t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _, hm⟩
  | succ n ih =>
    refine WP.seq (ih.mono fun t ⟨wt, ft, mt⟩ => ?_)
    obtain ⟨et, rt⟩ := ft.regs hp hrd
    refine (VG.Proof.Blake2.X86_64.Avx2.round_ok n et rt mt).mono fun u ⟨wu, fu, mu⟩ => ⟨?_, ft.trans fu, mu⟩
    rw [wu, wt, ft.mem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Blake2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Lit`. -/
section

/-!
# BLAKE2b on x86-64 with AVX2: the code as literals

The compression function, and the streaming `update` and `finalize` calling
it (`avx2`, the callee they are emitted with), as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG.Proof.Blake2.X86_64.Avx2

/-- The compression function, as the streaming functions call it. -/
def avx2 : Impl.Blake2.X86_64.Stream.Callee :=
  ⟨Spec.Blake2.compressBApi.name ++ "_avx2", Impl.Blake2.X86_64.Avx2.compress⟩

materialize_code compressY := Impl.Blake2.X86_64.Avx2.compress
materialize_code updateY := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b VG.Proof.Blake2.X86_64.Avx2.avx2
materialize_code finalizeY := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b VG.Proof.Blake2.X86_64.Avx2.avx2

end VG.Proof.Blake2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress`. -/
section

/-!
# BLAKE2b compression function on x86-64 with AVX2

The proof that `Impl.Blake2.X86_64.Avx2.compress` meets `compressX86_64 b`
(`Proof/Blake2/X86_64/Contract.lean`), as the scalar code does
(`Proof/Blake2/X86_64/Compress.lean`, whose description of the precondition
and of the work vector before the rounds, `V0`, this proof shares): the
masks and the IV in registers (`setup_ok`), then for each block the work
vector (`init_ok`), the rounds (`rounds_ok`), the XOR into the state
(`finish_ok`) and the next block (`advance_ok`). Constant time is checked
by evaluation.
-/

namespace VG.Proof.Blake2.X86_64.Avx2

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx2
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2.X86_64 (Pre pre_of stA bpA nb t₀ fl scA stR blR H₀ blkAddr V0 V0_get F_eq
  flagW stateAt_get carry_ofNat zf_last τ₀ agree₀ satState off off_eq)
open VG.Proof.Argon2.X86_64.Avx2 (vrun Masks words words_get cases_div4 x0 x1 x2 x3 ifp ifn
  read_write256)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qw_vbin qw_lane qw_setV256 qw_setV128 qword_punpcklqdq
  qw_vmovq cases4)

/-- Word `q` of BLAKE2b's IV. -/
def ivAt (q : Nat) : VG.Proof.Blake2.X86_64.Avx2.W := if h : q < 8 then Spec.Blake2.b.IV[q] else 0

/-- The masks and the IV, in their registers. -/
structure Consts (s : State) : Prop where
  masks : Masks s
  iv0 : ∀ q < 4, qw s .xmm11 q = VG.Proof.Blake2.X86_64.Avx2.ivAt q
  iv1 : ∀ q < 4, qw s .xmm12 q = VG.Proof.Blake2.X86_64.Avx2.ivAt (4 + q)

theorem Consts.of_vf {rs : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.Consts s) (hv : VG.Proof.Blake2.X86_64.Avx2.VF rs s t)
    (h11 : .xmm11 ∉ rs) (h12 : .xmm12 ∉ rs) (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : VG.Proof.Blake2.X86_64.Avx2.Consts t :=
  ⟨VG.Proof.Blake2.X86_64.Avx2.masks_of_vf h.masks hv h14 h15, fun q hq => (VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h11 hq).trans (h.iv0 q hq),
    fun q hq => (VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_vf hv h12 hq).trans (h.iv1 q hq)⟩

/-! ## Quadwords of registers after the other instructions -/

/-- What the set-up code leaves: everything but `rax`, the flags and the
vector registers `rs`. -/
structure SF (rs : List XReg) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  lane : ∀ r, r ∉ rs → ∀ l, t.lane r l = s.lane r l

theorem SF.trans {rs : List XReg} {s t u : State} (h : VG.Proof.Blake2.X86_64.Avx2.SF rs s t) (h' : VG.Proof.Blake2.X86_64.Avx2.SF rs t u) : VG.Proof.Blake2.X86_64.Avx2.SF rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr l => (h'.lane r hr l).trans (h.lane r hr l)⟩

theorem SF.of_mem {rs rs' : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.SF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Blake2.X86_64.Avx2.SF rs' s t := ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.lane r fun h' => hr (hs r h')⟩

theorem qw_eq_of_sf {rs : List XReg} {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.SF rs s t) {r : XReg} (hr : r ∉ rs) (k : Nat) :
    qw t r k = qw s r k := by
  simp only [qw, h.lane r hr (k / 2)]

theorem unpck_eq (lo hi : VG.Proof.Blake2.X86_64.Avx2.W) :
    XBinOp.punpcklqdq.eval ((0 : VG.Proof.Blake2.X86_64.Avx2.W) ++ lo) ((0 : VG.Proof.Blake2.X86_64.Avx2.W) ++ hi) = hi ++ lo := by
  apply VG.Proof.Argon2.X86_64.Avx2.eq_of_qwords <;>
    simp only [qword_punpcklqdq _ _ (show 0 < 2 by decide), qword_punpcklqdq _ _ (show 1 < 2 by decide),
      VG.Proof.Poly1305.X86_64.Avx2.qword_app0, VG.Proof.Poly1305.X86_64.Avx2.qword_app1,
      ↓reduceIte, Nat.one_ne_zero]

/-- `d := (lo, hi)` in its low 128 bits, through `rax` and `t`. -/
theorem pair_ok {d t : XReg} (hdt : d ≠ t) (lo hi : VG.Proof.Blake2.X86_64.Avx2.W) (s : State) :
    WP isa (.block (pair d t lo hi)) s fun u =>
      u.lane d 0 = hi ++ lo ∧ u.lane d 1 = 0 ∧ VG.Proof.Blake2.X86_64.Avx2.SF [d, t] s u := by
  apply WP.of_runBlock
  simp only [pair, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr l => ?_⟩⟩
  · simp only [VOp.exec, State.lane_setV128, RegUpd.gpr_setReg, ↓reduceIte, hdt,
      VG.Proof.Argon2.X86_64.Avx2.lane_setReg, VBinOp.sse]
    exact VG.Proof.Blake2.X86_64.Avx2.unpck_eq lo hi
  · simp only [VOp.exec, State.lane_setV128, ↓reduceIte, VG.Proof.Argon2.X86_64.Avx2.lane_setReg,
      Nat.one_ne_zero]
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [VOp.exec_mem, RegUpd.mem_setReg]
  · simp only [VOp.exec_rd, RegUpd.rd_setReg]
  · simp only [VOp.exec_wr, RegUpd.wr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VOp.exec, State.lane_setV128, VG.Proof.Argon2.X86_64.Avx2.lane_setReg, hr.1, hr.2,
      ite_false]

theorem qw_of_lanes {s : State} {r : XReg} {a b c e : VG.Proof.Blake2.X86_64.Avx2.W} (h0 : s.lane r 0 = b ++ a)
    (h1 : s.lane r 1 = e ++ c) :
    qw s r 0 = a ∧ qw s r 1 = b ∧ qw s r 2 = c ∧ qw s r 3 = e := by
  simp only [qw, Nat.reduceDiv, Nat.reduceMod, h0, h1, VG.Proof.Poly1305.X86_64.Avx2.qword_app0,
    VG.Proof.Poly1305.X86_64.Avx2.qword_app1, and_self]

/-- `d := (a, b, c, e)`, through `rax`, `ymm10` and `ymm13`. -/
theorem quad_ok {d : XReg} (hd10 : d ≠ .xmm10) (hd13 : d ≠ .xmm13) (a b c e : VG.Proof.Blake2.X86_64.Avx2.W) (s : State) :
    WP isa (.block (quad d a b c e)) s fun u =>
      (qw u d 0 = a ∧ qw u d 1 = b ∧ qw u d 2 = c ∧ qw u d 3 = e) ∧ VG.Proof.Blake2.X86_64.Avx2.SF [d, .xmm10, .xmm13] s u := by
  unfold quad
  rw [List.append_assoc]
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.pair_ok hd13 a b s).mono fun u1 ⟨l10, _, f1⟩ => ?_
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.pair_ok (by decide) c e u1).mono fun u2 ⟨l20, _, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  have hd : u2.lane d 0 = b ++ a := (f2.lane d (by simp [hd10, hd13]) 0).trans l10
  refine ⟨VG.Proof.Blake2.X86_64.Avx2.qw_of_lanes ?_ ?_, ?_⟩
  · simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, hd]
  · simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, Nat.one_ne_zero]
    exact l20
  · refine (f1.of_mem (by simp)).trans ((f2.of_mem (by simp)).trans
      ⟨fun r _ => by rw [VOp.exec_gpr], VOp.exec_mem _ _, VOp.exec_rd _ _, VOp.exec_wr _ _,
        fun r hr l => ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, hr.1]

theorem Consts.of_lanes {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.Consts s) (h11 : ∀ l, t.lane .xmm11 l = s.lane .xmm11 l)
    (h12 : ∀ l, t.lane .xmm12 l = s.lane .xmm12 l) (h14 : ∀ l, t.lane .xmm14 l = s.lane .xmm14 l)
    (h15 : ∀ l, t.lane .xmm15 l = s.lane .xmm15 l) : VG.Proof.Blake2.X86_64.Avx2.Consts t :=
  ⟨fun l hl => by rw [h14, h15]; exact h.masks l hl,
    fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h11]).trans (h.iv0 k hk),
    fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h12]).trans (h.iv1 k hk)⟩

theorem Consts.of_regs {s t : State} (h : VG.Proof.Blake2.X86_64.Avx2.Consts s) (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    VG.Proof.Blake2.X86_64.Avx2.Consts t := by
  have e : ∀ r l, t.lane r l = s.lane r l := fun r l => by simp only [State.lane, hx, hy]
  have q : ∀ r k, qw t r k = qw s r k := fun r k => by simp only [qw, e]
  exact ⟨fun l hl => by rw [e, e]; exact h.masks l hl, fun k hk => (q _ _).trans (h.iv0 k hk),
    fun k hk => (q _ _).trans (h.iv1 k hk)⟩

theorem setup_eq : VG.Impl.Blake2.X86_64.Avx2.setup = ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    (Impl.Argon2.X86_64.Avx2.masks ++ (quad .xmm11 (VG.Proof.Blake2.X86_64.Avx2.ivAt 0) (VG.Proof.Blake2.X86_64.Avx2.ivAt 1) (VG.Proof.Blake2.X86_64.Avx2.ivAt 2) (VG.Proof.Blake2.X86_64.Avx2.ivAt 3) ++
      (quad .xmm12 (VG.Proof.Blake2.X86_64.Avx2.ivAt 4) (VG.Proof.Blake2.X86_64.Avx2.ivAt 5) (VG.Proof.Blake2.X86_64.Avx2.ivAt 6) (VG.Proof.Blake2.X86_64.Avx2.ivAt 7) ++
        ([.mov32 .rax (.imm 0), .alu .test .r8 (.reg .r8)] : List Instr)))) := by
  simp only [VG.Impl.Blake2.X86_64.Avx2.setup, List.append_assoc]; rfl

theorem setup_ok (s : State) :
    WP isa (.block VG.Impl.Blake2.X86_64.Avx2.setup) s fun t => VG.Proof.Blake2.X86_64.Avx2.Consts t ∧ t.gpr .rax = 0 ∧
      t.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (((s.gpr .r8).setWidth 32).setWidth 64 &&& ((s.gpr .r8).setWidth 32).setWidth 64 == 0) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.setup_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  generalize hs0 : s.setReg .r8 (((s.gpr .r8).setWidth 32).setWidth 64) = s0
  have g0 : ∀ r, r ≠ .r8 → s0.gpr r = s.gpr r := fun r hr => by
    rw [← hs0, RegUpd.gpr_setReg, ifn hr]
  have r80 : s0.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := by
    rw [← hs0, RegUpd.gpr_setReg_self]
  have mem0 : s0.mem = s.mem := by rw [← hs0]; rfl
  have rd0 : s0.rd = s.rd := by rw [← hs0]; rfl
  have wr0 : s0.wr = s.wr := by rw [← hs0]; rfl
  apply WP.block_append
  refine WP.mono (VG.Proof.Argon2.X86_64.Avx2.masks_ok s0) ?_
  rintro u1 ⟨m1, mem1, g1, rd1, wr1, -⟩
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.quad_ok (d := .xmm11) (by decide) (by decide) _ _ _ _ u1).mono fun u2 ⟨q2, f2⟩ => ?_
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.quad_ok (d := .xmm12) (by decide) (by decide) _ _ _ _ u2).mono fun u3 ⟨q3, f3⟩ => ?_
  have c3 : VG.Proof.Blake2.X86_64.Avx2.Consts u3 := by
    refine ⟨fun l hl => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [f3.lane _ (by decide), f3.lane _ (by decide), f2.lane _ (by decide), f2.lane _ (by decide)]
      exact m1 l hl
    · rw [VG.Proof.Blake2.X86_64.Avx2.qw_eq_of_sf f3 (by decide)]
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q2.1, q2.2.1, q2.2.2.1, q2.2.2.2]
    · rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q3.1, q3.2.1, q3.2.2.1, q3.2.2.2]
  have g3 : ∀ r, r ≠ .rax → u3.gpr r = s0.gpr r := fun r hr =>
    (f3.gpr r hr).trans ((f2.gpr r hr).trans (g1 r hr))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.setReg32, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have e8 : u3.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := (g3 _ (by decide)).trans r80
  have m3 : u3.mem = s.mem := f3.mem.trans (f2.mem.trans (mem1.trans mem0))
  have rd3 : u3.rd = s.rd := f3.rd.trans (f2.rd.trans (rd1.trans rd0))
  have wr3 : u3.wr = s.wr := f3.wr.trans (f2.wr.trans (wr1.trans wr0))
  refine ⟨c3.of_regs rfl rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, ↓reduceIte, reduceCtorEq, e8, m3, rd3, wr3]
  · rfl
  · simp only [h1, ite_false]; exact (g3 r h1).trans (g0 r h2)

/-- What a block of general-purpose instructions leaves: memory, permissions
and vector registers. -/
structure GF (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi

theorem GF.trans {s t u : State} (h : VG.Proof.Blake2.X86_64.Avx2.GF s t) (h' : VG.Proof.Blake2.X86_64.Avx2.GF t u) : VG.Proof.Blake2.X86_64.Avx2.GF s u :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.xmm.trans h.xmm,
    h'.ymmHi.trans h.ymmHi⟩

theorem flag_ok {s₀ s₁ : State} (h8 : s₁.gpr .r8 = ((s₀.gpr .r8).setWidth 32).setWidth 64)
    (hzf : s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&&
      ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0)) :
    WP isa flag s₁ fun s₂ => s₂.gpr .r8 = flagW 64 (fl s₀) ∧
      s₂.zf = some (s₁.gpr .rdx &&& s₁.gpr .rdx == 0) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧
      VG.Proof.Blake2.X86_64.Avx2.GF s₁ s₂ := by
  refine WP.seq (WP.mono (Q := fun s : State => s.gpr .r8 = flagW 64 (fl s₀) ∧
      (∀ r, r ≠ .r8 → s.gpr r = s₁.gpr r) ∧ VG.Proof.Blake2.X86_64.Avx2.GF s₁ s) ?_ fun s h => ?_)
  · refine WP.ite (!(fl s₀)) (by simp only [eval, hzf, zf_last]) (fun h => ?_) (fun h => ?_)
    · have hf : fl s₀ = false := by simpa using h
      refine WP.block_nil ⟨?_, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      have hx : (s₀.gpr .r8).setWidth 32 = 0 := by simpa [fl] using hf
      rw [h8, hx, hf]; rfl
    · have hf : fl s₀ = true := by simpa using h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, RegUpd.gpr_setReg,
        ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hf]
      exact ⟨by decide, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨h8', hg, hf⟩ := h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
      RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, hg .rdx (by decide), Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨h8', trivial, hg, hf.trans ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## The work vector -/

def initOps : List VOp :=
  [.vmovdqa .l256 x2 .xmm11, .vmovq .xmm13 .rcx, .vmovq .xmm4 .rax,
    .vbin .vpunpcklqdq .l128 .xmm13 .xmm13 .xmm4, .vmovq .xmm4 .r8,
    .vinserti128 .xmm13 .xmm13 .xmm4 1, .vbin .vpxor .l256 x3 .xmm12 .xmm13]

theorem init_eq : VG.Impl.Blake2.X86_64.Avx2.init =
    ([.vmovdquLoad .l256 x0 (VG.Impl.Blake2.X86_64.at_ .rdi 0), .vmovdquLoad .l256 x1 (VG.Impl.Blake2.X86_64.at_ .rdi 32)] : List Instr) ++
      initOps.map .vop := rfl

/-- The fourth row's counter and flag: `ymm13` before the XOR. -/
theorem x13_lanes (s : State) :
    (VG.Proof.Argon2.X86_64.Avx2.vrun (initOps.take 6) s).lane .xmm13 0 = s.gpr .rax ++ s.gpr .rcx ∧
    (VG.Proof.Argon2.X86_64.Avx2.vrun (initOps.take 6) s).lane .xmm13 1 = (0 : VG.Proof.Blake2.X86_64.Avx2.W) ++ s.gpr .r8 := by
  simp only [VG.Proof.Blake2.X86_64.Avx2.initOps, List.take, VG.Proof.Argon2.X86_64.Avx2.vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
    show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, reduceCtorEq, Nat.one_ne_zero,
    VBinOp.sse, State.setV_gpr, RegUpd.xmm_setV]
  exact ⟨VG.Proof.Blake2.X86_64.Avx2.unpck_eq _ _, trivial⟩

theorem qword_pxor' (x y : BitVec 128) (i : Nat) :
    qword (XBinOp.eval .pxor x y) i = qword x i ^^^ qword y i :=
  VG.Proof.Argon2.X86_64.Avx2.qword_pxor x y i

/-- The rows after `initOps`, quadword by quadword. -/
theorem initOps_qw (s : State) {k : Nat} (hk : k < 4) :
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.initOps s) x0 k = qw s x0 k ∧ qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.initOps s) x1 k = qw s x1 k ∧
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.initOps s) x2 k = qw s .xmm11 k ∧
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.initOps s) x3 k = qw s .xmm12 k ^^^ qw (VG.Proof.Argon2.X86_64.Avx2.vrun (initOps.take 6) s) .xmm13 k := by
  have e : VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Blake2.X86_64.Avx2.initOps s = (VOp.vbin .vpxor .l256 x3 .xmm12 .xmm13).exec (VG.Proof.Argon2.X86_64.Avx2.vrun (initOps.take 6) s) :=
    rfl
  rw [e, qw_vbin, qw_vbin, qw_vbin, qw_vbin]
  simp only [↓reduceIte, reduceCtorEq, VBinOp.sse, VG.Proof.Blake2.X86_64.Avx2.qword_pxor', qw_lane]
  simp only [qw, VG.Proof.Blake2.X86_64.Avx2.initOps, List.take, VG.Proof.Argon2.X86_64.Avx2.vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
    show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, reduceCtorEq,
    VG.Proof.Poly1305.X86_64.Avx2.lane_sel _ _ hk, and_self]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (VG.Impl.Blake2.X86_64.at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Blake2.X86_64.at_, VG.Proof.Blake2.X86_64.Avx2.ofInt_natCast]

/-- The fourth row's counter and flag words, `(t₀, t₁, f, 0)`. -/
def ctr (T : Nat) (f : Bool) (q : Nat) : VG.Proof.Blake2.X86_64.Avx2.W :=
  if q = 0 then BitVec.ofNat 64 T else if q = 1 then BitVec.ofNat 64 (T / 2 ^ 64)
  else if q = 2 then flagW 64 f else 0

theorem init_ok {s : State} {st : Addr} {T : Nat} {f : Bool} (hdi : s.gpr .rdi = st)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 T) (hax : s.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 64))
    (h8 : s.gpr .r8 = flagW 64 f) (hc : VG.Proof.Blake2.X86_64.Avx2.Consts s)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block VG.Impl.Blake2.X86_64.Avx2.init) s fun t =>
      (∀ q < 4, qw t x0 q = s.mem.readW (st + BitVec.ofNat 64 (8 * q)) 64) ∧
      (∀ q < 4, qw t x1 q = s.mem.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64) ∧
      (∀ q < 4, qw t x2 q = VG.Proof.Blake2.X86_64.Avx2.ivAt q) ∧ (∀ q < 4, qw t x3 q = VG.Proof.Blake2.X86_64.Avx2.ivAt (4 + q) ^^^ VG.Proof.Blake2.X86_64.Avx2.ctr T f q) ∧
      VG.Proof.Blake2.X86_64.Avx2.VF [x0, x1, x2, x3, .xmm4, .xmm13] s t := by
  rw [VG.Proof.Blake2.X86_64.Avx2.init_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, VG.Proof.Blake2.X86_64.Avx2.ea_at, hdi, hin0,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, hin1, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine VG.Proof.Blake2.X86_64.Avx2.block_vops_ok _ _ ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · rw [(VG.Proof.Blake2.X86_64.Avx2.initOps_qw _ hq).1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifp rfl, VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add, Nat.zero_add]
  · rw [(VG.Proof.Blake2.X86_64.Avx2.initOps_qw _ hq).2.1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add,
      show 32 + 8 * q = 8 * (4 + q) by omega]
  · rw [(VG.Proof.Blake2.X86_64.Avx2.initOps_qw _ hq).2.2.1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifn (by decide)]
    exact hc.iv0 q hq
  · rw [(VG.Proof.Blake2.X86_64.Avx2.initOps_qw _ hq).2.2.2, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifn (by decide), hc.iv1 q hq]
    obtain ⟨l0, l1⟩ := VG.Proof.Blake2.X86_64.Avx2.x13_lanes ((s.setV .l256 x0 ((s.mem.readW (st + BitVec.ofNat 64 0) 256).extractLsb' 0 128)
      ((s.mem.readW (st + BitVec.ofNat 64 0) 256).extractLsb' 128 128)).setV .l256 x1
      ((s.mem.readW (st + BitVec.ofNat 64 32) 256).extractLsb' 0 128)
      ((s.mem.readW (st + BitVec.ofNat 64 32) 256).extractLsb' 128 128))
    obtain ⟨c0, c1, c2, c3⟩ := VG.Proof.Blake2.X86_64.Avx2.qw_of_lanes l0 l1
    simp only [State.setV_gpr, hcx, hax, h8] at c0 c1 c2
    rcases VG.X86_64.cases4 hq with rfl | rfl | rfl | rfl
    · rw [c0]; rfl
    · rw [c1]; rfl
    · rw [c2]; rfl
    · rw [c3]; rfl
  · refine ⟨by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_gpr, State.setV_gpr],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_mem, State.setV_mem],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_rd, State.setV_rd],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_wr, State.setV_wr], fun r hr l _ => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h13⟩ := hr
    simp only [VG.Proof.Blake2.X86_64.Avx2.initOps, VG.Proof.Argon2.X86_64.Avx2.vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
      show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, h0, h1, h2, h3, h4, h13]

/-- The rows after `init` are the work vector before the rounds. -/
theorem words_init {t : State} {m : Mem} {st : Addr} {T : Nat} {f : Bool}
    (h0 : ∀ q < 4, qw t x0 q = m.readW (st + BitVec.ofNat 64 (8 * q)) 64)
    (h1 : ∀ q < 4, qw t x1 q = m.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64)
    (h2 : ∀ q < 4, qw t x2 q = VG.Proof.Blake2.X86_64.Avx2.ivAt q) (h3 : ∀ q < 4, qw t x3 q = VG.Proof.Blake2.X86_64.Avx2.ivAt (4 + q) ^^^ VG.Proof.Blake2.X86_64.Avx2.ctr T f q) :
    VG.Proof.Argon2.X86_64.Avx2.words t = V0 Spec.Blake2.b (Spec.Blake2.stateAt 64 m st) T f := by
  apply Vector.ext; intro j hj
  rw [words_get _ _ hj, V0_get _ _ _ _ _ hj]
  have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [Impl.Argon2.X86_64.Avx2.vreg]
  · rw [h0 _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
      Vector.getElem_ofFn]
    exact congrArg (fun x => m.readW (st + BitVec.ofNat 64 x) 64) (by dsimp only; omega)
  · rw [h1 _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
      Vector.getElem_ofFn]
    exact congrArg (fun x => m.readW (st + BitVec.ofNat 64 x) 64) (by dsimp only; omega)
  · rw [h2 _ hq, dite_eq_right_of_eq_false (eq_false (by omega)), ifn (by omega), ifn (by omega),
      ifn (by omega), VG.Proof.Blake2.X86_64.Avx2.ivAt, dite_eq_left_of_eq_true (eq_true (by omega))]
    simp only [show j % 4 = j - 8 by omega]
  · rw [h3 _ hq, dite_eq_right_of_eq_false (eq_false (by omega))]
    have : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.Blake2.X86_64.Avx2.ivAt, VG.Proof.Blake2.X86_64.Avx2.ctr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte,
        ↓reduceIte, Nat.reduceEqDiff]
    exact BitVec.xor_zero

/-! ## The new state -/

theorem qw_xor (s : State) (d a b r : XReg) (k : Nat) :
    qw ((VOp.vbin .vpxor .l256 d a b).exec s) r k = if r = d then qw s a k ^^^ qw s b k else qw s r k := by
  rw [qw_vbin]
  split
  · simp only [VBinOp.sse, VG.Proof.Blake2.X86_64.Avx2.qword_pxor', qw_lane]
  · rfl

theorem finish_eq : VG.Impl.Blake2.X86_64.Avx2.finish =
    ([v .vpxor x0 x0 x2, v .vpxor x1 x1 x3, .vmovdquLoad .l256 .xmm4 (VG.Impl.Blake2.X86_64.at_ .rdi 0),
      v .vpxor x0 x0 .xmm4, .vmovdquStore .l256 (VG.Impl.Blake2.X86_64.at_ .rdi 0) x0] : List Instr) ++
    ([.vmovdquLoad .l256 .xmm4 (VG.Impl.Blake2.X86_64.at_ .rdi 32), v .vpxor x1 x1 .xmm4,
      .vmovdquStore .l256 (VG.Impl.Blake2.X86_64.at_ .rdi 32) x1] : List Instr) := rfl

/-- The first half of the new state. -/
theorem finish0_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hout : InRegions s.wr (st + BitVec.ofNat 64 0) 32) :
    WP isa (.block [v .vpxor x0 x0 x2, v .vpxor x1 x1 x3, .vmovdquLoad .l256 .xmm4 (VG.Impl.Blake2.X86_64.at_ .rdi 0),
      v .vpxor x0 x0 .xmm4, .vmovdquStore .l256 (VG.Impl.Blake2.X86_64.at_ .rdi 0) x0]) s fun t => ∃ y : BitVec 256,
      (∀ q < 4, qword256 y q = qw s x0 q ^^^ qw s x2 q ^^^
        s.mem.readW (st + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * q)) 64) ∧
      t.mem = s.mem.writeW (st + BitVec.ofNat 64 0) y ∧
      (∀ q < 4, qw t x1 q = qw s x1 q ^^^ qw s x3 q) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ x0 → r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, VG.Proof.Blake2.X86_64.Avx2.ea_at, hdi, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VOp.exec_mem,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, hin, hout, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, fun q hq => ?_, trivial, trivial, trivial, fun r h0 h1 h4 l => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm _ _ hq, VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifn (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifp rfl]
  · rw [VG.Proof.Argon2.X86_64.Avx2.qw_setMem, VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifp rfl, VG.Proof.Blake2.X86_64.Avx2.qw_xor,
      ifn (by decide), VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifn (by decide)]
  · simp only [State.setMem_lane, lane_vbin256, State.lane_setV256, h0, h1, h4, ite_false]

/-- The second half of the new state. -/
theorem finish1_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32)
    (hout : InRegions s.wr (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block [.vmovdquLoad .l256 .xmm4 (VG.Impl.Blake2.X86_64.at_ .rdi 32), v .vpxor x1 x1 .xmm4,
      .vmovdquStore .l256 (VG.Impl.Blake2.X86_64.at_ .rdi 32) x1]) s fun t => ∃ y : BitVec 256,
      (∀ q < 4, qword256 y q = qw s x1 q ^^^
        s.mem.readW (st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * q)) 64) ∧
      t.mem = s.mem.writeW (st + BitVec.ofNat 64 32) y ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r, r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, VG.Proof.Blake2.X86_64.Avx2.ea_at, hdi, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VOp.exec_mem,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, hin, hout, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, trivial, trivial, trivial, fun r h1 h4 l => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm _ _ hq, VG.Proof.Blake2.X86_64.Avx2.qw_xor, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq]
  · simp only [State.setMem_lane, lane_vbin256, State.lane_setV256, h1, h4, ite_false]

theorem finish_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32)
    (hout0 : InRegions s.wr (st + BitVec.ofNat 64 0) 32)
    (hout1 : InRegions s.wr (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block VG.Impl.Blake2.X86_64.Avx2.finish) s fun t =>
      (∀ j (hj : j < 8), t.mem.readW (st + BitVec.ofNat 64 (8 * j)) 64 =
        s.mem.readW (st + BitVec.ofNat 64 (8 * j)) 64 ^^^ (VG.Proof.Argon2.X86_64.Avx2.words s)[j]'(Nat.lt_trans hj (by decide)) ^^^
          (VG.Proof.Argon2.X86_64.Avx2.words s)[j + 8]'(Nat.add_lt_add_right hj 8)) ∧
      Frame [⟨st, 64⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ x0 → r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  rw [VG.Proof.Blake2.X86_64.Avx2.finish_eq]
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.finish0_ok hdi hin0 hout0).mono fun u ⟨y0, hy0, m0, x1u, gu, rdu, wru, lu⟩ => ?_
  refine (VG.Proof.Blake2.X86_64.Avx2.finish1_ok (st := st) (by rw [gu]; exact hdi) (by rw [rdu, wru]; exact hin1)
    (by rw [wru]; exact hout1)).mono fun t ⟨y1, hy1, m1, gt, rdt, wrt, lt⟩ => ?_
  have u32 : ∀ q < 4, u.mem.readW (st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * q)) 64 =
      s.mem.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64 := fun q hq => by
    rw [Offset.add_add, m0, show 32 + 8 * q = 8 * (4 + q) by omega,
      read_write256 _ st (d := 8 * (4 + q)) (e := 0) (by omega) (by omega) (by omega) (by omega),
      ifn (by omega)]
  refine ⟨fun j hj => ?_, ?_, gt.trans gu, rdt.trans rdu, wrt.trans wru, fun r h0 h1 h4 l =>
    (lt r h1 h4 l).trans (lu r h0 h1 h4 l)⟩
  · rw [m1, read_write256 _ st (d := 8 * j) (e := 32) (by omega) (by omega) (by omega) (by omega)]
    by_cases hj4 : j < 4
    · rw [ifn (by omega), m0,
        read_write256 _ st (d := 8 * j) (e := 0) (by omega) (by omega) (by omega) (by omega), ifp (by omega),
        Nat.sub_zero, show 8 * j / 8 = j by omega, hy0 j hj4, Offset.add_add, Nat.zero_add,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 0 by omega,
        show (j + 8) / 4 = 2 by omega, show j % 4 = j by omega, show (j + 8) % 4 = j by omega]
      simp only [Impl.Argon2.X86_64.Avx2.vreg]
      rw [BitVec.xor_comm _ (s.mem.readW _ 64), BitVec.xor_assoc]
    · rw [ifp (by omega), show (8 * j - 32) / 8 = j - 4 by omega, hy1 _ (by omega), x1u _ (by omega),
        u32 _ (by omega), show 4 + (j - 4) = j by omega,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 1 by omega,
        show (j + 8) / 4 = 3 by omega, show j % 4 = j - 4 by omega, show (j + 8) % 4 = j - 4 by omega]
      simp only [Impl.Argon2.X86_64.Avx2.vreg]
      rw [BitVec.xor_comm _ (s.mem.readW _ 64), BitVec.xor_assoc]
  · rw [m1, m0]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))

/-! ## The next block -/

theorem advance_ok {s : State} {T : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 T)
    (hax : s.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 64)) :
    WP isa (.block advance) s fun t => t.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 128 ∧
      t.gpr .rcx = BitVec.ofNat 64 (T + 128) ∧ t.gpr .rax = BitVec.ofNat 64 ((T + 128) / 2 ^ 64) ∧
      t.gpr .rdx = s.gpr .rdx - 1 ∧ t.zf = some (s.gpr .rdx - 1 == 0) ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ VG.Proof.Blake2.X86_64.Avx2.GF s t := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  have e0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    RegUpd.zf_setReg, RegUpd.zf_arithFlags, e128, e0, e1, ↓reduceIte, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', hcx, hax]
  refine ⟨trivial, ?_, ?_, trivial, trivial, fun r h1 h2 h3 h4 => ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.ofNat_add_ofNat]
  · rw [show ∀ x : VG.Proof.Blake2.X86_64.Avx2.W, x + (0 : VG.Proof.Blake2.X86_64.Avx2.W) = x from fun x => BitVec.add_zero x]
    exact carry_ofNat T 128 (by decide)
  · simp only [h1, h2, h3, h4, ite_false]

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = blkAddr 64 s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
  rax : s.gpr .rax = BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64)
  r8 : s.gpr .r8 = flagW 64 (fl s₀)
  keep : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Blake2.X86_64.stR 64 s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 64 s.mem (stA s₀) =
    Spec.Blake2.compressBlocks Spec.Blake2.b (H₀ 64 s₀) s₀.mem (bpA s₀) i (t₀ s₀) (fl s₀)
  consts : VG.Proof.Blake2.X86_64.Avx2.Consts s

namespace PreY
variable {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Pre 64 s₀)
include hp

theorem st_in {d : Nat} (hd : d + 32 ≤ 64) :
    InRegions (s₀.rd ++ s₀.wr) (stA s₀ + BitVec.ofNat 64 d) 32 :=
  ⟨VG.Proof.Blake2.X86_64.stR 64 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem st_out {d : Nat} (hd : d + 32 ≤ 64) : InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 d) 32 :=
  ⟨VG.Proof.Blake2.X86_64.stR 64 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem blk_in {i : Nat} (hi : i < nb s₀) {k : Nat} (hk : k ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr 64 s₀ i + BitVec.ofNat 64 (8 * k)) 16 := by
  have := hp.nb_lt (.inl rfl)
  refine ⟨blR 64 s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
  rw [hb] at this ⊢
  exact Offset.contains_base _ (by rw [hb]; omega) (by omega)

/-- The block is not in the state. -/
theorem blk_frame {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [VG.Proof.Blake2.X86_64.stR 64 s₀] s₀.mem m) :
    Spec.Blake2.blockAt 64 m (blkAddr 64 s₀ i) = Spec.Blake2.blockAt 64 s₀.mem (blkAddr 64 s₀ i) := by
  have := hp.nb_lt (.inl rfl)
  funext j
  rw [show j = ⟨j.val, j.isLt⟩ from rfl, Proof.Blake2.blockAt_word _ _ _ j.isLt,
    Proof.Blake2.blockAt_word _ _ _ j.isLt]
  refine hf.readW (r := blR 64 s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [blkAddr, Offset.add_add]
    have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
    rw [hb] at this ⊢
    exact Offset.contains_base _ (by rw [hb]; omega) (by omega)
  · simp only [List.mem_singleton] at hr
    subst hr; exact hp.bl_st

end PreY

theorem body_ok {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Pre 64 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : VG.Proof.Blake2.X86_64.Avx2.Common s₀ i s) :
    WP isa body s fun s' =>
      VG.Proof.Blake2.X86_64.Avx2.Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hdi : s.gpr .rdi = stA s₀ := hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hc.rd, hc.wr]
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.init_ok hdi hc.rcx hc.rax hc.r8 hc.consts (hrw ▸ PreY.st_in hp (by decide))
    (hrw ▸ PreY.st_in hp (by decide))).mono fun t1 ⟨h0, h1, h2, h3, f1⟩ => ?_)
  have w1 := VG.Proof.Blake2.X86_64.Avx2.words_init h0 h1 h2 h3
  have c1 := hc.consts.of_vf f1 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.rounds_ok 12 (p := blkAddr 64 s₀ i) (by rw [f1.gpr]; exact hc.rsi)
    (fun k hk => by rw [f1.rd, f1.wr, hrw]; exact PreY.blk_in hp hi hk) c1.masks).mono
    fun t2 ⟨w2, f2, m2⟩ => ?_)
  have c2 := c1.of_vf f2 (by decide) (by decide) (by decide) (by decide)
  apply WP.block_append
  refine (VG.Proof.Blake2.X86_64.Avx2.finish_ok (st := stA s₀) (by rw [f2.gpr, f1.gpr]; exact hdi)
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreY.st_in hp (by decide))
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreY.st_in hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreY.st_out hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreY.st_out hp (by decide))).mono
    fun t3 ⟨x3, fr3, g3, rd3, wr3, l3⟩ => ?_
  have cx3 : t3.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rcx
  have ax3 : t3.gpr .rax = BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rax
  refine (VG.Proof.Blake2.X86_64.Avx2.advance_ok cx3 ax3).mono fun t4 ⟨si4, cx4, ax4, dx4, zf4, g4, gf4⟩ => ?_
  have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
  have gs : ∀ r, t3.gpr r = s.gpr r := fun r => by rw [g3, f2.gpr, f1.gpr]
  have dx : t4.gpr .rdx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [dx4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]
  have mem2 : t2.mem = s.mem := f2.mem.trans f1.mem
  refine ⟨⟨?_, dx, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [si4, gs, hc.rsi]; exact Proof.Blake2.X86_64.blkAddr_succ (w := 64) s₀ i
  · rw [cx4, hb]; congr 1; omega
  · rw [ax4, hb, show t₀ s₀ + i * 128 + 128 = t₀ s₀ + (i + 1) * 128 by omega]
  · rw [g4 _ (by decide) (by decide) (by decide) (by decide), gs]; exact hc.r8
  · rw [g4 _ h1 h2 h3 h4, gs]; exact hc.keep r h1 h2 h3 h4 h5
  · rw [gf4.rd, rd3, f2.rd, f1.rd, hc.rd]
  · rw [gf4.wr, wr3, f2.wr, f1.wr, hc.wr]
  · rw [gf4.mem]
    exact hc.frame.trans (by rw [← mem2]; exact fr3)
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, F_eq]
    apply Vector.ext; intro j hj
    rw [Vector.getElem_ofFn, Spec.Blake2.stateAt, Vector.getElem_ofFn, gf4.mem]
    simp only [Nat.reduceDiv]
    rw [x3 j hj, mem2, w2, w1, f1.mem, PreY.blk_frame hp hi hc.frame,
      show Spec.Blake2.b.r = 12 from rfl, Fin.getElem_fin, Fin.getElem_fin]
    have hst : (Spec.Blake2.stateAt 64 s.mem (stA s₀))[j] =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * j)) 64 := by
      simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, Nat.reduceDiv]
    rw [hst]
  · exact (c2.of_lanes (l3 _ (by decide) (by decide) (by decide))
      (l3 _ (by decide) (by decide) (by decide)) (l3 _ (by decide) (by decide) (by decide))
      (l3 _ (by decide) (by decide) (by decide))).of_regs gf4.xmm gf4.ymmHi
  · rw [zf4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]

/-! ## The whole function -/

theorem common0 {s₀ s₂ : State} (h8 : s₂.gpr .r8 = flagW 64 (fl s₀))
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r) (hax : s₂.gpr .rax = 0)
    (hm : s₂.mem = s₀.mem) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr) (hc : VG.Proof.Blake2.X86_64.Avx2.Consts s₂) :
    VG.Proof.Blake2.X86_64.Avx2.Common s₀ 0 s₂ := by
  refine ⟨?_, ?_, ?_, ?_, h8, fun r _ _ h3 _ h5 => hg r h3 h5, hrd, hwr, ?_, ?_, hc⟩
  · rw [hg _ (by decide) (by decide), blkAddr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [hg _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hg _ (by decide) (by decide), Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hax, Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt (s₀.gpr .rcx).isLt]; rfl
  · rw [hm]; exact Frame.refl _ _
  · rw [Proof.Blake2.compressBlocks_zero, hm]

theorem correct {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Pre 64 s₀) :
    WP isa VG.Impl.Blake2.X86_64.Avx2.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 Spec.Blake2.b).post s₀ s' := by
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.setup_ok s₀).mono fun s₁ ⟨c1, ax1, r81, g1, m1, rd1, wr1, zf1⟩ => ?_)
  refine WP.seq ((VG.Proof.Blake2.X86_64.Avx2.flag_ok (s₀ := s₀) r81 zf1).mono fun s₂ ⟨r82, zf2, g2, f2⟩ => ?_)
  have hc₀ : VG.Proof.Blake2.X86_64.Avx2.Common s₀ 0 s₂ := VG.Proof.Blake2.X86_64.Avx2.common0 r82
    (fun r h1 h2 => (g2 r h2).trans (g1 r h1 h2)) ((g2 _ (by decide)).trans ax1)
    (f2.mem.trans m1) (f2.rd.trans rd1) (f2.wr.trans wr1) (c1.of_regs f2.xmm f2.ymmHi)
  have hdx : s₁.gpr .rdx = s₀.gpr .rdx := g1 _ (by decide) (by decide)
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86_64.Avx2.Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_)
  · refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp only [eval, zf2, hdx])
      (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp only [nb, h]; rfl
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VG.Proof.Blake2.X86_64.Avx2.Common s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
          (isa.eval .ne s' = some false ∧ VG.Proof.Blake2.X86_64.Avx2.Common s₀ (nb s₀) s') ∨
          (isa.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hc⟩
        refine WP.mono (VG.Proof.Blake2.X86_64.Avx2.body_ok hp hi hc) fun s' ⟨hc', hz⟩ => ?_
        by_cases hlast : i + 1 = nb s₀
        · left
          refine ⟨?_, hlast ▸ hc'⟩
          simp only [eval, hz, ← hlast, Nat.sub_self, Option.map_some]; rfl
        · right
          have hne : nb s₀ - (i + 1) ≠ 0 := by omega
          refine ⟨?_, nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hc'⟩
          have h0 : (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) = false := by
            rw [beq_eq_false_iff_ne]
            intro h'
            have h'' := congrArg BitVec.toNat h'
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s₀.gpr .rdx).isLt)] at h''
            exact hne (h''.trans rfl)
          simp only [eval, hz, h0, Option.map_some]; rfl
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hc₀⟩
  · refine (VG.Proof.Argon2.X86_64.Avx2.vzeroupper_ok s₃).mono fun s' ⟨m', g', _, _, _⟩ => ?_
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [g']
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [m']
      exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
    · show Spec.Blake2.stateAt _ _ _ = _
      rw [m']; exact hc.state

/-! ## Results -/

theorem compress_correct (s : State) (hs : (compressX86_64 Spec.Blake2.b).pre s) :
    ∃ t s', Exec isa Impl.Blake2.X86_64.Avx2.compress s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.b).post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Blake2.X86_64.Avx2.correct (VG.Proof.Blake2.X86_64.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem compress_ct : ConstantTime isa (compressX86_64 Spec.Blake2.b).pre
    (compressX86_64 Spec.Blake2.b).pub Impl.Blake2.X86_64.Avx2.compress :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (VG.Proof.Blake2.X86_64.τ₀ 64) (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.agree₀ (.inl rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compress_verified :
    Verified X86_64.target Impl.Blake2.X86_64.Avx2.compress (Spec.Blake2.compressBContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Blake2.X86_64.Avx2.compress_correct VG.Proof.Blake2.X86_64.Avx2.compress_ct (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)

end VG.Proof.Blake2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Stream`. -/
section

/-!
# BLAKE2b on x86-64 with AVX2: the streaming functions

`update` and `finalize` calling `vg_blake2b_compress_avx2` (`avx2`): what
their proofs of correctness need of it (`callee`), and their constant time,
by the same taint analysis as with the scalar compression function
(`Proof/Blake2/X86_64/Stream/CT.lean`), of the code with this callee.
-/

namespace VG.Proof.Blake2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Blake2
open VG.Proof.Blake2.X86_64.Stream (CalleeOk τUpdate τFinalize update_agree finalize_agree okB)

theorem callee : CalleeOk b Impl.Blake2.X86_64.Avx2.compress :=
  CalleeOk.of_verified VG.Proof.Blake2.X86_64.Avx2.compress_correct (by lit_decide) (by lit_decide)

theorem update_ct : ConstantTime isa (updateX86_64 b).pre (updateX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.update b VG.Proof.Blake2.X86_64.Avx2.avx2) :=
  VG.Taint.constantTime (A := taint) (τUpdate 64) (fun _ _ h₁ h₂ hp => update_agree okB h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86_64 b).pre (finalizeX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.finalize b VG.Proof.Blake2.X86_64.Avx2.avx2) :=
  VG.Taint.constantTime (A := taint) (τFinalize 64)
    (fun _ _ h₁ h₂ hp => finalize_agree okB h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Avx2

end
