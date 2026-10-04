import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Blake2.Cols
import VerifiedGarbage.Impl.Blake2.X86_64.Avx

/-!
# BLAKE2s on x86-64 with AVX: a round

The rows of the work vector are in `xmm0`–`xmm3` (`words`). Each message
vector is gathered into `xmm5` (`msg_ok`), each half of `G` runs on the
four doublewords at once (`half_cols`), and the diagonals are rotated into
columns and back (`diag_words`, `undiag_words`); `round_ok` composes them
into `Spec.Blake2.round` through `round_colsP`.

Every instruction is `VEX.128`-encoded: only the low lanes of the vector
registers (`State.xmm`) are followed.
-/

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2 (mix pick4 mixColsP rotInP rotOutP mixColsP_get rotInP_get rotOutP_get
  round_colsP)

abbrev W := BitVec 32

/-- Doubleword `q` of `r`. -/
abbrev dw (s : State) (r : XReg) (q : Nat) : W := dword (s.xmm r) q

theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## Blocks of vector instructions -/

/-- Run instructions that write only vector registers. -/
def run : List VOp → State → State
  | [], s => s
  | o :: os, s => run os (o.exec s)

theorem runBlock_run (os : List VOp) (s : State) :
    runBlock isa (os.map .vop) s = some (run os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem run_append (a b : List VOp) (s : State) : run (a ++ b) s = run b (run a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

@[simp] theorem run_gpr (os : List VOp) (s : State) : (run os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_gpr o s)

@[simp] theorem run_mem (os : List VOp) (s : State) : (run os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_mem o s)

@[simp] theorem run_rd (os : List VOp) (s : State) : (run os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_rd o s)

@[simp] theorem run_wr (os : List VOp) (s : State) : (run os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_wr o s)

theorem block_run_ok (os : List VOp) (s : State) {Q : State → Prop} (h : Q (run os s)) :
    WP isa (.block (os.map .vop)) s Q :=
  WP.of_runBlock ⟨_, runBlock_run os s, h⟩

/-! ## The low lanes after `VEX.128` instructions

These hold by definition, but are proven by `(rfl)`, not `rfl`: `simp` uses a
lemma proven by `rfl` as a definitional rewrite, and the kernel then checks
its result by unfolding `VOp.exec` at every instruction of a block. -/

theorem xmm_vbin (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) :
    ((VOp.vbin op .l128 d a b).exec s).xmm r =
      if r = d then op.sse.eval (s.xmm a) (s.xmm b) else s.xmm r := (rfl)

theorem xmm_vshift (op : XShiftOp) (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vshift op .l128 d a n).exec s).xmm r = if r = d then op.eval (s.xmm a) n else s.xmm r :=
  (rfl)

theorem xmm_vpshufd (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vpshufd .l128 d a o).exec s).xmm r = if r = d then shufDwords (s.xmm a) o else s.xmm r :=
  (rfl)

theorem xmm_vmovdqa (d a : XReg) (s : State) (r : XReg) :
    ((VOp.vmovdqa .l128 d a).exec s).xmm r = if r = d then s.xmm a else s.xmm r := (rfl)

theorem xmm_vmovq (d : XReg) (g : Reg) (s : State) (r : XReg) :
    ((VOp.vmovq d g).exec s).xmm r = if r = d then (0 : BitVec 64) ++ s.gpr g else s.xmm r :=
  (rfl)

/-- What a block leaves: everything but the low lanes of the vector registers
`rs` (and their upper lanes and the flags, which nothing reads). -/
structure XF (rs : List XReg) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : ∀ r, r ∉ rs → t.xmm r = s.xmm r

theorem XF.refl (rs : List XReg) (s : State) : XF rs s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XF.trans {rs : List XReg} {s t u : State} (h : XF rs s t) (h' : XF rs t u) : XF rs s u :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XF.mono {rs rs' : List XReg} {s t : State} (h : XF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    XF rs' s t := ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem XF.run {os : List VOp} {rs : List XReg} {s : State}
    (h : ∀ r, r ∉ rs → (run os s).xmm r = s.xmm r) : XF rs s (run os s) :=
  ⟨run_gpr os s, run_mem os s, run_rd os s, run_wr os s, h⟩

theorem dw_of_xf {rs : List XReg} {s t : State} (h : XF rs s t) {r : XReg} (hr : r ∉ rs) (q : Nat) :
    dw t r q = dw s r q := by
  simp only [dw, h.xmm r hr]

/-! ## Doublewords -/

theorem rotr_shifts (x : W) {n : Nat} (hn : n < 32) :
    x <<< (32 - n) ||| x >>> n = x.rotateRight n := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hn]
  exact BitVec.or_comm _ _

theorem rotr16 (x : W) : x.rotateLeft 16 = x.rotateRight 16 := by
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.rotateRight, BitVec.rotateRightAux,
    Nat.reduceMod, Nat.reduceSub]
  exact BitVec.or_comm _ _

/-- The `vpshufb` mask rotating each doubleword right by 8 bits. -/
abbrev rotr8Mask : BitVec 128 := 0x0c0f0e0d080b0a090407060500030201#128

theorem pshufb_rotr8_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rotr8Mask = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 1) % 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem dword_pshufb_rotr8 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rotr8Mask) i = (dword a i).rotateRight 8 := by
  rw [pshufb_rotr8_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword_ofBytes _ hi hm, BitVec.getLsbD_rotateRight]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byte, BitVec.getLsbD_extractLsb', getLsbD_dword, h8, decide_true, Bool.true_and,
    show 8 % 32 = 8 from rfl]
  by_cases h : m < 32 - 8
  · have h' : 8 + m < 32 := by omega
    simp only [h, h', ite_true, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · have h' : m - (32 - 8) < 32 := by omega
    simp only [h, h', hm, ite_false, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

theorem dword_pshufb_rotr16 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rot16Mask) i = (dword a i).rotateRight 16 := by
  rw [dword_pshufb_rot16 _ hi, rotr16]

/-- A 16-byte load, doubleword by doubleword. -/
theorem dword_readW (m : Mem) (a : Addr) {q : Nat} (hq : q < 4) :
    dword (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (4 * q)) 32 := by
  have h := readW_extract m a (w := 128) (k := 4 * q) (n := 4) (by omega)
  simp only [← Nat.mul_assoc, Nat.reduceMul] at h
  rw [dword_eq]; exact h

theorem punpcklqdq_dwords (a b : BitVec 128) :
    XBinOp.eval .punpcklqdq a b = ofDwords (dword a 0) (dword a 1) (dword b 0) (dword b 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, ofDwords, dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 32
  · simp [h1, show i < 64 by omega]
  by_cases h2 : i < 64
  · simp [h1, h2, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]
  by_cases h3 : i < 96
  · simp [h1, h2, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega,
      show i - 64 < 64 by omega, show i - 64 < 32 by omega]
  · simp [h1, h2, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 < 32 by omega, show 32 + (i - 32 - 32 - 32) = i - 64 by omega,
      show i - 64 < 64 by omega]

theorem dword_punpcklqdq (a b : BitVec 128) {q : Nat} (hq : q < 4) :
    dword (XBinOp.eval .punpcklqdq a b) q = if q < 2 then dword a q else dword b (q - 2) := by
  rw [punpcklqdq_dwords]
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      Nat.reduceLT, ↓reduceIte, Nat.reduceSub]

/-! ## The two halves of `G` -/

/-- Half of `G`: `a += x + b; d = (d ^ a) >>> R; c += d; b = (b ^ c) >>> n`. -/
def H (R n : Nat) (v : W × W × W × W) (x : W) : W × W × W × W :=
  let a := v.1 + x + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight R
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight n
  (a, b, c, d)

theorem add_right_comm' (a b c : W) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc]

theorem mix_eq (va vb vc vd x y : W) :
    mix Spec.Blake2.s va vb vc vd x y = H 8 7 (H 16 12 (va, vb, vc, vd) x) y := by
  simp only [mix, H, Spec.Blake2.s, add_right_comm' va vb x]
  rw [add_right_comm' _ _ y]

/-- Doubleword `q` of each of the four rows. -/
def cols (s : State) (q : Nat) : W × W × W × W := (dw s .xmm0 q, dw s .xmm1 q, dw s .xmm2 q, dw s .xmm3 q)

def halfOps (mask : XReg) (n : Nat) : List VOp :=
  [.vbin .vpaddd .l128 .xmm0 .xmm0 .xmm5, .vbin .vpaddd .l128 .xmm0 .xmm0 .xmm1,
    .vbin .vpxor .l128 .xmm3 .xmm3 .xmm0, .vbin .vpshufb .l128 .xmm3 .xmm3 mask,
    .vbin .vpaddd .l128 .xmm2 .xmm2 .xmm3, .vbin .vpxor .l128 .xmm1 .xmm1 .xmm2,
    .vshift .psrld .l128 .xmm4 .xmm1 (BitVec.ofNat 8 n),
    .vshift .pslld .l128 .xmm1 .xmm1 (BitVec.ofNat 8 (32 - n)), .vbin .vpor .l128 .xmm1 .xmm1 .xmm4]

theorem half_eq (mask : XReg) (n : Nat) : half mask n = (halfOps mask n).map .vop := rfl

/-- The registers a half writes. -/
abbrev halfRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4]

theorem half_cols {mask : XReg} {R n : Nat} (hn : 0 < n) (hn' : n < 32) {s : State}
    (h0 : mask ≠ .xmm0) (h3 : mask ≠ .xmm3)
    (hm : ∀ y : BitVec 128, ∀ q < 4, dword (XBinOp.eval .pshufb y (s.xmm mask)) q = (dword y q).rotateRight R)
    {q : Nat} (hq : q < 4) :
    cols (run (halfOps mask n) s) q = H R n (cols s q) (dw s .xmm5 q) := by
  have e1 : (BitVec.ofNat 8 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (BitVec.ofNat 8 (32 - n)).toNat = 32 - n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [halfOps, run, cols, dw, xmm_vbin, xmm_vshift, ↓reduceIte, reduceCtorEq, h0, h3,
    VBinOp.sse]
  simp only [dword_paddd _ _ hq, dword_pxor, dword_por, hm _ q hq,
    dword_psrld _ (BitVec.ofNat 8 n) (by rw [e1]; omega) hq,
    dword_pslld _ (BitVec.ofNat 8 (32 - n)) (by rw [e2]; omega) hq, e1, e2, rotr_shifts _ hn', H]

theorem half_keeps {mask : XReg} {n : Nat} (s : State) : XF halfRegs s (run (halfOps mask n) s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  simp only [halfOps, run, xmm_vbin, xmm_vshift, h0, h1, h2, h3, h4, ite_false]

/-! ## Diagonals -/

def diagOps : List VOp :=
  [.vpshufd .l128 .xmm0 .xmm0 0x93, .vpshufd .l128 .xmm2 .xmm2 0x39, .vpshufd .l128 .xmm3 .xmm3 0x4e]
def undiagOps : List VOp :=
  [.vpshufd .l128 .xmm0 .xmm0 0x39, .vpshufd .l128 .xmm2 .xmm2 0x93, .vpshufd .l128 .xmm3 .xmm3 0x4e]

/-- The register of row `k`. -/
def row : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- The work vector in `xmm0`–`xmm3`: word `j` is doubleword `j % 4` of row `j / 4`. -/
def words (s : State) : Spec.Blake2.Work 32 := Vector.ofFn fun j => dw s (row (j.val / 4)) (j.val % 4)

theorem words_get (s : State) (j : Nat) (hj : j < 16) : (words s)[j] = dw s (row (j / 4)) (j % 4) := by
  simp only [words, Vector.getElem_ofFn]

theorem cases_div4 {j : Nat} (hj : j < 16) : j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3 := by
  omega

theorem sel_93 {k : Nat} (hk : k < 4) : ((0x93 : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 3) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel_39 {k : Nat} (hk : k < 4) : ((0x39 : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 1) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel_4e {k : Nat} (hk : k < 4) : ((0x4e : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 2) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem diag_words (s : State) : words (run diagOps s) = rotInP (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotInP_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) % 4 = (j % 4 + j / 4 + 3) % 4 by omega]
  simp only [diagOps, run, dw]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [row, xmm_vpshufd, ↓reduceIte, reduceCtorEq, dword_shufDwords _ _ hk, sel_93 hk,
      sel_39 hk, sel_4e hk] <;> congr 1 <;> omega

theorem undiag_words (s : State) : words (run undiagOps s) = rotOutP (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotOutP_get _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) % 4 = (j % 4 + 3 * (j / 4) + 1) % 4 by omega]
  simp only [undiagOps, run, dw]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [row, xmm_vpshufd, ↓reduceIte, reduceCtorEq, dword_shufDwords _ _ hk, sel_93 hk,
      sel_39 hk, sel_4e hk] <;> congr 1 <;> omega

theorem diag_keeps (s : State) : XF halfRegs s (run diagOps s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [diagOps, run, xmm_vpshufd, hr.1, hr.2.2.1, hr.2.2.2.1, ite_false]

theorem undiag_keeps (s : State) : XF halfRegs s (run undiagOps s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [undiagOps, run, xmm_vpshufd, hr.1, hr.2.2.1, hr.2.2.2.1, ite_false]

/-- The rows after `G` on each doubleword are `mixColsP` of the rows before. -/
theorem words_of_cols {s t : State} {x y : Nat → W}
    (h : ∀ q < 4, cols t q = H 8 7 (H 16 12 (cols s q) (x q)) (y q)) :
    words t = mixColsP Spec.Blake2.s x y (words s) := by
  apply Vector.ext
  intro j hj
  have g := h (j % 4) (Nat.mod_lt _ (by decide))
  rw [← mix_eq] at g
  simp only [cols] at g
  rw [words_get _ _ hj, mixColsP_get _ _ _ _ _ hj, words_get _ _ (by omega),
    words_get _ _ (by omega), words_get _ _ (by omega), words_get _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [row, pick4] <;> rw [← g]

/-! ## Gathering the message words -/

/-- Where the block is, and that its 64 bytes may be read. -/
structure Blk (p : Addr) (s : State) : Prop where
  rsi : s.gpr .rsi = p
  rd : ∀ i ≤ 12, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (4 * i)) 16

theorem Blk.of_xf {rs : List XReg} {p : Addr} {s t : State} (h : Blk p s) (hf : XF rs s t) : Blk p t :=
  ⟨by rw [hf.gpr]; exact h.rsi, by rw [hf.rd, hf.wr]; exact h.rd⟩

/-- Word `j` of the block at `p`. -/
abbrev mw (m : Mem) (p : Addr) (j : Nat) : W := m.readW (p + BitVec.ofNat 64 (4 * j)) 32

theorem src_ok : ∀ j < 16, ∀ q < 4, (src j q).1 ≤ 12 ∧
    (if (src j q).2 then (src j q).1 = 4 * (j / 4) else (src j q).1 + q = j) := by decide

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

theorem mw_load {m : Mem} {p : Addr} {b q : Nat} (hq : q < 4) :
    dword (m.readW (p + BitVec.ofNat 64 (4 * b)) 128) q = mw m p (b + q) := by
  rw [dword_readW _ _ hq, Offset.add_add, mw, Nat.mul_add]

/-- Word `j` into doubleword `p` of `d`. -/
theorem ldw_ok {d : XReg} {j p : Nat} (hj : j < 16) (hp : p < 4) {s : State} {pa : Addr}
    (hb : Blk pa s) :
    WP isa (.block (ldw d j p)) s fun t => dw t d p = mw s.mem pa j ∧ XF [d] s t := by
  obtain ⟨hb12, he⟩ := src_ok j hj p hp
  have hj4 : j % 4 < 4 := Nat.mod_lt _ (by decide)
  unfold ldw
  generalize src j p = sp at hb12 he
  obtain ⟨b, sw⟩ := sp
  simp only at hb12 he
  have ld := hb.rd b hb12
  have hea : s.ea (at_ .rsi (4 * b)) = pa + BitVec.ofNat 64 (4 * b) := by rw [ea_at, hb.rsi]
  cases sw <;> simp only [Bool.false_eq_true, ite_true, ite_false] at he ⊢ <;>
  apply WP.of_runBlock <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, hea, ld, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩⟩
    · simp only [dw, RegUpd.xmm_setV, ↓reduceIte]
      rw [mw_load hp, he]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.xmm_setV, hr, ite_false]
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr => ?_⟩⟩
    · simp only [dw, xmm_vpshufd, RegUpd.xmm_setV, ↓reduceIte]
      rw [dword_shufDwords_bcast _ hj4 hp, mw_load hj4, he]
      exact congrArg (mw s.mem pa) (by omega)
    · simp only [List.mem_singleton] at hr
      simp only [xmm_vpshufd, RegUpd.xmm_setV, hr, ite_false]

theorem pairPos_lt (j j' : Nat) : pairPos j j' < 4 := by
  unfold pairPos; split <;> decide

theorem xmm_unpck (hi : Bool) (d a b : XReg) (s : State) (r : XReg) :
    ((VOp.vbin (if hi then .vpunpckhdq else .vpunpckldq) .l128 d a b).exec s).xmm r =
      if r = d then (if hi then XBinOp.eval .punpckhdq (s.xmm a) (s.xmm b)
        else XBinOp.eval .punpckldq (s.xmm a) (s.xmm b)) else s.xmm r := by
  cases hi <;> rfl

/-- Words `j` and `j'` into doublewords 0 and 1 of `d`. -/
theorem pair_ok {d a b : XReg} (hab : a ≠ b) {j j' : Nat} (hj : j < 16)
    (hj' : j' < 16) {s : State} {pa : Addr} (hb : Blk pa s) :
    WP isa (.block (pair d a b j j')) s fun t =>
      dw t d 0 = mw s.mem pa j ∧ dw t d 1 = mw s.mem pa j' ∧ XF [d, a, b] s t := by
  unfold pair
  rw [List.append_assoc]
  apply WP.block_append
  refine (ldw_ok (d := a) hj (pairPos_lt j j') hb).mono fun t1 ⟨l1, f1⟩ => ?_
  apply WP.block_append
  refine (ldw_ok (d := b) hj' (pairPos_lt j j') (hb.of_xf f1)).mono fun t2 ⟨l2, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  have a2 : dw t2 a (pairPos j j') = mw s.mem pa j := by
    rw [dw_of_xf f2 (by simpa using hab), l1]
  rw [f1.mem] at l2
  refine ⟨?_, ?_, ⟨by simp [f2.gpr, f1.gpr], by simp [f2.mem, f1.mem], by simp [f2.rd, f1.rd],
    by simp [f2.wr, f1.wr], fun r hr => ?_⟩⟩
  · simp only [dw, xmm_unpck, ↓reduceIte]
    unfold pairPos at a2 l2
    cases hh : hiPair j j' <;> simp only [hh, Bool.false_eq_true, ite_false, ite_true] at a2 l2 ⊢ <;>
      simp only [dword_punpckldq, dword_punpckhdq, dword_ofDwords_0] <;> exact a2
  · simp only [dw, xmm_unpck, ↓reduceIte]
    unfold pairPos at a2 l2
    cases hh : hiPair j j' <;> simp only [hh, Bool.false_eq_true, ite_false, ite_true] at a2 l2 ⊢ <;>
      simp only [dword_punpckldq, dword_punpckhdq, dword_ofDwords_1] <;> exact l2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [xmm_unpck, ifn hr.1, f2.xmm r (by simpa using hr.2.2), f1.xmm r (by simpa using hr.2.1)]

/-- The registers `msg` writes. -/
abbrev msgRegs : List XReg := [.xmm5, .xmm6, .xmm7, .xmm8, .xmm9]

theorem msgWord_lt (r k q : Nat) : msgWord r k q < 16 := (Spec.Blake2.sigmaAt _ _).isLt

/-- Message vector `k` of round `r`, in `xmm5`. -/
theorem msg_ok (r k : Nat) {s : State} {pa : Addr} (hb : Blk pa s) :
    WP isa (.block (msg r k)) s fun t =>
      (∀ q < 4, dw t .xmm5 q = mw s.mem pa (msgWord r k q)) ∧ XF msgRegs s t := by
  unfold msg
  rw [List.append_assoc]
  apply WP.block_append
  refine (pair_ok (d := .xmm5) (a := .xmm6) (b := .xmm7) (by decide)
    (msgWord_lt r k 0) (msgWord_lt r k 1) hb).mono fun t1 ⟨p0, p1, f1⟩ => ?_
  apply WP.block_append
  refine (pair_ok (d := .xmm8) (a := .xmm8) (b := .xmm9) (by decide)
    (msgWord_lt r k 2) (msgWord_lt r k 3) (hb.of_xf f1)).mono fun t2 ⟨p2, p3, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  rw [f1.mem] at p2 p3
  have x50 : dw t2 .xmm5 0 = mw s.mem pa (msgWord r k 0) := by
    rw [dw_of_xf f2 (by decide), p0]
  have x51 : dw t2 .xmm5 1 = mw s.mem pa (msgWord r k 1) := by
    rw [dw_of_xf f2 (by decide), p1]
  refine ⟨fun q hq => ?_, ⟨by simp [f2.gpr, f1.gpr], by simp [f2.mem, f1.mem],
    by simp [f2.rd, f1.rd], by simp [f2.wr, f1.wr], fun r hr => ?_⟩⟩
  · rcases cases4 hq with rfl | rfl | rfl | rfl <;>
      simp only [dw, xmm_vbin, ↓reduceIte, VBinOp.sse, dword_punpcklqdq _ _ hq, Nat.reduceLT,
        Nat.reduceSub]
    exacts [x50, x51, p2, p3]
  · simp only [msgRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [xmm_vbin, ifn hr.1, f2.xmm r (by simp [hr.2.2.2.1, hr.2.2.2.2]),
      f1.xmm r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-! ## A round -/

/-- The masks of the rotations, in `xmm14` and `xmm15`. -/
structure Masks (s : State) : Prop where
  m16 : s.xmm .xmm14 = rot16Mask
  m8 : s.xmm .xmm15 = rotr8Mask

/-- The registers a round writes. -/
abbrev roundRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9]

theorem Masks.of_xf {rs : List XReg} {s t : State} (h : Masks s) (hv : XF rs s t)
    (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Masks t :=
  ⟨(hv.xmm _ h14).trans h.m16, (hv.xmm _ h15).trans h.m8⟩

theorem cols_of_xf {rs : List XReg} {s t : State} (hv : XF rs s t) (h0 : .xmm0 ∉ rs)
    (h1 : .xmm1 ∉ rs) (h2 : .xmm2 ∉ rs) (h3 : .xmm3 ∉ rs) (q : Nat) : cols t q = cols s q := by
  simp only [cols, dw_of_xf hv h0, dw_of_xf hv h1, dw_of_xf hv h2, dw_of_xf hv h3]

theorem half1_cols {s : State} (h : Masks s) {q : Nat} (hq : q < 4) :
    cols (run (halfOps .xmm14 12) s) q = H 16 12 (cols s q) (dw s .xmm5 q) :=
  half_cols (by decide) (by decide) (by decide) (by decide)
    (fun y q hq => by rw [h.m16]; exact dword_pshufb_rotr16 y hq) hq

theorem half2_cols {s : State} (h : Masks s) {q : Nat} (hq : q < 4) :
    cols (run (halfOps .xmm15 7) s) q = H 8 7 (cols s q) (dw s .xmm5 q) :=
  half_cols (by decide) (by decide) (by decide) (by decide)
    (fun y q hq => by rw [h.m8]; exact dword_pshufb_rotr8 y hq) hq

theorem half_vf {mask : XReg} {n : Nat} (s : State) : XF roundRegs s (run (halfOps mask n) s) :=
  (half_keeps s).mono (by decide)

/-- The first half of `G` on the four doublewords, with the message vector
`x`, and the message vector `y` loaded for the second half, before `D`. -/
theorem g_ok {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) (r k : Nat) (x y : Nat → W)
    (hx : ∀ q < 4, mw s.mem pa (msgWord r k q) = x q)
    (hy : ∀ q < 4, mw s.mem pa (msgWord r (k + 1) q) = y q)
    {D : Prog isa} {Q : State → Prop}
    (hD : ∀ s3, XF roundRegs s s3 → Masks s3 → (∀ q < 4, cols s3 q = H 16 12 (cols s q) (x q)) →
      (∀ q < 4, dw s3 .xmm5 q = y q) → WP isa D s3 Q) :
    WP isa (.seq (.block (msg r k)) (.seq (.block half1) (.seq (.block (msg r (k + 1))) D))) s Q := by
  refine WP.seq ((msg_ok r k hb).mono fun s1 ⟨m1, f1⟩ => ?_)
  have hm1 := hm.of_xf f1 (by decide) (by decide)
  rw [half1, half_eq]
  refine WP.seq (block_run_ok _ _ ?_)
  generalize hs2 : run (halfOps .xmm14 12) s1 = s2
  have f2 : XF roundRegs s1 s2 := hs2 ▸ half_vf s1
  have c2 : ∀ q < 4, cols s2 q = H 16 12 (cols s1 q) (dw s1 .xmm5 q) := fun q hq =>
    hs2 ▸ half1_cols hm1 hq
  have f12 : XF roundRegs s s2 := (f1.mono (by decide)).trans f2
  refine WP.seq ((msg_ok r (k + 1) (hb.of_xf f12)).mono fun s3 ⟨m3, f3⟩ => ?_)
  refine hD s3 (f12.trans (f3.mono (by decide)))
    ((hm1.of_xf f2 (by decide) (by decide)).of_xf f3 (by decide) (by decide))
    (fun q hq => ?_) (fun q hq => ?_)
  · rw [cols_of_xf f3 (by decide) (by decide) (by decide) (by decide), c2 q hq,
      cols_of_xf f1 (by decide) (by decide) (by decide) (by decide), m1 q hq, hx q hq]
  · rw [m3 q hq, f12.mem, hy q hq]

/-- The second half of `G`, after `g_ok`. -/
theorem h2_words {s s3 : State} {x y : Nat → W} (hm : Masks s3)
    (hc : ∀ q < 4, cols s3 q = H 16 12 (cols s q) (x q)) (hy : ∀ q < 4, dw s3 .xmm5 q = y q) :
    words (run (halfOps .xmm15 7) s3) = mixColsP Spec.Blake2.s x y (words s) :=
  words_of_cols fun q hq => by rw [half2_cols hm hq, hc q hq, hy q hq]

theorem half2_diag_eq : half2 ++ diagonalize = (halfOps .xmm15 7 ++ diagOps).map .vop := by
  rw [List.map_append]; rfl

theorem half2_undiag_eq : half2 ++ undiagonalize = (halfOps .xmm15 7 ++ undiagOps).map .vop := by
  rw [List.map_append]; rfl

/-- Word `j` of the block. -/
theorem mw_block (m : Mem) (pa : Addr) (j : Nat) (hj : j < 16) :
    mw m pa j = Spec.Blake2.blockAt 32 m pa ⟨j, hj⟩ :=
  (Proof.Blake2.blockAt_word m pa j hj).symm

theorem lane_lo {k q : Nat} (hk : k < 2) : lane k q = q := by simp only [lane, hk, ite_true]
theorem lane_hi {k q : Nat} (hk : ¬ k < 2) : lane k q = (q + 3) % 4 := by
  simp only [lane, hk, ite_false]

theorem msg_word (m : Mem) (pa : Addr) (r k q : Nat) :
    mw m pa (msgWord r k q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * lane k q + k % 2)) :=
  mw_block m pa _ (Fin.isLt _)

theorem msg_lo (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r 0 q) = Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (2 * q)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_lo1 (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r (0 + 1) q) = Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (2 * q + 1)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r 2 q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem msg_hi1 (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r (2 + 1) q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega))

theorem diag_vf (s : State) : XF roundRegs s (run diagOps s) := (diag_keeps s).mono (by decide)
theorem undiag_vf (s : State) : XF roundRegs s (run undiagOps s) := (undiag_keeps s).mono (by decide)

/-- Round `r` on the rows in `xmm0`–`xmm3`, with the block at `rsi`. -/
theorem round_ok (r : Nat) {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) :
    WP isa (round r) s fun t =>
      words t = Spec.Blake2.round Spec.Blake2.s (Spec.Blake2.blockAt 32 s.mem pa) (words s) r ∧
      XF roundRegs s t ∧ Masks t := by
  unfold round
  refine g_ok hb hm r 0 _ _ (fun q _ => msg_lo _ _ r q) (fun q _ => msg_lo1 _ _ r q)
    fun s3 f3 hm3 hc3 hy3 => ?_
  rw [half2_diag_eq]
  refine WP.seq (block_run_ok _ _ ?_)
  generalize hs4 : run (halfOps .xmm15 7 ++ diagOps) s3 = s4
  have f4 : XF roundRegs s s4 := by
    rw [← hs4, run_append]; exact (f3.trans (half_vf s3)).trans (diag_vf _)
  have hm4 : Masks s4 := hm.of_xf f4 (by decide) (by decide)
  have w4 : words s4 = rotInP (mixColsP Spec.Blake2.s
      (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (2 * q)))
      (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (2 * q + 1))) (words s)) := by
    rw [← hs4, run_append, diag_words, h2_words hm3 hc3 hy3]
  refine g_ok (hb.of_xf f4) hm4 r 2
    (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))))
    (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))))
    (fun q _ => by rw [f4.mem]; exact msg_hi _ _ r q) (fun q _ => by rw [f4.mem]; exact msg_hi1 _ _ r q)
    fun s7 f7 hm7 hc7 hy7 => ?_
  rw [half2_undiag_eq]
  refine block_run_ok _ _ ⟨?_, ?_, ?_⟩
  · rw [run_append, undiag_words, h2_words hm7 hc7 hy7, w4, round_colsP]
  · rw [run_append]; exact ((f4.trans f7).trans (half_vf s7)).trans (undiag_vf _)
  · rw [run_append]
    exact hm.of_xf (((f4.trans f7).trans (half_vf s7)).trans (undiag_vf _)) (by decide) (by decide)

/-- Rounds `0 … n-1`. -/
theorem rounds_ok (n : Nat) {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) :
    WP isa (rounds n) s fun t =>
      words t = (List.range n).foldl (Spec.Blake2.round Spec.Blake2.s
        (Spec.Blake2.blockAt 32 s.mem pa)) (words s) ∧ XF roundRegs s t ∧ Masks t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, XF.refl _ _, hm⟩
  | succ n ih =>
    refine WP.seq (ih.mono fun t ⟨wt, ft, mt⟩ => ?_)
    refine (round_ok n (hb.of_xf ft) mt).mono fun u ⟨wu, fu, mu⟩ => ⟨?_, ft.trans fu, mu⟩
    rw [wu, wt, ft.mem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Blake2.X86_64.Avx
