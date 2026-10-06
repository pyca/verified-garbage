import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Round
import VerifiedGarbage.Impl.Blake2.X86_64.Avx512

/-!
# BLAKE2b on x86-64 with AVX-512: a round

As for the AVX2 code (`Proof/Blake2/X86_64/Avx2/Round.lean`), whose
message gathering (`msg_ok`), diagonals (`diag_words`, `undiag_words`) and
columns (`words_of_cols`) this proof uses: only the halves of `G` differ,
each rotation being one `vprorq` (`xorRor_qw`), so no masks are needed.
-/

namespace VG.Proof.Blake2.X86_64.Avx512

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx512
open VG.Impl.Blake2.X86_64.Avx2 (msg msgWord diagonalize undiagonalize)
open VG.Proof.Argon2.X86_64.Avx2 (vrun vrun_append words x0 x1 x2 x3 qword_pxor)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qw_lane qword_app0 qword_app1)
open VG.Proof.Blake2 (mixCols rotIn round_lanes)
open VG.Proof.Blake2.X86_64.Avx2 (W H1 H2 cols qw_add vrun_cons_nil vrun_pair Keeps halfRegs
  diagOps undiagOps diag_words undiag_words words_of_cols VF msg_ok qw_eq_of_vf VF.trans VF.of_mem
  VF.regs roundRegs block_vops_ok VF.vrun diag_vf undiag_vf cols_of_vf msg_lo msg_lo1 msg_hi
  msg_hi1)

/-! ## Rotations -/

theorem lane_vprorq256 (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vprorq .l256 d a n).exec s).lane r l =
      if r = d then rorQwords (s.lane a l) n else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem qword_rorQwords (x : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 2) :
    qword (rorQwords x n) i = (qword x i).rotateRight (n.toNat % 64) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [rorQwords, qword_app0, qword_app1]

def xorRorOps (d a : XReg) (n : BitVec 8) : List VOp :=
  [.vbin .vpxor .l256 d d a, .vprorq .l256 d d n]

theorem xorRor_qw {d a : XReg} {n : BitVec 8} {m : Nat} (hn : n.toNat % 64 = m) (s : State)
    (r : XReg) (k : Nat) :
    qw (vrun (xorRorOps d a n) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight m else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRorOps, vrun, qw, lane_vprorq256, lane_vbin256, VBinOp.sse, ite_true]
  split
  · rw [qword_rorQwords _ _ h2, qword_pxor, hn]
  · rfl

theorem xorRor_keeps {d a r : XReg} (h : r ≠ d) (n : BitVec 8) (s : State) (l : Nat) :
    (vrun (xorRorOps d a n) s).lane r l = s.lane r l := by
  simp only [xorRorOps, vrun, lane_vprorq256, lane_vbin256, h, ite_false]

/-! ## The two halves of `G` -/

def half1Ops : List VOp :=
  [.vbin .vpaddq .l256 x0 x0 .xmm5, .vbin .vpaddq .l256 x0 x0 x1] ++
    (xorRorOps x3 x0 32 ++ ([.vbin .vpaddq .l256 x2 x2 x3] ++ xorRorOps x1 x2 24))

def half2Ops : List VOp :=
  [.vbin .vpaddq .l256 x0 x0 .xmm5, .vbin .vpaddq .l256 x0 x0 x1] ++
    (xorRorOps x3 x0 16 ++ ([.vbin .vpaddq .l256 x2 x2 x3] ++ xorRorOps x1 x2 63))

theorem half1_eq : half1 = half1Ops.map .vop := rfl

theorem half1_cols (s : State) (k : Nat) :
    cols (vrun half1Ops s) k = H1 (cols s k) (qw s .xmm5 k) := by
  simp only [half1Ops, vrun_append, vrun_cons_nil, vrun_pair]
  simp (disch := decide) only [cols, xorRor_qw (show (24 : BitVec 8).toNat % 64 = 24 from rfl),
    xorRor_qw (show (32 : BitVec 8).toNat % 64 = 32 from rfl), qw_add, ↓reduceIte, reduceCtorEq]
  rfl

theorem half2_cols (s : State) (k : Nat) :
    cols (vrun half2Ops s) k = H2 (cols s k) (qw s .xmm5 k) := by
  simp only [half2Ops, vrun_append, vrun_cons_nil, vrun_pair]
  simp (disch := decide) only [cols, xorRor_qw (show (63 : BitVec 8).toNat % 64 = 63 from rfl),
    xorRor_qw (show (16 : BitVec 8).toNat % 64 = 16 from rfl), qw_add, ↓reduceIte, reduceCtorEq]
  rfl

theorem half1_keeps {r : XReg} (hr : r ∉ halfRegs) (s : State) : Keeps r s (vrun half1Ops s) := by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, -⟩ := hr
  intro l
  simp only [half1Ops, vrun_append, xorRor_keeps h1, xorRor_keeps h3, vrun_cons_nil, vrun_pair,
    lane_vbin256, h0, h2, ite_false]

theorem half2_keeps {r : XReg} (hr : r ∉ halfRegs) (s : State) : Keeps r s (vrun half2Ops s) := by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, -⟩ := hr
  intro l
  simp only [half2Ops, vrun_append, xorRor_keeps h1, xorRor_keeps h3, vrun_cons_nil, vrun_pair,
    lane_vbin256, h0, h2, ite_false]

/-! ## A round -/

theorem not_mem_half {r : XReg} (h : r ∉ roundRegs) : r ∉ halfRegs := fun h' => h (by
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem half1_vf (s : State) : VF roundRegs s (vrun half1Ops s) :=
  VF.vrun fun _ hr => half1_keeps (not_mem_half hr) s

theorem half2_vf (s : State) : VF roundRegs s (vrun half2Ops s) :=
  VF.vrun fun _ hr => half2_keeps (not_mem_half hr) s

/-- The first half of `G` on the four quadwords, with the message vector `x`,
and the message vector `y` loaded for the second half, before `D`. -/
theorem g_ok {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16)
    (r k : Nat) (x y : Nat → W)
    (hx : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r k q)) 64 = x q)
    (hy : ∀ q < 4, s.mem.readW (p + BitVec.ofNat 64 (8 * msgWord r (k + 1) q)) 64 = y q)
    {D : Prog isa} {Q : State → Prop}
    (hD : ∀ s3, VF roundRegs s s3 → (∀ q < 4, cols s3 q = H1 (cols s q) (x q)) →
      (∀ q < 4, qw s3 .xmm5 q = y q) → WP isa D s3 Q) :
    WP isa (.seq (.block (msg r k)) (.seq (.block half1) (.seq (.block (msg r (k + 1))) D))) s Q := by
  refine WP.seq ((msg_ok r k hp hrd).mono fun s1 ⟨m1, f1⟩ => ?_)
  rw [half1_eq]
  refine WP.seq (block_vops_ok _ _ ?_)
  generalize hs2 : vrun half1Ops s1 = s2
  have f2 : VF roundRegs s1 s2 := hs2 ▸ half1_vf s1
  have c2 : ∀ k < 4, cols s2 k = H1 (cols s1 k) (qw s1 .xmm5 k) := fun k _ => hs2 ▸ half1_cols s1 k
  obtain ⟨e2, r2⟩ := VF.regs (VF.trans (f1.of_mem (rs' := roundRegs) (by decide)) f2) hp hrd
  refine WP.seq ((msg_ok r (k + 1) e2 r2).mono fun s3 ⟨m3, f3⟩ => ?_)
  refine hD s3 (((f1.of_mem (by decide)).trans f2).trans (f3.of_mem (by decide)))
    (fun q hq => ?_) (fun q hq => ?_)
  · rw [cols_of_vf f3 (by decide) (by decide) (by decide) (by decide) hq, c2 q hq,
      cols_of_vf f1 (by decide) (by decide) (by decide) (by decide) hq, m1 q hq, hx q hq]
  · rw [m3 q hq, f2.mem, f1.mem, hy q hq]

/-- The second half of `G`, after `g_ok`. -/
theorem h2_words {s s3 : State} {x y : Nat → W}
    (hc : ∀ q < 4, cols s3 q = H1 (cols s q) (x q)) (hy : ∀ q < 4, qw s3 .xmm5 q = y q) :
    words (vrun half2Ops s3) = mixCols x y (words s) :=
  words_of_cols fun q hq => by rw [half2_cols s3 q, hc q hq, hy q hq]

theorem half2_diag_eq : half2 ++ diagonalize = (half2Ops ++ diagOps).map .vop := by
  rw [List.map_append]; rfl

theorem half2_undiag_eq : half2 ++ undiagonalize = (half2Ops ++ undiagOps).map .vop := by
  rw [List.map_append]; rfl

/-- Round `r` on the rows in `ymm0`–`ymm3`, with the block at `rsi`. -/
theorem round_ok (r : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) :
    WP isa (round r) s fun t =>
      words t = Spec.Blake2.round Spec.Blake2.b (Spec.Blake2.blockAt 64 s.mem p) (words s) r ∧
      VF roundRegs s t := by
  unfold round
  refine g_ok hp hrd r 0 _ _ (fun q _ => msg_lo _ _ r q) (fun q _ => msg_lo1 _ _ r q)
    fun s3 f3 hc3 hy3 => ?_
  rw [half2_diag_eq]
  refine WP.seq (block_vops_ok _ _ ?_)
  generalize hs4 : vrun (half2Ops ++ diagOps) s3 = s4
  have f4 : VF roundRegs s s4 := by
    rw [← hs4, vrun_append]; exact (f3.trans (half2_vf s3)).trans (diag_vf _)
  have w4 : words s4 = rotIn (mixCols (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q)))
      (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (2 * q + 1))) (words s)) := by
    rw [← hs4, vrun_append, diag_words, h2_words hc3 hy3]
  obtain ⟨e4, r4⟩ := f4.regs hp hrd
  refine g_ok e4 r4 r 2
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))))
    (fun q => Spec.Blake2.blockAt 64 s.mem p (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))))
    (fun q _ => by rw [f4.mem]; exact msg_hi _ _ r q) (fun q _ => by rw [f4.mem]; exact msg_hi1 _ _ r q)
    fun s7 f7 hc7 hy7 => ?_
  rw [half2_undiag_eq]
  refine block_vops_ok _ _ ⟨?_, ?_⟩
  · rw [vrun_append, undiag_words, h2_words hc7 hy7, w4, round_lanes]
  · rw [vrun_append]; exact ((f4.trans f7).trans (half2_vf s7)).trans (undiag_vf _)

/-- Rounds `0 … n-1`. -/
theorem rounds_ok (n : Nat) {s : State} {p : Addr} (hp : s.gpr .rsi = p)
    (hrd : ∀ i ≤ 14, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 16) :
    WP isa (rounds n) s fun t =>
      words t = (List.range n).foldl (Spec.Blake2.round Spec.Blake2.b
        (Spec.Blake2.blockAt 64 s.mem p)) (words s) ∧ VF roundRegs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (ih.mono fun t ⟨wt, ft⟩ => ?_)
    obtain ⟨et, rt⟩ := ft.regs hp hrd
    refine (round_ok n et rt).mono fun u ⟨wu, fu⟩ => ⟨?_, ft.trans fu⟩
    rw [wu, wt, ft.mem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Blake2.X86_64.Avx512
