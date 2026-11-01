module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Table
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-!
# GHASH on RISC-V: the multiplications

Untrusted: everything here is checked by Lean. With the table `Tab` in the
frame at `B`, a step of Algorithm 1 (`mulStep_ok`: `Z := Z ⊕ Vᵢ` if bit `i`
of `x` is set), a byte of `x` (`mulBody_ok`), and the product
(`mul_loop`).
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (mulSteps)

/-- The registers the multiplication writes. -/
def mulRegs : List Reg := [Z0, Z1, X0, X1, U0, U1, M, T, P]

/-- After `j` bytes of `x • h`, from the state `sB` (where the table is in
memory): `Z` is Algorithm 1's after `8 j` steps, `x` is shifted left by
`j` bytes, and `P` is at entry `8 j`. -/
structure MulInv (x h : Block) (B : Addr) (sB : State) (j : Nat) (s : State) : Prop where
  z : w2 (s.gpr Z0) (s.gpr Z1) = (mulSteps x h (8 * j)).1
  x : w2 (s.gpr X0) (s.gpr X1) = x <<< (8 * j)
  p : s.gpr P = B + BitVec.ofNat 64 (128 * j)
  e : s.gpr E = B + BitVec.ofNat 64 2048
  mem : s.mem = sB.mem
  keep : ∀ r, r ∉ mulRegs → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

/-- Within byte `j`, after `k` of its steps. -/
structure StepInv (x h : Block) (B : Addr) (sB : State) (j k : Nat) (s : State) : Prop where
  z : w2 (s.gpr Z0) (s.gpr Z1) = (mulSteps x h (8 * j + k)).1
  x : w2 (s.gpr X0) (s.gpr X1) = x <<< (8 * j)
  p : s.gpr P = B + BitVec.ofNat 64 (128 * j)
  e : s.gpr E = B + BitVec.ofNat 64 2048
  mem : s.mem = sB.mem
  keep : ∀ r, r ∉ mulRegs → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem mulStep_ok {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {j k : Nat} (hj : j < 16) (hk : k < 8) {s : State} (hs : StepInv x h B sB j k s) :
    WP isa (.block (Impl.Gcm.RISCV64.mulStep k)) s (StepInv x h B sB j (k + 1)) := by
  have hF' : FrameOk B s := hF.of_wr hs.wr
  have a₁ : s.gpr P + BitVec.ofNat 64 (16 * k) = B + BitVec.ofNat 64 (16 * (8 * j + k)) := by
    rw [hs.p, ptr_off]; congr 2; omega
  have a₂ : s.gpr P + BitVec.ofNat 64 (16 * k + 8) = B + BitVec.ofNat 64 (16 * (8 * j + k) + 8) := by
    rw [hs.p, ptr_off]; congr 2; omega
  refine wp_sll (by omega) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => ?_
  refine wp_ld (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₁)
    (hF.al8 (by omega) (by omega)) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hF'.inR (by omega))
    fun s₃ u₃ => ?_
  refine wp_ld (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₂)
    (hF.al8 (by omega) (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hF'.inR (by omega)) fun s₄ u₄ => ?_
  refine wp_and fun s₅ u₅ => wp_and fun s₆ u₆ => wp_xor fun s₇ u₇ => wp_xor fun s₈ u₈ =>
    WP.block_nil ?_
  have mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, mem₃]
  have hm : s₂.gpr M = mask ((x <<< (8 * j)).getMsbD k) := by
    rw [u₂.gpr, u₁.gpr, mask_shl _ (by omega), ← hs.x, getMsbD_w2 _ _ (by omega)]
  have hm₄ : s₄.gpr M = mask (x.getMsbD (8 * j + k)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), hm, getMsbD_shl8]
  have hu0 : s₄.gpr U0 = hi (Proof.Gcm.RISCV64.vs h (8 * j + k)) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, hs.mem]; exact (ht _ (by omega)).1
  have hu1 : s₄.gpr U1 = lo (Proof.Gcm.RISCV64.vs h (8 * j + k)) := by
    rw [u₄.gpr, mem₃, hs.mem]; exact (ht _ (by omega)).2
  have g₄ : ∀ r, r ≠ M → r ≠ U0 → r ≠ U1 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h1]
  have z0 : s₈.gpr Z0 = s.gpr Z0 ^^^ (hi (vs h (8 * j + k)) &&& mask (x.getMsbD (8 * j + k))) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, hu0, hm₄, g₄ _ (by decide) (by decide) (by decide)]
  have z1 : s₈.gpr Z1 = s.gpr Z1 ^^^ (lo (vs h (8 * j + k)) &&& mask (x.getMsbD (8 * j + k))) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₅.other _ (by decide), hu1, hm₄, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide) (by decide) (by decide)]
  have g₈ : ∀ r, r ≠ M → r ≠ U0 → r ≠ U1 → r ≠ Z0 → r ≠ Z1 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₈.other _ h5, u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, g₄ _ h1 h2 h3]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [z0, z1, acc_mask, hs.z, w2_hi_lo, ← Proof.Gcm.RISCV64.mulSteps_fst_succ]; rfl
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.x
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.p
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.e
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, mem₄]; exact hs.mem
  · simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈ _ hr.2.2.2.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.1 hr.2.1]; exact hs.keep r
      (by simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hs.rd
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hs.wr
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; exact hs.sp

theorem mulBody_ok {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {j : Nat} (hj : j < 16) {s : State} (hs : MulInv x h B sB j s) :
    WP isa (.block mulBody) s (MulInv x h B sB (j + 1)) := by
  rw [mulBody, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) (StepInv x h B sB j)
    (fun k s' hk hi => mulStep_ok hF ht hj hk hi) 8 (Nat.le_refl _) s
    ⟨by simpa using hs.z, hs.x, hs.p, hs.e, hs.mem, hs.keep, hs.rd, hs.wr, hs.sp⟩) fun s₁ h₁ => ?_
  refine wp_sll (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ => wp_or fun s₄ u₄ =>
    wp_sll (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ X0 → r ≠ X1 → r ≠ T → r ≠ P → s₆.gpr r = s₁.gpr r := fun r a b c d => by
    rw [u₆.other _ d, u₅.other _ b, u₄.other _ a, u₃.other _ c, u₂.other _ a]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), h₁.z]; rfl
  · rw [u₆.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide), u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w2_shl8, h₁.x, ← BitVec.shiftLeft_add,
      Nat.mul_succ]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), h₁.p, ptr_off]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₁.e
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.mem
  · simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g _ hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]
    exact h₁.keep r (by simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact h₁.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact h₁.wr
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact h₁.sp

theorem mul_loop {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {s : State} (hs : MulInv x h B sB 0 s) :
    WP isa (.loop (.block mulBody) (.ne P E)) s (MulInv x h B sB 16) := by
  refine WP.loop (M := isa) (fun n s' => ∃ j, n = 16 - j ∧ j < 16 ∧ MulInv x h B sB j s')
    (fun n s' ⟨j, hn, hj, hi⟩ => WP.mono (mulBody_ok hF ht hj hi) fun s'' hi' => ?_) 16 s
    ⟨0, rfl, by decide, hs⟩
  have hev : isa.eval (.ne P E) s'' = some (decide (j + 1 ≠ 16)) := by
    show some (s''.gpr P != s''.gpr E) = _
    rw [hi'.p, hi'.e, end_ne B hj]
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hev, decide_eq_true hl], 16 - (j + 1), by omega, j + 1, rfl, by omega, hi'⟩

end VG.Proof.Gcm.RISCV64
