module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombStage
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Double4
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Ed25519's comb with AVX512_IFMA: an addition in the lanes

`vadd` adds the entry in the lanes of `ymm5–ymm9` to the point in the lanes of
`ymm0–ymm4`: the point there is then `pointAdd` of the two, as field elements
(`fe5`, `vadd_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord mul4 carry)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds EnvOK symOf symOf_eq lanes slotv CConsts carryNat fe5
  fe5_congr fe5_add fe5_sub fe5_carry fe5_mul carryI_wp carryF_wp mul4_wp mulS_eq mulV_nat mulV_ok
  mulV_keep mulV_st kbv kb_m vm vm_gpr vm_rd vm_wr envOK_of envOf envOf_m envOf_v lt64 run_ok
  stores_mq stores_outside limbNat xi_xr Ctx xor_mask pick2_tt pick2_ff)
open VG.Proof.X25519.X86_64 (Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4 sel4_lt)

/-! ## The negation -/

/-- The entry `(y - x, y + x, 2dt, 2Z)` negated: `(y + x, y - x, bias - 2dt, 2Z)`. -/
def negL (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 1 i
  | 1 => x 0 i
  | 2 => kbv i - x 2 i
  | _ => x 3 i

/-! ## An addition's blocks -/

/-- `(Y - X, Y + X, T, Z)` from `(X, Y, Z, T)`. -/
def aOp (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 1 i + (kbv i - x 0 i)
  | 1 => x 1 i + x 0 i
  | 2 => x 3 i + 0
  | _ => x 2 i + 0

theorem addB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) : EnvOK s addB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
  · simp only [addB]
    split
    · have := hx l hl r (by omega_arith); simp only [lanes, Nat.zero_add] at this; omega_arith
    · exact lt64 _
  · simp only [addB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact lt64 _
  · simp only [addB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact Nat.zero_le _

theorem vaddA_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block vaddA) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = aOp (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 5 ≤ r → r < 10 ∨ 14 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := addB_env hs hk hx
  have e : Sym.init.run vaddA = some vaddAS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ⟨h.eq, by rw [h.mem, vaddAS_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep hr hl (vaddAS_keep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := vaddAS_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith⟩
  rw [e, vaddAS_nat _ i hi l hl]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [aNat, aOp, lanes, Nat.zero_add, envOf_v, envOf_m hs, kb_m hk (show 0 < 4 by decide)]

/-- What `vstA` leaves: the lanes of `ymm0–ymm4` in `OPL`. -/
theorem vstA_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s) :
    WP isa (.block vstA) s fun s' => vm s s' = s' ∧ Outside base OPL 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPL l i = lanes s 0 l i) ∧
      (∀ r < 16, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run vstA = some vstAS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, ?_, fun l hl i hi => ?_, fun r hr l hl => h.keep hr hl (vstAS_keep r hr)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [vstAS_st]; decide)
  · have hm : ∀ i < 5, ((OPL + 32 * i), T.reg i) ∈ vstAS.st := by
      rw [vstAS_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [vstAS_st]; decide)
      (by rw [vstAS_st]; decide)]
    simp only [T.eval, lanes, Nat.zero_add]

/-- `(E, G, F, H) = (B - A, D + C, D - C, B + A)` from `(A, B, C, D)`. -/
def wOp (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 1 i + (kbv i - x 0 i)
  | 1 => x 3 i + x 2 i
  | 2 => x 3 i + (kbv i - x 2 i)
  | _ => x 1 i + x 0 i

/-- `(E, G, F, E)`. -/
def bO1 (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => wOp x 0 i
  | 1 => wOp x 1 i
  | 2 => wOp x 2 i
  | _ => wOp x 0 i

/-- `(F, H, G, H)`. -/
def bO2 (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => wOp x 2 i
  | 1 => wOp x 3 i
  | 2 => wOp x 1 i
  | _ => wOp x 3 i

theorem vaddB_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block vaddB) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = bO1 (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63 ∧
        lanes s' 5 l i = bO2 (lanes s 0) l i ∧ lanes s' 5 l i < 2 ^ 63) ∧
      (∀ r < 16, 14 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := addB_env hs hk hx
  have e : Sym.init.run vaddB = some vaddBS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ⟨h.eq, by rw [h.mem, vaddBS_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (vaddBS_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := vaddBS_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega_arith) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega_arith) hl o2
  obtain ⟨n1, n2⟩ := vaddBS_nat (envOf s) i hi l hl
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega_arith, ?_, by omega_arith⟩
  · rw [e1, n1]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [bOp1, wNat, bO1, wOp, lanes, Nat.zero_add, envOf_v, envOf_m hs,
        kb_m hk (show 0 < 4 by decide), kb_m hk (show 2 < 4 by decide)]
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [bOp2, wNat, bO2, wOp, lanes, Nat.zero_add, envOf_v, envOf_m hs,
        kb_m hk (show 2 < 4 by decide)]

/-! ## An addition -/

/-- The entry in the lanes of `ymm5–ymm9`. -/
def lanePt5 (s : State) : Spec.Ed25519.Point :=
  ⟨fe5 (lanes s 5 0), fe5 (lanes s 5 1), fe5 (lanes s 5 2), fe5 (lanes s 5 3)⟩

/-- The sum the lanes compute: `P` plus the cached point `e = (y - x, y + x, 2dt, 2z)`. -/
def vAddPt (P e : Spec.Ed25519.Point) : Spec.Ed25519.Point :=
  let a := (P.Y - P.X) * e.X
  let b := (P.Y + P.X) * e.Y
  let c := P.T * e.Z
  let dd := P.Z * e.T
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem aOp_fe (x : Nat → Nat → Nat) (hx : ∀ l < 4, ∀ i < 5, x l i < 2 ^ 61) :
    fe5 (aOp x 0) = fe5 (x 1) - fe5 (x 0) ∧ fe5 (aOp x 1) = fe5 (x 1) + fe5 (x 0) ∧
    fe5 (aOp x 2) = fe5 (x 3) ∧ fe5 (aOp x 3) = fe5 (x 2) :=
  ⟨fe5_sub (fun _ _ => rfl) (fun i hi => by have := hx 0 (by decide) i hi; have := kbv_ge i; omega_arith),
    fe5_add fun _ _ => rfl, fe5_congr fun _ _ => Nat.add_zero _, fe5_congr fun _ _ => Nat.add_zero _⟩

theorem wOp_fe (x : Nat → Nat → Nat) (hx : ∀ l < 4, ∀ i < 5, x l i < 2 ^ 61) :
    fe5 (wOp x 0) = fe5 (x 1) - fe5 (x 0) ∧ fe5 (wOp x 1) = fe5 (x 3) + fe5 (x 2) ∧
    fe5 (wOp x 2) = fe5 (x 3) - fe5 (x 2) ∧ fe5 (wOp x 3) = fe5 (x 1) + fe5 (x 0) :=
  ⟨fe5_sub (fun _ _ => rfl) (fun i hi => by have := hx 0 (by decide) i hi; have := kbv_ge i; omega_arith),
    fe5_add fun _ _ => rfl,
    fe5_sub (fun _ _ => rfl) (fun i hi => by have := hx 2 (by decide) i hi; have := kbv_ge i; omega_arith),
    fe5_add fun _ _ => rfl⟩

/-- `vadd`: the entry in the lanes of `ymm5–ymm9` added to the point in those of `ymm0–ymm4`. -/
theorem vadd_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : EConsts s.mem base) (hx : Small s) (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block vadd) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 1024 320 s.mem s'.mem ∧ Small s' ∧ lanePt s' = vAddPt (lanePt s) (lanePt5 s) := by
  have hcc : CConsts s.mem base := hk.toCConsts
  simp only [vadd, List.append_assoc]
  -- `(Y - X, Y + X, T, Z)`
  rw [WP.block_append_iff]
  refine WP.mono (vaddA_wp hs hc hcc hx) fun s₁ ⟨v₁, m₁, u₁, k₁⟩ => ?_
  have hs₁ : s₁.gpr .rdi = base := by rw [vm_gpr v₁]; exact hs
  have hc₁ : Ctx s₁ := by intro d hd; rw [vm_gpr v₁, vm_wr v₁]; exact hc d hd
  have hk₁ : EConsts s₁.mem base := by rw [m₁]; exact hk
  have l₁ := lanes_keep (r := 5) (s := s) (t := s₁) (by decide) fun q hq h1 h2 l hl =>
    k₁ q hq h1 (by omega_arith) l hl
  -- carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁ hc₁ hk₁.toCConsts fun l hl i hi => (u₁ l hl i hi).2)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [vm_gpr v₂]; exact hs₁
  have hc₂ : Ctx s₂ := by intro d hd; rw [vm_gpr v₂, vm_wr v₂]; exact hc₁ d hd
  have l₂ := lanes_keep (r := 5) (s := s₁) (t := s₂) (by decide) fun q hq h1 h2 l hl =>
    k₂ q hq (by omega_arith) (by omega_arith) l hl
  have p₂ : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (aOp (lanes s 0) l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1),
      fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega_arith),
      fe5_congr (fun i hi => (u₁ l hl i hi).1)]
  -- to `OPL`
  rw [WP.block_append_iff]
  refine WP.mono (vstA_wp hs₂ hc₂) fun s₃ ⟨v₃, o₃, u₃, k₃⟩ => ?_
  have hs₃ : s₃.gpr .rdi = base := by rw [vm_gpr v₃]; exact hs₂
  have hc₃ : Ctx s₃ := by intro d hd; rw [vm_gpr v₃, vm_wr v₃]; exact hc₂ d hd
  have l₃ := lanes_keep (r := 5) (s := s₂) (t := s₃) (by decide) fun q hq _ _ l hl => k₃ q hq l hl
  have e₃ : ∀ l < 4, ∀ i < 5, lanes s₃ 5 l i = lanes s 5 l i := fun l hl i hi => by
    rw [l₃ l hl i hi, l₂ l hl i hi, l₁ l hl i hi]
  -- the first product: `(A, B, C, D)`
  rw [WP.block_append_iff]
  refine WP.mono (mulLB_wp hs₃ hc₃ (fun l hl i hi => by rw [u₃ l hl i hi]; exact (u₂ l hl i hi).2)
    (fun l hl i hi => by rw [e₃ l hl i hi]; exact hy l hl i hi)) fun s₄ ⟨⟨v₄, m₄, u₄, _⟩, b₄⟩ => ?_
  have hs₄ : s₄.gpr .rdi = base := by rw [vm_gpr v₄]; exact hs₃
  have hc₄ : Ctx s₄ := by intro d hd; rw [vm_gpr v₄, vm_wr v₄]; exact hc₃ d hd
  have p₄ : ∀ l < 4, fe5 (lanes s₄ 0 l) = fe5 (aOp (lanes s 0) l) * fe5 (lanes s 5 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₄ l hl i hi).1),
      fe5_mul (fun i hi => by rw [u₃ l hl i hi]; exact (u₂ l hl i hi).2)
        (fun i hi => by rw [e₃ l hl i hi]; exact hy l hl i hi),
      fe5_congr (fun i hi => (u₃ l hl i hi).trans rfl), p₂ l hl, fe5_congr (fun i hi => e₃ l hl i hi)]
  have mo₄ : Outside base 1024 320 s.mem s₄.mem := by
    rw [m₄]; rw [m₂, m₁] at o₃; exact o₃.mono (by decide) (by decide)
  have hk₄ : EConsts s₄.mem base := hk.outside mo₄
  -- the second operands
  rw [WP.block_append_iff]
  refine WP.mono (vaddB_wp hs₄ hc₄ hk₄.toCConsts fun l hl i hi => (u₄ l hl i hi).2)
    fun s₅ ⟨v₅, m₅, u₅, k₅⟩ => ?_
  have hs₅ : s₅.gpr .rdi = base := by rw [vm_gpr v₅]; exact hs₄
  have hc₅ : Ctx s₅ := by intro d hd; rw [vm_gpr v₅, vm_wr v₅]; exact hc₄ d hd
  have hk₅ : EConsts s₅.mem base := by rw [m₅]; exact hk₄
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₅ hc₅ hk₅.toCConsts fun l hl i hi => (u₅ l hl i hi).2.2.2)
    fun s₆ ⟨v₆, m₆, u₆, k₆⟩ => ?_
  have hs₆ : s₆.gpr .rdi = base := by rw [vm_gpr v₆]; exact hs₅
  have hc₆ : Ctx s₆ := by intro d hd; rw [vm_gpr v₆, vm_wr v₆]; exact hc₅ d hd
  have hk₆ : EConsts s₆.mem base := by rw [m₆]; exact hk₅
  have l₆ := lanes_keep (r := 0) (s := s₅) (t := s₆) (by decide) fun q hq h1 h2 l hl =>
    k₆ q hq (by omega_arith) (by omega_arith) l hl
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₆ hc₆ hk₆.toCConsts fun l hl i hi => by
      rw [l₆ l hl i hi]; exact (u₅ l hl i hi).2.1) fun s₇ ⟨v₇, m₇, u₇, k₇⟩ => ?_
  have hs₇ : s₇.gpr .rdi = base := by rw [vm_gpr v₇]; exact hs₆
  have hc₇ : Ctx s₇ := by intro d hd; rw [vm_gpr v₇, vm_wr v₇]; exact hc₆ d hd
  have l₇ := lanes_keep (r := 5) (s := s₆) (t := s₇) (by decide) fun q hq h1 h2 l hl =>
    k₇ q hq (by omega_arith) (by omega_arith) l hl
  -- the first operand to `OPV`
  rw [WP.block_append_iff]
  refine WP.mono (dblC_wp hs₇ hc₇) fun s₈ ⟨v₈, o₈, u₈, k₈⟩ => ?_
  have hs₈ : s₈.gpr .rdi = base := by rw [vm_gpr v₈]; exact hs₇
  have hc₈ : Ctx s₈ := by intro d hd; rw [vm_gpr v₈, vm_wr v₈]; exact hc₇ d hd
  have l₈ := lanes_keep (r := 5) (s := s₇) (t := s₈) (by decide) fun q hq _ _ l hl => k₈ q hq l hl
  -- the second product
  refine WP.mono (mul4_wp (by decide) (mulS_eq OPV _) (mulV_nat) mulV_ok mulV_keep mulV_st hs₈ hc₈
    (fun l hl i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
    (fun l hl i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2))
    fun s₉ ⟨v₉, m₉, u₉, _⟩ => ?_
  refine ⟨by rw [vm_gpr v₉, vm_gpr v₈, vm_gpr v₇, vm_gpr v₆, vm_gpr v₅, vm_gpr v₄, vm_gpr v₃, vm_gpr v₂,
      vm_gpr v₁],
    by rw [vm_rd v₉, vm_rd v₈, vm_rd v₇, vm_rd v₆, vm_rd v₅, vm_rd v₄, vm_rd v₃, vm_rd v₂, vm_rd v₁],
    by rw [vm_wr v₉, vm_wr v₈, vm_wr v₇, vm_wr v₆, vm_wr v₅, vm_wr v₄, vm_wr v₃, vm_wr v₂, vm_wr v₁], ?_,
    fun l hl i hi => (u₉ l hl i hi).2, ?_⟩
  · rw [m₇, m₆, m₅] at o₈
    rw [m₉]; exact mo₄.trans (o₈.mono (by decide) (by decide))
  have p₉ : ∀ l < 4, fe5 (lanes s₉ 0 l) = fe5 (bO1 (lanes s₄ 0) l) * fe5 (bO2 (lanes s₄ 0) l) :=
    fun l hl => by
    rw [fe5_congr (fun i hi => (u₉ l hl i hi).1),
      fe5_mul (fun i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
        (fun i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2),
      fe5_congr (fun i hi => u₈ l hl i hi), fe5_congr (fun i hi => (u₇ l hl i hi).1),
      fe5_carry _ (by rw [l₆ l hl 4 (by decide)]; have := (u₅ l hl 4 (by decide)).2.1; omega_arith),
      fe5_congr (fun i hi => (l₆ l hl i hi).trans (u₅ l hl i hi).1),
      fe5_congr (fun i hi => (l₈ l hl i hi).trans (l₇ l hl i hi)),
      fe5_congr (fun i hi => (u₆ l hl i hi).1),
      fe5_carry _ (by have := (u₅ l hl 4 (by decide)).2.2.2; omega_arith),
      fe5_congr (fun i hi => (u₅ l hl i hi).2.2.1)]
  obtain ⟨w0, w1, w2, w3⟩ := wOp_fe (lanes s₄ 0) fun l hl i hi => (u₄ l hl i hi).2
  obtain ⟨a0, a1, a2, a3⟩ := aOp_fe (lanes s 0) fun l hl i hi => by have := hx l hl i hi; omega_arith
  have hA := p₄ 0 (by decide); have hB := p₄ 1 (by decide); have hC := p₄ 2 (by decide)
  have hD := p₄ 3 (by decide)
  rw [a0] at hA; rw [a1] at hB; rw [a2] at hC; rw [a3] at hD
  simp only [lanePt, lanePt5, vAddPt]
  rw [p₉ 0 (by decide), p₉ 1 (by decide), p₉ 2 (by decide), p₉ 3 (by decide)]
  rw [show bO1 (lanes s₄ 0) 0 = wOp (lanes s₄ 0) 0 from rfl, show bO1 (lanes s₄ 0) 1 = wOp (lanes s₄ 0) 1 from rfl,
    show bO1 (lanes s₄ 0) 2 = wOp (lanes s₄ 0) 2 from rfl, show bO1 (lanes s₄ 0) 3 = wOp (lanes s₄ 0) 0 from rfl,
    show bO2 (lanes s₄ 0) 0 = wOp (lanes s₄ 0) 2 from rfl, show bO2 (lanes s₄ 0) 1 = wOp (lanes s₄ 0) 3 from rfl,
    show bO2 (lanes s₄ 0) 2 = wOp (lanes s₄ 0) 1 from rfl, show bO2 (lanes s₄ 0) 3 = wOp (lanes s₄ 0) 3 from rfl,
    w0, w1, w2, w3, hA, hB, hC, hD]

/-! ## An entry, from its words -/

/-- A cached point negated if `b`: `(y - x, y + x, 2dt, 2z)` becomes `(y + x, y - x, -2dt, 2z)`. -/
def negIf (b : Bool) (e : Spec.Ed25519.Point) : Spec.Ed25519.Point :=
  if b then ⟨e.Y, e.X, 0 - e.Z, e.T⟩ else e

end VG.Proof.Ed25519.X86_64.Ifma
