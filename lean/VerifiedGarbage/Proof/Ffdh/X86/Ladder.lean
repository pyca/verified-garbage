module

public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH on i686: powers of two

`ladderStep_ok`: a bit of x. The accumulator, where it is `y R mod M`, is
squared to `y² R mod M` and doubled modulo `M`, and the doubled one replaces
it under the bit's mask: `y² 2^b R mod M`. `ladderPower_ok`: over the `8 L` bits of
x's public length from the top, from Montgomery one, slot 6 is
`2^x mod M` (`ladder_exp`: the bits of x above bit `k`, doubled, and bit
`k`, are the bits above bit `k − 1`). `ladderCall_ok` is the call, and
`twoTest_ok` the test of the generator that chooses it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Ladder

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86
open VG.Proof.Ffdh.X86.Cached (bit_ok storeW_ok readW_ok)
open VG.Proof.Rsa.FixedBaseComb (bit)

/-- The bits of `x` above bit `k`, doubled, and bit `k`: the bits above bit `k − 1`. -/
theorem ladder_exp (x k : Nat) : (2 ^ (x / 2 ^ (k + 1))) ^ 2 * 2 ^ bit x k = 2 ^ (x / 2 ^ k) := by
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  unfold bit
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega_arith

/-- A bit below bit `N` of `x` is the bit of `x mod 2^N`. -/
theorem bit_mod (x : Nat) {N k : Nat} (hk : k < N) : bit (x % 2 ^ N) k = bit x k := by
  unfold bit
  rw [show 2 ^ N = 2 ^ k * 2 ^ (N - k) by rw [← Nat.pow_add]; congr 1; omega_arith, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ ⟨2 ^ (N - k - 1), by rw [← Nat.pow_succ']; congr 1; omega_arith⟩]

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A multiplication into slot 6 changes what a power does. -/
theorem pw_mul {sp : BitVec 32} {m m' : Mem} (F : Frame (frameR base sp (mulR len .wide 6)) m m') :
    Frame (frameR base sp (pwR len .wide)) m m' :=
  frameR_mono F fun p hp => by
    simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [pwR]

/-- A sum into slot 7 changes what a power does. -/
theorem pw_add {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp [(lo len (.slot .wide 1), bc len .wide + 4), (lo len (.slot .wide 7), bc len .wide)])
      m m') : Frame (frameR base sp (pwR len .wide)) m m' :=
  frameR_widen F fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨(lo len (.slot .wide 1), 3 * bc len .wide + 56), by simp [pwR], Nat.le_refl _, by dsimp only; omega_arith⟩
    · exact ⟨(lo len (.slot .wide 7), bc len .wide), by simp [pwR], Nat.le_refl _, Nat.le_refl _⟩

/-- x (slot 13) through a power's writes. -/
theorem pw_x (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (pwR len .wide)) m m') (R : CallRoom sp base bytes) :
    sv m' base len .wide 13 = sv m base len .wide 13 :=
  (kept_ops h (stR_widen F (pwR_in h .wide 0)) R).slots 13 (by decide) (by decide) (by simp)

/-- One (slot 3) through a power's writes. -/
theorem pw_one (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (pwR len .wide)) m m') (R : CallRoom sp base bytes) :
    sv m' base len .wide 3 = sv m base len .wide 3 := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  obtain e20 := lo_wide len 20
  obtain e1 := lo_wide len 1
  obtain e3 := lo_wide len 3
  obtain e5 := lo_wide len 5
  obtain e6 := lo_wide len 6
  obtain e7 := lo_wide len 7
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega_arith) ?_ (pwR_fit h .wide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [winOff] <;> omega_arith

/-- The bit `eax` as a mask in the window word. -/
theorem bitMask_ok (h : In Ex base bytes len args s) {b : Nat} (hb : (s.gpr .eax).toNat % 2 = b) :
    WP isa (.block bitMask) s fun u => In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      w32 u.mem base winOff = (cmask (decide (b = 1))).toNat ∧ Keeps [.eax, .ecx] s u := by
  have wo : winOff = 4 := rfl
  have nb : numBase = 3336 := rfl
  unfold bitMask
  refine wp_logicS (.inl rfl) rfl fun s₁ U₁ => wp_movS rfl fun s₂ U₂ _ => wp_subS rfl fun s₃ U₃ _ => ?_
  obtain K₃ : Keeps [.eax, .ecx] s s₃ :=
    ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))
  obtain m₃ : s₃.mem = s.mem := by rw [U₃.mem, U₂.mem, U₁.mem]
  obtain e₃ : s₃.gpr .ecx = cmask (decide (b = 1)) := by
    rw [U₃.gpr, U₂.gpr, U₂.other _ (by decide), U₁.gpr]
    exact (zero_sub_and_one (s.gpr .eax)).trans (by rw [hb])
  refine WP.mono (storeW_ok (h.regs K₃ m₃) (d := winOff) (by omega_arith) .ecx) fun u ⟨I, O, W, K⟩ =>
    ⟨I, by rw [m₃] at O; exact O, by rw [W, e₃], K₃.trans (K.mono (by decide))⟩

/-- One bit of x: the accumulator, where it is `y R mod M`, to `y² 2^b R mod M` for the bit `b` at
`n − 1`; it stays below `M`, and the count is down one. -/
theorem ladderStep_ok {M : Nat} (C : CtxOk Ex base bytes len args .wide M s) {n : Nat}
    (hlt : sv s.mem base len .wide 6 < M) (hn0 : 0 < n) (hn : n < 2 ^ 32)
    (he : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa ladderStep s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧ Frame (frameR base (s.gpr .esp) (pwR len .wide)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 (n - 1) ∧ u.zf = some (decide (n = 1)) ∧
      sv u.mem base len .wide 6 < M ∧
      ∀ y, sv s.mem base len .wide 6 = y * 2 ^ (8 * bc len .wide) % M → sv u.mem base len .wide 6 =
        y ^ 2 * 2 ^ bit (sv s.mem base len .wide 13) (n - 1) * 2 ^ (8 * bc len .wide) % M := by
  have h := C.inp
  have P1 := C.gt
  have cp := C.coprime
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain e1 := lo_wide len 1
  obtain e6 := lo_wide len 6
  obtain e7 := lo_wide len 7
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold ladderStep
  -- The square.
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hlt) fun s₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  generalize hZ : sv s₁.mem base len .wide 6 = Z at L₁ V₁
  obtain Y₁ : ∀ y, sv s.mem base len .wide 6 = y * 2 ^ (8 * bc len .wide) % M →
      Z = y ^ 2 * 2 ^ (8 * bc len .wide) % M := fun y hy => by
    obtain v := VG.Proof.Bignum.mont_cancel cp (o := Z) (c := y ^ 2 * 2 ^ (8 * bc len .wide))
      (by rw [V₁, hy, ← Nat.mul_mod, Nat.mul_mul_mul_comm, Nat.pow_two, Nat.mul_assoc (y * y)])
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain x₁ : sv s₁.mem base len .wide 13 = sv s.mem base len .wide 13 := pw_x h (pw_mul F₁) h.room
  -- The bit's index, the bit and its mask.
  refine WP.seq (wp_subS rfl fun s₂ U₂ _ => WP.block_nil ?_)
  obtain esi₂ : s₂.gpr .esi = BitVec.ofNat 32 (n - 1) := by
    rw [U₂.gpr, K₁.1 _ (by decide), he]; exact VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0
  obtain C₂ : CtxOk Ex base bytes len args .wide M s₂ := C₁.regs U₂.keeps U₂.mem
  refine WP.seq (WP.mono (bit_ok C₂.inp (k := n - 1) (by omega_arith) esi₂) fun s₃ ⟨m₃, K₃, e₃⟩ => ?_)
  rw [U₂.mem, x₁] at e₃
  generalize bit (sv s.mem base len .wide 13) (n - 1) = b at e₃ ⊢
  obtain C₃ : CtxOk Ex base bytes len args .wide M s₃ := C₂.regs K₃ m₃
  refine WP.seq (WP.mono (bitMask_ok C₃.inp e₃) fun s₄ ⟨I₄, O₄, W₄, K₄⟩ => ?_)
  obtain F₄ : Frame (frameR base (s₃.gpr .esp) [(winOff, 4)]) s₃.mem s₄.mem :=
    frameR_of_outside O₄ (by omega_arith) (List.mem_singleton_self _)
  obtain C₄ : CtxOk Ex base bytes len args .wide M s₄ := C₃.keepF2 K₄ (by decide) (by decide) F₄
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; dsimp only; omega_arith)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by omega_arith, by dsimp only; omega_arith⟩)
  obtain m₁₃ : s₃.mem = s₁.mem := by rw [m₃, U₂.mem]
  obtain six₄ : sv s₄.mem base len .wide 6 = Z := by
    simp only [sv]; rw [O₄.val32 (.inr (by omega_arith)) (by omega_arith), m₁₃]; exact hZ
  -- Twice the accumulator, modulo `M`.
  obtain lt₄ : sv s₄.mem base len .wide 6 < sv s₄.mem base len .wide 0 := by
    rw [six₄, C₄.mod]; exact L₁
  refine WP.seq (WP.mono (addMod_ok C₄.inp .wide (o := 7) (a := 6) (b := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) lt₄ lt₄) fun s₅ ⟨F₅, V₅, K₅⟩ => ?_)
  rw [six₄, C₄.mod] at V₅
  obtain fit₅ : ∀ p ∈ [(lo len (.slot .wide 1), bc len .wide + 4), (lo len (.slot .wide 7), bc len .wide)],
      p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain keep₅ : ∀ d k, d + 4 * k ≤ bytes → (d + 4 * k ≤ lo len (.slot .wide 1) ∨
      lo len (.slot .wide 1) + (bc len .wide + 4) ≤ d) → (d + 4 * k ≤ lo len (.slot .wide 7) ∨
      lo len (.slot .wide 7) + bc len .wide ≤ d) → val32 s₅.mem base d k = val32 s₄.mem base d k :=
    fun d k hd h1 h7 => frameR_val32 F₅ C₄.inp.room nw hd (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> assumption) fit₅
  obtain C₅ : CtxOk Ex base bytes len args .wide M s₅ := C₄.keepF K₅ (by decide) (by decide) F₅ fit₅
    (by intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith)
  obtain six₅ : sv s₅.mem base len .wide 6 = Z := by
    simp only [sv]; rw [keep₅ _ _ (by omega_arith) (.inr (by omega_arith)) (.inl (by omega_arith))]; exact six₄
  obtain W₅ : w32 s₅.mem base winOff = (cmask (decide (b = 1))).toNat := by
    rw [← w32_val32_one, keep₅ _ _ (by omega_arith) (.inl (by omega_arith)) (.inl (by omega_arith)), w32_val32_one]
    exact W₄
  -- The doubled one under the bit's mask.
  refine WP.seq (wp_movS (readW_ok C₅.inp (d := winOff) (by omega_arith) W₅ (BitVec.isLt _)) fun s₆ U₆ _ =>
    WP.block_nil ?_)
  obtain ecx₆ : s₆.gpr .ecx = cmask (decide (b = 1)) := by
    rw [U₆.gpr]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)])
  obtain C₆ : CtxOk Ex base bytes len args .wide M s₆ := C₅.regs U₆.keeps U₆.mem
  refine WP.seq (WP.mono (select_ok (x := .slot .wide 7) (d := .slot .wide 6) C₆.inp (one_ok .wide)
    (by rw [cb1]; omega_arith) (by rw [cb1]; omega_arith) (by rw [cb1]; simp only [Apart]; omega_arith) ecx₆)
    fun s₇ ⟨O₇, V₇, K₇⟩ => ?_)
  simp only [cb1, cw1] at O₇ V₇
  obtain C₇ : CtxOk Ex base bytes len args .wide M s₇ := C₆.keepF K₇ (by decide) (by decide)
    (ws := [(lo len (.slot .wide 6), bc len .wide)]) (frameR_of_outside O₇ (by omega_arith) (by simp))
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega_arith)
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega_arith)
  refine wp_testS rfl fun u T z => WP.block_nil ?_
  -- What the bit's step leaves.
  obtain K₂₇ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s₂ s₇ :=
    ((((K₃.mono (by decide)).trans (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans
      (U₆.keeps.mono (by decide))).trans (K₇.mono (by decide))
  obtain esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (n - 1) := by rw [K₂₇.1 _ (by decide), esi₂]
  obtain sp₃ : s₃.gpr .esp = s.gpr .esp := by
    rw [K₃.1 _ (by decide), U₂.other _ (by decide), K₁.1 _ (by decide)]
  obtain sp₄ : s₄.gpr .esp = s.gpr .esp := by rw [K₄.1 _ (by decide), sp₃]
  rw [sp₃] at F₄
  rw [sp₄] at F₅
  obtain G₄ : Frame (frameR base (s.gpr .esp) (pwR len .wide)) s₁.mem s₄.mem := by
    rw [← m₁₃]
    exact frameR_mono F₄ fun p hp => by obtain rfl := List.mem_singleton.mp hp; simp [pwR]
  obtain G₇ : Frame (frameR base (s.gpr .esp) (pwR len .wide)) s₅.mem s₇.mem := by
    rw [← U₆.mem]; exact frameR_of_outside O₇ (by omega_arith) (by simp [pwR])
  refine ⟨C₇.regs (T.keeps []) T.mem, by rw [T.mem]; exact (((pw_mul F₁).trans G₄).trans (pw_add F₅)).trans G₇,
    ((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      ((K₂₇.mono (by decide)).trans ((T.keeps []).mono (by decide))),
    by rw [(T.keeps []).1 _ (by decide), esi₇], ?_, ?_, ?_⟩
  · rw [z, BitVec.and_self, esi₇]
    congr 1
    by_cases e : n = 1
    · subst e; rfl
    · rw [decide_eq_false e]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro c
      have := congrArg BitVec.toNat c
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact e (by have : (0 : BitVec 32).toNat = 0 := rfl; omega_arith)
  · simp only [sv] at six₅ V₅ ⊢
    rw [T.mem, V₇, U₆.mem]
    rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl
    · simp only [show decide ((0 : Nat) = 1) = false from by decide, Bool.false_eq_true, ↓reduceIte]
      rw [six₅]; exact L₁
    · rw [V₅]
      simp only [decide_true, ↓reduceIte]
      exact Nat.mod_lt _ (by omega_arith)
  · intro y hy
    obtain eZ := Y₁ y hy
    simp only [sv] at six₅ V₅ ⊢
    rw [T.mem, V₇, U₆.mem]
    rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl
    · simp only [show decide ((0 : Nat) = 1) = false from by decide, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.pow_zero, Nat.mul_one, six₅]; exact eZ
    · rw [V₅, eZ, ← Nat.add_mod, Nat.pow_one, Nat.mul_right_comm, Nat.mul_two]
      simp only [decide_true, ↓reduceIte]

/-- Slot 6 two to the power of x's low `8 L` bits (x in slot 13, the public length `L` in argument 11)
modulo `M`. -/
theorem ladderPower_ok {M L : Nat} (C : CtxOk Ex base bytes len args .wide M s)
    (h3 : sv s.mem base len .wide 3 = 1) (h4 : sv s.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M)
    (hx : args 11 = BitVec.ofNat 32 L) (hL0 : 0 < L) (hL : L ≤ 1024) :
    WP isa ladderPower s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧ Frame (frameR base (s.gpr .esp) (pwR len .wide)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len .wide 6 = 2 ^ (sv s.mem base len .wide 13 % 2 ^ (8 * L)) % M := by
  have h := C.inp
  have hM := C.gt
  have cp := C.coprime
  obtain RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  generalize hX : sv s.mem base len .wide 13 = x
  unfold ladderPower
  -- One in Montgomery form into slot 6.
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact hM)) fun s₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  obtain Y₁ : sv s₁.mem base len .wide 6 = 2 ^ (8 * bc len .wide) % M := by
    obtain v := VG.Proof.Bignum.mont_cancel cp (o := sv s₁.mem base len .wide 6) (c := 2 ^ (8 * bc len .wide))
      (by rw [V₁, h4, h3, Nat.mul_one, Nat.mod_mod, RR])
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- The count of bits.
  unfold bitCount
  refine WP.seq (wp_movS (C₁.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ =>
    wp_addS rfl fun t₃ a₃ _ => wp_addS rfl fun s₅ a₄ _ => WP.block_nil ?_)
  obtain K₅ : Keeps [.esi] s₁ s₅ :=
    ((a₁.keeps.trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans (a₄.keeps.mono (by decide))
  obtain m₅ : s₅.mem = s₁.mem := by rw [a₄.mem, a₃.mem, a₂.mem, a₁.mem]
  obtain esi₅ : s₅.gpr .esi = BitVec.ofNat 32 (8 * L) := by
    rw [a₄.gpr, a₃.gpr, a₂.gpr, a₁.gpr, hx, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1; omega_arith
  obtain C₅ : CtxOk Ex base bytes len args .wide M s₅ := C₁.regs K₅ m₅
  obtain sp₅ : s₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), sp₁]
  obtain x₅ : sv s₅.mem base len .wide 13 = x := by rw [sv, m₅]; exact (pw_x h (pw_mul F₁) h.room).trans hX
  -- The bits.
  refine WP.seq (WP.mono (PublicRt.countLoop (N := 8 * L) (by omega_arith) (fun j t =>
      CtxOk Ex base bytes len args .wide M t ∧ Frame (frameR base (s.gpr .esp) (pwR len .wide)) s₅.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₅ t ∧ t.gpr .esi = BitVec.ofNat 32 (8 * L - j) ∧
      sv t.mem base len .wide 6 = 2 ^ (x % 2 ^ (8 * L) / 2 ^ (8 * L - j)) * 2 ^ (8 * bc len .wide) % M)
    (fun j t hj ⟨Ct, Ft, Kt, et, Yt⟩ => WP.mono (ladderStep_ok Ct
      (by rw [Yt]; exact Nat.mod_lt _ (by omega_arith)) (by omega_arith) (by omega_arith) et)
      fun u ⟨Cu, Fu, Ku, eu, zu, _, Yu⟩ => ?_)
    ⟨C₅, Frame.refl _ _, Keeps.refl _ _, by rw [esi₅, Nat.sub_zero],
      by rw [sv, m₅, Nat.sub_zero, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.pow_zero,
        Nat.one_mul]; exact Y₁⟩)
    fun s₆ ⟨C₆, F₆, K₆, _, Y₆⟩ => ?_)
  · have spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₅]
    rw [spt] at Fu
    obtain xt : sv t.mem base len .wide 13 = x := (pw_x C₅.inp Ft (sp₅ ▸ C₅.inp.room)).trans x₅
    rw [xt] at Yu
    refine ⟨⟨Cu, Ft.trans Fu, Kt.trans Ku, by rw [eu, Nat.sub_sub], ?_⟩,
      by rw [zu]; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩
    rw [Yu _ Yt, Nat.sub_sub, ← bit_mod x (N := 8 * L) (by omega_arith),
      show 8 * L - j = 8 * L - (j + 1) + 1 by omega_arith, ladder_exp]
  -- Out of Montgomery form.
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at Y₆
  obtain F₀₆ : Frame (frameR base (s.gpr .esp) (pwR len .wide)) s.mem s₆.mem := by
    rw [m₅] at F₆; exact (pw_mul F₁).trans F₆
  obtain one₆ : sv s₆.mem base len .wide 3 = 1 := (pw_one h F₀₆ h.room).trans h3
  obtain sp₆ : s₆.gpr .esp = s.gpr .esp := by rw [K₆.1 _ (by decide), sp₅]
  refine WP.mono (cmul_ok C₆ (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [one₆]; exact hM)) fun u ⟨Cu, Ku, Fu, Lu, Vu⟩ => ⟨Cu, ?_, ?_, ?_⟩
  · rw [sp₆] at Fu; exact F₀₆.trans (pw_mul Fu)
  · exact ((K₁.mono (by decide)).trans (K₅.mono (by decide))).trans (K₆.trans (Ku.mono (by decide)))
  · rw [Y₆, one₆, Nat.mul_one, Nat.mod_mod] at Vu
    obtain v := VG.Proof.Bignum.mont_cancel cp Vu
    rwa [Nat.mod_eq_of_lt Lu] at v

/-! ## The call, and the generator's test -/

theorem ladderBody_noSp :
    NoSp (.seq (.block ((List.range 18).flatMap copyArg)) ladderPower : Prog isa) :=
  NoSp.of_all (by rsa_stack_shape)

/-- `ladderPower`, called: slot 6 two to the power of x's low `8 L` bits, with the changes within a
stage's. -/
theorem ladderCall_ok {M L : Nat} (C : CtxOk Ex base bytes len args .wide M s)
    (RF : RoomF (s.gpr .esp) base bytes) (h3 : sv s.mem base len .wide 3 = 1)
    (h4 : sv s.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M) (hx : args 11 = BitVec.ofNat 32 L)
    (hL0 : 0 < L) (hL : L ≤ 1024) :
    WP isa ladderCall s fun u => CtxOk Ex base bytes len args .wide M u ∧
      Frame (frameF base (s.gpr .esp) (pwR len .wide)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len .wide 6 = 2 ^ (sv s.mem base len .wide 13 % 2 ^ (8 * L)) % M := by
  unfold ladderCall
  refine WP.mono (argCall_ok ladderBody_noSp C.inp RF (pwR_fit C.inp .wide)
    (R := WinMem base len M (2 ^ (sv s.mem base len .wide 13 % 2 ^ (8 * L)) % M))
    (fun W F hr => winMem_below C.inp RF W F hr) fun u hu Fs => ?_)
    fun w ⟨I, F, K, a, b, c⟩ => ⟨⟨I, a, C.gt, C.odd, b⟩, F, K, c⟩
  have e := fun j (hj : j ≤ 27) => frameF_sv C.inp RF Fs hj
  refine WP.mono (ladderPower_ok (ctx_callee C RF hu Fs) (by rw [e 3 (by decide)]; exact h3)
    (by rw [e 4 (by decide)]; exact h4) hx hL0 hL)
    fun v ⟨Cv, F, K, Y⟩ => ⟨F, K, Cv.mod, Cv.inv, ?_⟩
  rw [Y, e 13 (by decide)]

/-- The generator's test: ZF set exactly when g (slot 10) is not two; slot 17 changes. -/
theorem twoTest_ok (h : In Ex base bytes len args s) :
    WP isa twoTest s fun u => Step Ex base bytes len args s u ∧
      Gate u (¬ sv s.mem base len .wide 10 = 2) ∧ Kept base len [17] [] s.mem u.mem := by
  unfold twoTest
  refine WP.seq (WP.mono (setW_ok h (a := 17) (v := 2) (by decide) (by decide)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  obtain k₁ := kept_slot h (a := 17) O₁
  refine WP.seq (WP.mono (eqW_ok S₁.inp (a := 10) (b := 17) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [V₁, k₁.slot_eq] at e₂
  obtain S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs S₁.inp m₂ K₂
  refine WP.mono (testMask_ok e₂) fun u ⟨z, m, K⟩ => ?_
  obtain S₃ : Step Ex base bytes len args u₂ u := Step.regs S₂.inp m K
  refine ⟨(S₁.trans S₂).trans S₃, Gate.of_eval z ?_, by rw [m, m₂]; exact k₁⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]

end

end VG.Proof.Ffdh.X86.Ladder
