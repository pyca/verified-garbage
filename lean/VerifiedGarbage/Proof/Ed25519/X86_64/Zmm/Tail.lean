import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Consts

/-!
# The `zmm` comb: `32 A + B`

After the steps, `A` is doubled five times as the lanes of `ymm0–ymm4`
(`vdbl5`); `B`'s cached point `(Y - X, Y + X, 2dT, 2Z)` is its
`(Y - X, Y + X, T, Z)` (`vaddA`) times the lanes `(1, 1, 2d, 2)` of slots
12–15 (split as an entry, `esplit`), and is added to `32 A` (`vadd`).
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld st mov carry mul4 OPL KM)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vadd vaddA vstA vstore vdbl5)
open Edwards
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr fe5_carry fe5_mul mq vm vm_gpr vm_rd vm_wr Ctx carryI_wp
  carryF_wp slotv envOf envOf_v limbNat Sym symOf symOf_eq run_ok CConsts)
open VG.Proof.X25519.X86_64 (off ofs Outside F)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-- The cached point of `(X, Y, Z, T)`, as `vcache` computes it: `(Y - X, Y + X, T (d + d), Z 2)`. -/
def cacheOf (P : Spec.Ed25519.Point) : Spec.Ed25519.Point :=
  ⟨(P.Y - P.X) * 1, (P.Y + P.X) * 1, P.T * (Spec.Ed25519.d + Spec.Ed25519.d), P.Z * 2⟩

theorem cacheOf_eq (P : Spec.Ed25519.Point) : cacheOf P = cache P := by
  simp only [cacheOf, cache, Spec.Ed25519.Point.mk.injEq]
  refine ⟨mul_one _, mul_one _, by grind, trivial⟩

theorem xr_ne' : ∀ a < 16, ∀ b < 16, a ≠ b → xr a ≠ xr b := by decide

theorem limbNat_congr' {w w' : Nat → Nat} {m : Nat} (h : ∀ k < 4, w k = w' k) (i : Nat) :
    limbNat w m i = limbNat w' m i := by
  rcases i with _ | _ | _ | _ | _ | _ <;>
    simp only [limbNat, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- A field element's four words, split into limbs. -/
theorem fe5_words' (m : Mem) (base : Addr) (d : Nat) :
    fe5 (limbNat (fun k => (mq m base (d + 8 * k)).toNat) (2 ^ 51 - 1)) = F m base d := by
  show VG.Proof.X25519.toFe _ = VG.Proof.X25519.toFe _
  rw [VG.Proof.X25519.X86_64.Ifma.limbNat_lv _ (fun k _ => BitVec.isLt _)]
  rfl

/-- The rows of slots 12–15 into `ymm11–ymm14`. -/
def vrowsK : List Instr := [ld 11 (offset 12), ld 12 (offset 13), ld 13 (offset 14), ld 14 (offset 15)]

def vrowsKS : Sym := symOf vrowsK

theorem vrowsKS_regs : ∀ l < 4, vrowsKS.reg (11 + l) = .ld (64 + 32 * (12 + l)) := by decide +kernel
theorem vrowsKS_keep : ∀ r < 11, vrowsKS.reg r = .reg r := by decide +kernel
theorem vrowsKS_st : vrowsKS.st = [] := by decide +kernel

/-- The product's limbs to `ymm5–ymm9`. -/
def vmovs : List Instr := (List.range 5).map fun j => mov (5 + j) j

def vmovsS : Sym := symOf vmovs

theorem vmovsS_regs : ∀ j < 5, vmovsS.reg (5 + j) = .reg j := by decide +kernel
theorem vmovsS_st : vmovsS.st = [] := by decide +kernel

/-- `B`'s cached point from its lanes: `(Y - X, Y + X, T, Z)` (`vaddA`), carried, to `OPL`
(`vstA`), times the factors of slots 12–15 (`vrowsK`, `esplit`, `mul4 OPL`), to `ymm5–ymm9`,
carried. -/
theorem vcache_wp {s : State} {b : Addr} (hs : Scratch s b) (hk : EConsts s.mem b) (hx : Small s)
    (h12 : F s.mem b (offset 12) = 1) (h13 : F s.mem b (offset 13) = 1)
    (h14 : F s.mem b (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d) (h15 : F s.mem b (offset 15) = 2) :
    WP isa (.block (vaddA ++ carry id ++ vstA ++ vrowsK ++ esplit ++ mul4 OPL ++ vmovs ++ carry (5 + ·))) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Outside b 1024 320 s.mem t.mem ∧
        (∀ l < 4, ∀ i < 5, lanes t 5 l i < 2 ^ 52) ∧ lanePt5 t = cache (lanePt s) := by
  have hcc : CConsts s.mem b := hk.toCConsts
  simp only [List.append_assoc]
  -- `(Y - X, Y + X, T, Z)`
  rw [WP.block_append_iff]
  refine WP.mono (vaddA_wp hs.rdi (ctx_of hs) hcc hx) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ : Scratch s₁ b := ⟨by rw [vm_gpr v₁]; exact hs.rdi, by rw [vm_wr v₁]; exact hs.wr, hs.nowrap⟩
  -- carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (ctx_of hs₁) (by rw [m₁]; exact hcc) fun l hl i hi => (u₁ l hl i hi).2)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ : Scratch s₂ b := ⟨by rw [vm_gpr v₂]; exact hs₁.rdi, by rw [vm_wr v₂]; exact hs₁.wr, hs.nowrap⟩
  have p₂ : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (aOp (lanes s 0) l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1),
      fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega),
      fe5_congr (fun i hi => (u₁ l hl i hi).1)]
  -- to `OPL`
  rw [WP.block_append_iff]
  refine WP.mono (vstA_wp hs₂.rdi (ctx_of hs₂)) fun s₃ ⟨v₃, o₃, u₃, _⟩ => ?_
  have hs₃ : Scratch s₃ b := ⟨by rw [vm_gpr v₃]; exact hs₂.rdi, by rw [vm_wr v₃]; exact hs₂.wr, hs.nowrap⟩
  have mo₃ : Outside b 1024 320 s.mem s₃.mem := by
    rw [m₂, m₁] at o₃; exact o₃.mono (by decide) (by decide)
  have hk₃ : EConsts s₃.mem b := hk.outside mo₃
  -- the factors' rows
  rw [WP.block_append_iff]
  have e₄ : Sym.init.run vrowsK = some vrowsKS := symOf_eq _ _
  refine WP.mono (run_ok (ctx_of hs₃) e₄) fun s₄ h₄ => ?_
  have m₄ : s₄.mem = s₃.mem := by rw [h₄.mem, vrowsKS_st]; rfl
  have hs₄ : Scratch s₄ b := ⟨by rw [h₄.gpr]; exact hs₃.rdi, by rw [h₄.wr]; exact hs₃.wr, hs.nowrap⟩
  have r₄ : ∀ l < 4, ∀ k < 4, qw s₄ (xr (11 + l)) k = mq s₃.mem b (64 + 32 * (12 + l) + 8 * k) :=
    fun l hl k hk => by
      rw [h₄.reg _ k hk, VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), vrowsKS_regs l hl]
      simp only [VG.Proof.X25519.X86_64.Ifma.T.eval, hs₃.rdi, mq]
  -- split
  rw [WP.block_append_iff]
  refine WP.mono (esplit_wp hs₄.rdi (ctx_of hs₄) (by rw [m₄]; exact hk₃.toCConsts))
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  have hs₅ : Scratch s₅ b := ⟨by rw [vm_gpr v₅]; exact hs₄.rdi, by rw [vm_wr v₅]; exact hs₄.wr, hs.nowrap⟩
  have f₅ : ∀ l < 4, fe5 (lanes s₅ 5 l) = F s.mem b (64 + 32 * (12 + l)) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₅ l hl i hi).1), ← Outside_F mo₃ (by omega) (Or.inl (by omega)),
      ← fe5_words' s₃.mem b (64 + 32 * (12 + l))]
    exact fe5_congr fun i _ => limbNat_congr' (fun k hk => by
      simp only [srow, envOf_v]; rw [r₄ l hl k hk]) i
  -- the product
  rw [WP.block_append_iff]
  have sl₅ : ∀ l < 4, ∀ i < 5, slotv s₅.mem b OPL l i = lanes s₂ 0 l i := fun l hl i hi => by
    rw [m₅, m₄]; exact u₃ l hl i hi
  refine WP.mono (mulLB_wp hs₅.rdi (ctx_of hs₅) (fun l hl i hi => by rw [sl₅ l hl i hi]; exact (u₂ l hl i hi).2)
    (fun l hl i hi => (u₅ l hl i hi).2)) fun s₆ ⟨⟨v₆, m₆, u₆, _⟩, b₆⟩ => ?_
  have hs₆ : Scratch s₆ b := ⟨by rw [vm_gpr v₆]; exact hs₅.rdi, by rw [vm_wr v₆]; exact hs₅.wr, hs.nowrap⟩
  have p₆ : ∀ l < 4, fe5 (lanes s₆ 0 l) = fe5 (aOp (lanes s 0) l) * F s.mem b (64 + 32 * (12 + l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₆ l hl i hi).1),
        fe5_mul (fun i hi => by rw [sl₅ l hl i hi]; exact (u₂ l hl i hi).2) (fun i hi => (u₅ l hl i hi).2),
        fe5_congr (fun i hi => sl₅ l hl i hi), p₂ l hl, f₅ l hl]
  -- to `ymm5–ymm9`
  rw [WP.block_append_iff]
  have e₇ : Sym.init.run vmovs = some vmovsS := symOf_eq _ _
  refine WP.mono (run_ok (ctx_of hs₆) e₇) fun s₇ h₇ => ?_
  have hs₇ : Scratch s₇ b := ⟨by rw [h₇.gpr]; exact hs₆.rdi, by rw [h₇.wr]; exact hs₆.wr, hs.nowrap⟩
  have l₇ : ∀ l < 4, ∀ i < 5, lanes s₇ 5 l i = lanes s₆ 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [h₇.reg _ l hl, VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), vmovsS_regs i hi]; rfl
  have m₇ : s₇.mem = s₆.mem := by rw [h₇.mem, vmovsS_st]; rfl
  -- carried
  refine WP.mono (carryF_wp hs₇.rdi (ctx_of hs₇) (by rw [m₇, m₆, m₅, m₄]; exact hk₃.toCConsts)
    fun l hl i hi => by rw [l₇ l hl i hi]; have := b₆ l hl i hi; have : prodBound < 2 ^ 63 := by decide
                        omega) fun t ⟨v₈, m₈, u₈, _⟩ => ?_
  refine ⟨by rw [vm_gpr v₈, h₇.gpr, vm_gpr v₆, vm_gpr v₅, h₄.gpr, vm_gpr v₃, vm_gpr v₂, vm_gpr v₁],
    by rw [vm_rd v₈, h₇.rd, vm_rd v₆, vm_rd v₅, h₄.rd, vm_rd v₃, vm_rd v₂, vm_rd v₁],
    by rw [vm_wr v₈, h₇.wr, vm_wr v₆, vm_wr v₅, h₄.wr, vm_wr v₃, vm_wr v₂, vm_wr v₁],
    by rw [m₈, m₇, m₆, m₅, m₄]; exact mo₃, fun l hl i hi => (u₈ l hl i hi).2, ?_⟩
  have f₈ : ∀ l < 4, fe5 (lanes t 5 l) = fe5 (aOp (lanes s 0) l) * F s.mem b (64 + 32 * (12 + l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₈ l hl i hi).1),
        fe5_carry _ (by rw [l₇ l hl 4 (by decide)]; have := b₆ l hl 4 (by decide)
                        have : prodBound < 2 ^ 63 := by decide
                        omega),
        fe5_congr (fun i hi => l₇ l hl i hi), p₆ l hl]
  obtain ⟨a0, a1, a2, a3⟩ := aOp_fe (lanes s 0) hx
  rw [← cacheOf_eq]
  simp only [lanePt5, cacheOf, lanePt]
  rw [f₈ 0 (by decide), f₈ 1 (by decide), f₈ 2 (by decide), f₈ 3 (by decide), a0, a1, a2, a3]
  rw [show F s.mem b 448 = 1 from h12, show F s.mem b 480 = 1 from h13,
    show F s.mem b 512 = _ from h14, show F s.mem b 544 = 2 from h15]

/-! ## The accumulators' rows -/

/-- Quadword `k` of half `h` of a `zmm` register. -/
theorem zmm_qword (s : State) (r : XReg) {h k : Nat} (hh : h < 2) (hk : k < 4) :
    (s.zmm r).extractLsb' (8 * (32 * h + 8 * k)) (8 * 8) = zq s r h k := by
  rw [zq, ← zmm_lane s r (i := 2 * h + k / 2) (by omega), qword, extract_extract _ _ _ _ _ (by omega)]
  congr 1; omega

/-- Quadword `k` of a `ymm` register. -/
theorem ymm_qword (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (s.ymm r).extractLsb' (8 * (8 * k)) (8 * 8) = qw s r k := by
  rw [← VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm s r hk, qword256]
  congr 1; omega

theorem readW_zmm (m : Mem) (a : Addr) (s : State) (r : XReg) {h k : Nat} (hh : h < 2) (hk : k < 4) :
    (m.writeW a (s.zmm r)).readW (a + BitVec.ofNat 64 (32 * h + 8 * k)) 64 = zq s r h k := by
  have e := readW_writeW_inside m a (s.zmm r) (k := 32 * h + 8 * k) (n := 8) (by omega) (by decide)
  rw [zmm_qword s r hh hk] at e
  exact e

theorem readW_ymm (m : Mem) (a : Addr) (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.ymm r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = qw s r k := by
  have e := readW_writeW_inside m a (s.ymm r) (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [ymm_qword s r hk] at e
  exact e

theorem zst_ok {z : State} {b : Addr} (hs : Scratch z b) {d : Nat} (hd : d + 64 ≤ 8192) (r : Nat) :
    WP isa (.block [.vmovdqu32Store (sc d) (y r)]) z fun t =>
      t = z.setMem (z.mem.writeW (b + BitVec.ofNat 64 d) (z.zmm (y r))) := by
  have hw : InRegions z.wr (b + BitVec.ofNat 64 d) 64 := ⟨_, hs.wr, Offset.contains_base b hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc' hs.rdi, State.store512_eq, hw, ite_true,
    Option.some.injEq, exists_eq_left']

theorem yst_ok {s : State} {b : Addr} (hs : Scratch s b) {d : Nat} (hd : d + 32 ≤ 8192) (r : Nat) :
    WP isa (.block [st d r]) s fun t => t = s.setMem (s.mem.writeW (b + BitVec.ofNat 64 d) (s.ymm (y r))) := by
  have hw : InRegions s.wr (b + BitVec.ofNat 64 d) 32 := ⟨_, hs.wr, Offset.contains_base b hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, st, ea_sc' hs.rdi, State.store256_eq, hw,
    ite_true, Option.some.injEq, exists_eq_left']

theorem yld_ok {s : State} {b : Addr} (hs : Scratch s b) {d : Nat} (hd : d + 32 ≤ 8192) {r : Nat} (hr : r < 16) :
    WP isa (.block [ld r d]) s fun t => (∀ k < 4, qw t (xr r) k = mq s.mem b (d + 8 * k)) ∧
      (∀ x, x ≠ xr r → ∀ k < 4, qw t x k = qw s x k) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  have hin : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) 32 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base b hd (by omega)⟩
  have hy : y r = xr r := y_xr r hr
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ld, ea_sc' hs.rdi, State.load256, hin, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, fun x hx k hk => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, hy, ite_eq_left_iff.mpr (fun h => absurd rfl h), mq,
      Offset.add_ofNat_add_ofNat]
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, hy]; exact ite_eq_right_iff.mpr fun h => absurd h hx

/-- The halves of `zmm0–zmm4` to the rows at `ZACC`. -/
theorem zstores_ok {b : Addr} : ∀ n ≤ 5, ∀ z : State, Scratch z b →
    WP isa (.block ((List.range n).map fun j => .vmovdqu32Store (sc (ZACC + 64 * j)) (y j))) z fun t =>
      (∀ j < n, ∀ h < 2, ∀ k < 4, mq t.mem b (ZACC + 64 * j + (32 * h + 8 * k)) = zq z (y j) h k) ∧
      Outside b ZACC (64 * n) z.mem t.mem ∧ t = z.setMem t.mem
  | 0, _, z, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, by cases z; rfl⟩
  | n + 1, hn, z, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstores_ok n (by omega) z hs) fun t₁ ⟨c₁, o₁, e₁⟩ => ?_
    have hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (zst_ok hs₁ (d := ZACC + 64 * n) (by unfold ZACC; omega) n) fun t et => ?_
    have ez : t₁.zmm (y n) = z.zmm (y n) := by rw [e₁]; rfl
    refine ⟨fun j hj h hh k hk => ?_, fun a ha => ?_, ?_⟩
    · rw [et]
      by_cases hjn : j = n
      · subst hjn
        rw [State.setMem_mem, mq, ez, ← Offset.add_ofNat_add_ofNat b (ZACC + 64 * j) (32 * h + 8 * k)]
        exact readW_zmm _ _ z _ hh hk
      · rw [State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + (32 * h + 8 * k)) (n := 8)
          (by unfold ZACC; omega) (by unfold ZACC; omega) (Or.inl (by unfold ZACC; omega))]
        exact c₁ j (by omega) h hh k hk
    · rw [et, State.setMem_mem, writeW_byte_off _ _ _ _ ?_, o₁ a (by omega)]
      simp only [ofs] at ha
      rw [sub_off]; have := (a - b).isLt; unfold ZACC at *; omega
    · rw [et, e₁]; rfl

/-- `ymm0–ymm4` to the low halves of the rows at `ZACC`. -/
theorem ystores_ok {b : Addr} : ∀ n ≤ 5, ∀ s : State, Scratch s b →
    WP isa (.block ((List.range n).map fun j => st (ZACC + 64 * j) j)) s fun t =>
      (∀ j < n, ∀ k < 4, mq t.mem b (ZACC + 64 * j + 8 * k) = qw s (xr j) k) ∧
      (∀ j < 5, ∀ k < 4, mq t.mem b (ZACC + 64 * j + 32 + 8 * k) = mq s.mem b (ZACC + 64 * j + 32 + 8 * k)) ∧
      Outside b ZACC 320 s.mem t.mem ∧ t = s.setMem t.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl,
      Outside.refl _ _ _ _, by cases s; rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ystores_ok n (by omega) s hs) fun t₁ ⟨c₁, u₁, o₁, e₁⟩ => ?_
    have hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (yst_ok hs₁ (d := ZACC + 64 * n) (by unfold ZACC; omega) n) fun t et => ?_
    have ey : t₁.ymm (y n) = s.ymm (y n) := by rw [e₁]; rfl
    refine ⟨fun j hj k hk => ?_, fun j hj k hk => ?_, fun a ha => ?_, ?_⟩
    · rw [et]
      by_cases hjn : j = n
      · subst hjn
        rw [State.setMem_mem, mq, ey, ← Offset.add_ofNat_add_ofNat b (ZACC + 64 * j) (8 * k),
          readW_ymm _ _ s _ hk, y_xr j (by omega)]
      · rw [State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + 8 * k) (n := 8)
          (by unfold ZACC; omega) (by unfold ZACC; omega) (by unfold ZACC; omega)]
        exact c₁ j (by omega) k hk
    · rw [et, State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + 32 + 8 * k) (n := 8)
        (by unfold ZACC; omega) (by unfold ZACC; omega) (by unfold ZACC; omega)]
      exact u₁ j hj k hk
    · rw [et, State.setMem_mem, writeW_byte_off _ _ _ _ ?_, o₁ a ha]
      simp only [ofs] at ha
      rw [sub_off]; have := (a - b).isLt; unfold ZACC at *; omega
    · rw [et, e₁]; rfl

/-- The rows at `f j` into `ymm0–ymm4`. -/
theorem yloads_ok {b : Addr} {f : Nat → Nat} (hf : ∀ j < 5, f j + 32 ≤ 8192) :
    ∀ n ≤ 5, ∀ s : State, Scratch s b →
    WP isa (.block ((List.range n).map fun j => ld j (f j))) s fun t =>
      (∀ j < n, ∀ k < 4, qw t (xr j) k = mq s.mem b (f j + 8 * k)) ∧
      (∀ r < 16, n ≤ r → ∀ k < 4, qw t (xr r) k = qw s (xr r) k) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      rfl, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (yloads_ok hf n (by omega) s hs) fun t₁ ⟨c₁, k₁, g₁, m₁, rd₁, wr₁, sy₁⟩ => ?_
    have hs₁ : Scratch t₁ b := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (yld_ok hs₁ (hf n (by omega)) (r := n) (by omega))
      fun t ⟨c, k, g, m, rd, wr, sy⟩ => ⟨fun j hj q hq => ?_, fun r hr hnr q hq => ?_, g.trans g₁, m.trans m₁,
        rd.trans rd₁, wr.trans wr₁, sy.trans sy₁⟩
    · by_cases hjn : j = n
      · subst hjn; rw [c q hq, m₁]
      · rw [k _ (xr_ne' j (by omega) n (by omega) hjn) q hq, c₁ j (by omega) q hq]
    · rw [k _ (xr_ne' r hr n (by omega) (by omega)) q hq, k₁ r hr (by omega) q hq]

/-! ## `32 A + B` -/

theorem qw_half0 (b : Addr) (w : State) (r : XReg) {k : Nat} (hk : k < 4) : qw (Zmm.half b 0 w) r k = qw w r k := by
  rw [qw_half b w r hk]
  simp only [zq, qw, State.zlane, Nat.mul_zero, Nat.zero_add, show k / 2 < 2 by omega, ite_true]

theorem lanes_eq_of {s t : State} {r : Nat} (h : ∀ i < 5, ∀ l < 4, qw t (xr (r + i)) l = qw s (xr (r + i)) l) :
    ∀ l < 4, ∀ i < 5, lanes t r l i = lanes s r l i := fun l hl i hi => by
  simp only [lanes]; rw [h i hi l hl]

theorem lanePt_eq_of {s t : State} (h : ∀ l < 4, ∀ i < 5, lanes t 0 l i = lanes s 0 l i) : lanePt t = lanePt s := by
  simp only [lanePt]
  rw [fe5_congr (h 0 (by decide)), fe5_congr (h 1 (by decide)), fe5_congr (h 2 (by decide)),
    fe5_congr (h 3 (by decide))]

theorem lanePt5_eq_of {s t : State} (h : ∀ l < 4, ∀ i < 5, lanes t 5 l i = lanes s 5 l i) :
    lanePt5 t = lanePt5 s := by
  simp only [lanePt5]
  rw [fe5_congr (h 0 (by decide)), fe5_congr (h 1 (by decide)), fe5_congr (h 2 (by decide)),
    fe5_congr (h 3 (by decide))]

theorem _root_.VG.Proof.Ed25519.X86_64.Ifma.EConsts.zacc {m m' : Mem} {b : Addr} (hk : EConsts m b) (h : Outside b ZACC 320 m m') : EConsts m' b :=
  hk.of_mq fun d _ h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact h.word (Or.inl (by unfold ZACC; omega)) (by omega)

theorem outside_mq {m m' : Mem} {b : Addr} {o n : Nat} (h : Outside b o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : mq m' b d = mq m b d :=
  h.word hd hd'

theorem ztail2_split : ztail2 ++ vstore = (List.range 5).map (fun j => st (ZACC + 64 * j) j) ++
    ((List.range 5).map (fun j => ld j (ZACC + 64 * j + 32)) ++
    ((vaddA ++ carry id ++ vstA ++ vrowsK ++ esplit ++ mul4 OPL ++ vmovs ++ carry (5 + ·)) ++
    ((List.range 5).map (fun j => ld j (ZACC + 64 * j)) ++ (vadd ++ vstore)))) := by
  simp only [ztail2, vrowsK, vmovs, List.append_assoc, List.cons_append, List.nil_append]

/-- After the steps, with `A` in half 0 and `B` in half 1 of the lanes: `32 A + B` in slots 0–3. -/
theorem ztail_ok {w : State} {b : Addr} (hs : Scratch w b) (hk : EConsts w.mem b)
    (hA : Small (Zmm.half b 0 w)) (hB : Small (Zmm.half b 1 w)) {a c : EPoint dZ}
    (ha : Rep (lanePt (Zmm.half b 0 w)) a) (hc : Rep (lanePt (Zmm.half b 1 w)) c)
    (h12 : F w.mem b (offset 12) = 1) (h13 : F w.mem b (offset 13) = 1)
    (h14 : F w.mem b (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d) (h15 : F w.mem b (offset 15) = 2) :
    WP isa (.seq (.block ztail1) (.seq vdbl5 (.block (ztail2 ++ vstore)))) w fun t =>
      (∀ r, r ≠ .rsi → t.gpr r = w.gpr r) ∧ t.rd = w.rd ∧ t.wr = w.wr ∧
      Outside b 64 (ZACC + 320 - 64) w.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3) ((32 : Nat) • a + c) := by
  -- the halves to `ZACC`
  refine WP.seq (WP.mono (zstores_ok 5 (by decide) w hs) fun t₁ ⟨c₁, o₁, e₁⟩ => ?_)
  have hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
  have q₁ : ∀ r k, k < 4 → qw t₁ r k = qw w r k := fun r k hk => by rw [e₁]; rfl
  have hk₁ : EConsts t₁.mem b := hk.zacc o₁
  have l₁ : ∀ l < 4, ∀ i < 5, lanes t₁ 0 l i = lanes (Zmm.half b 0 w) 0 l i := fun l hl i hi => by
    simp only [lanes]; rw [q₁ _ _ hl, qw_half0 b w _ hl]
  -- `32 A`
  refine WP.seq (WP.mono (vdbl5_ok hs₁ hk₁ (fun l hl i hi => by rw [l₁ l hl i hi]; exact hA l hl i hi)
    (a := a) (by rw [lanePt_eq_of l₁]; exact ha)) fun t₂ ⟨g₂, rd₂, wr₂, o₂, sm₂, p₂⟩ => ?_)
  have hs₂ : Scratch t₂ b := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs.nowrap⟩
  have hk₂ : EConsts t₂.mem b := hk₁.outside o₂
  rw [ztail2_split, WP.block_append_iff]
  -- `32 A` to `ZACC`
  refine WP.mono (ystores_ok 5 (by decide) t₂ hs₂) fun t₃ ⟨c₃, u₃, o₃, e₃⟩ => ?_
  have hs₃ : Scratch t₃ b := ⟨by rw [e₃]; exact hs₂.rdi, by rw [e₃]; exact hs₂.wr, hs.nowrap⟩
  have hk₃ : EConsts t₃.mem b := hk₂.zacc o₃
  -- `B`
  rw [WP.block_append_iff]
  refine WP.mono (yloads_ok (f := fun j => ZACC + 64 * j + 32) (fun j hj => by unfold ZACC; omega) 5 (by decide)
    t₃ hs₃) fun t₄ ⟨c₄, k₄, g₄, m₄, rd₄, wr₄, _⟩ => ?_
  have hs₄ : Scratch t₄ b := ⟨by rw [g₄]; exact hs₃.rdi, by rw [wr₄]; exact hs₃.wr, hs.nowrap⟩
  have l₄ : ∀ l < 4, ∀ i < 5, lanes t₄ 0 l i = lanes (Zmm.half b 1 w) 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [c₄ i hi l hl, u₃ i hi l hl, outside_mq o₂ (Or.inr (by unfold ZACC; omega)) (by unfold ZACC; omega),
      qw_half b w _ hl, ← y_xr i (by omega), ← c₁ i hi 1 (by decide) l hl, Nat.add_assoc]
  have F₄ : ∀ d, d + 32 ≤ 1024 → F t₄.mem b d = F w.mem b d := fun d hd => by
    rw [m₄, Outside_F o₃ (by omega) (Or.inl (by unfold ZACC; omega)), Outside_F o₂ (by omega) (Or.inl hd),
      Outside_F o₁ (by omega) (Or.inl (by unfold ZACC; omega))]
  -- `B`'s cached point
  rw [WP.block_append_iff]
  refine WP.mono (vcache_wp hs₄ (by rw [m₄]; exact hk₃)
    (fun l hl i hi => by rw [l₄ l hl i hi]; exact hB l hl i hi)
    (by rw [F₄ _ (by decide)]; exact h12) (by rw [F₄ _ (by decide)]; exact h13)
    (by rw [F₄ _ (by decide)]; exact h14) (by rw [F₄ _ (by decide)]; exact h15))
    fun t₅ ⟨g₅, rd₅, wr₅, o₅, b₅, p₅⟩ => ?_
  have hs₅ : Scratch t₅ b := ⟨by rw [g₅]; exact hs₄.rdi, by rw [wr₅]; exact hs₄.wr, hs.nowrap⟩
  -- `32 A` back
  rw [WP.block_append_iff]
  refine WP.mono (yloads_ok (f := fun j => ZACC + 64 * j) (fun j hj => by unfold ZACC; omega) 5 (by decide)
    t₅ hs₅) fun t₆ ⟨c₆, k₆, g₆, m₆, rd₆, wr₆, _⟩ => ?_
  have hs₆ : Scratch t₆ b := ⟨by rw [g₆]; exact hs₅.rdi, by rw [wr₆]; exact hs₅.wr, hs.nowrap⟩
  have l₆ : ∀ l < 4, ∀ i < 5, lanes t₆ 0 l i = lanes t₂ 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [c₆ i hi l hl, outside_mq o₅ (Or.inr (by unfold ZACC; omega)) (by unfold ZACC; omega), m₄, c₃ i hi l hl]
  have l₆' : ∀ l < 4, ∀ i < 5, lanes t₆ 5 l i = lanes t₅ 5 l i :=
    lanes_eq_of fun i hi l hl => k₆ (5 + i) (by omega) (by omega) l hl
  have hk₆ : EConsts t₆.mem b := by rw [m₆]; exact (hk₃.outside (by rw [← m₄]; exact o₅))
  -- the sum
  rw [WP.block_append_iff]
  refine WP.mono (vadd_wp hs₆.rdi (ctx_of hs₆) hk₆ (fun l hl i hi => by rw [l₆ l hl i hi]; exact sm₂ l hl i hi)
    (fun l hl i hi => by rw [l₆' l hl i hi]; exact b₅ l hl i hi)) fun t₇ ⟨g₇, rd₇, wr₇, o₇, sm₇, p₇⟩ => ?_
  have hs₇ : Scratch t₇ b := ⟨by rw [g₇]; exact hs₆.rdi, by rw [wr₇]; exact hs₆.wr, hs.nowrap⟩
  have pt₇ : Rep (lanePt t₇) ((32 : Nat) • a + c) := by
    rw [p₇, lanePt_eq_of l₆, lanePt5_eq_of l₆', p₅, lanePt_eq_of l₄, vAddPt_cache]
    exact pointAdd_rep p₂ hc
  -- to slots 0–3
  refine WP.mono (vstore_wp hs₇.rdi (ctx_of hs₇) (hk₆.outside o₇) sm₇) fun t ⟨g, rd, wr, o, f⟩ => ?_
  have eg₃ : t₃.gpr = t₂.gpr := by rw [e₃]; rfl
  have eg₁ : t₁.gpr = w.gpr := by rw [e₁]; rfl
  have er₃ : t₃.rd = t₂.rd := by rw [e₃]; rfl
  have er₁ : t₁.rd = w.rd := by rw [e₁]; rfl
  have ew₃ : t₃.wr = t₂.wr := by rw [e₃]; rfl
  have ew₁ : t₁.wr = w.wr := by rw [e₁]; rfl
  refine ⟨fun r hr => by rw [g, g₇, g₆, g₅, g₄, eg₃, g₂ r hr, eg₁],
    by rw [rd, rd₇, rd₆, rd₅, rd₄, er₃, rd₂, er₁], by rw [wr, wr₇, wr₆, wr₅, wr₄, ew₃, wr₂, ew₁], ?_, ?_⟩
  · intro x hx
    have hx' : ofs b x < 64 ∨ 6400 ≤ ofs b x := by unfold ZACC at hx; omega
    refine (o x (by omega_using [hx'])).trans ((o₇ x (by omega_using [hx'])).trans ?_)
    rw [m₆]
    refine (o₅ x (show ofs b x < 1024 ∨ 1024 + 320 ≤ ofs b x by omega_using [hx'])).trans ?_
    rw [m₄]
    exact (o₃ x (show ofs b x < 6080 ∨ 6080 + 320 ≤ ofs b x by omega_using [hx'])).trans
      ((o₂ x (by omega_using [hx'])).trans (o₁ x (show ofs b x < 6080 ∨ 6080 + 64 * 5 ≤ ofs b x by omega_using [hx'])))
  · have pt : point (env t.mem b) 0 1 2 3 = lanePt t₇ := by
      simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
      rw [← f 0 (by decide), ← f 1 (by decide), ← f 2 (by decide), ← f 3 (by decide)]
      rfl
    rw [pt]; exact pt₇

end VG.Proof.Ed25519.X86_64.Zmm
