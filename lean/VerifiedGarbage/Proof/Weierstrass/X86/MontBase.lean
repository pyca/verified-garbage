import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Mont.X86.Step

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the working space at `ebp`

The functions of `Impl/Weierstrass/X86/Mont.lean` address their working
space through `ebp`, which holds its base `base` (`Bx`), and the numbers
`[a]`, `[b]` and `[o]` through pointers, a register holding `ebp` plus an
offset (`Ptr`). The loads and stores at constant offsets of either
(`Bx.ea`, `Bx.ea_ptr`), as `Proof/Mont/X86/Words.lean` has them for `edi`,
and the multiply-accumulate steps of a row of the product (`stepG_ok`,
`step0G_ok`, `stepZ_ok`), whose multiplicand word comes from any source: a
pointer (`[esi + 4j]`) or an immediate (a word of the modulus).
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The working space: `ebp` holds its base `base`, it is writable and it
lies below `2³²`. -/
structure Bx (s : State) (base : Addr) (size : Nat) : Prop where
  ebp : (s.gpr .ebp).setWidth 64 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

/-- `r` points `p` bytes into the working space at `ebp`. -/
abbrev Ptr (s : State) (r : Reg) (p : Nat) : Prop := s.gpr r = s.gpr .ebp + BitVec.ofNat 32 p

variable {s : State} {base : Addr} {size : Nat}

theorem Bx.ebp_toNat (hb : Bx s base size) : (s.gpr .ebp).toNat = base.toNat := by
  rw [← hb.ebp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .ebp).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- `[ebp + d]`. -/
theorem Bx.ea (hb : Bx s base size) {d : Nat} (hd : d < size) : s.ea (bp d) = off base d := by
  change addr (s.gpr .ebp) d = _
  rw [addr_eq (by have := hb.nowrap; have := hb.ebp_toNat; omega), hb.ebp]

/-- `[r + d]`, for `r` pointing `p` bytes into the working space. -/
theorem Bx.ea_ptr (hb : Bx s base size) {r : Reg} {p d : Nat} (hp : Ptr s r p) (hd : p + d < size) :
    s.ea (at_ r d) = off base (p + d) := by
  change ((s.gpr r + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hb.ea hd

theorem Bx.read (hb : Bx s base size) {d n : Nat} (hd : d + n ≤ size) :
    InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hb.wr, Scr.contains hb.nowrap hd⟩

theorem Bx.write (hb : Bx s base size) {d n : Nat} (hd : d + n ≤ size) : InRegions s.wr (off base d) n :=
  ⟨_, hb.wr, Scr.contains hb.nowrap hd⟩

theorem Bx.of_keeps {rs : List Reg} {s' : State} (hb : Bx s base size) (h : Keeps rs s s')
    (hr : .ebp ∉ rs) : Bx s' base size :=
  ⟨by rw [h.1 _ hr]; exact hb.ebp, h.2.2 ▸ hb.wr, hb.nowrap⟩

theorem Ptr.of_keeps {rs : List Reg} {s' : State} {r : Reg} {p : Nat} (hp : Ptr s r p) (h : Keeps rs s s')
    (hr : r ∉ rs) (he : .ebp ∉ rs) : Ptr s' r p := by
  change s'.gpr r = s'.gpr .ebp + _
  rw [h.1 _ hr, h.1 _ he]; exact hp

/-- A load of the working space through `ebp`. -/
theorem readSrc_bp (hb : Bx s base size) {d : Nat} (hd : d + 4 ≤ size) :
    readSrc s (.mem (bp d)) = some (s.mem.readW (off base d) 32) := by
  show s.load32 (s.ea (bp d)) = _
  rw [hb.ea (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (hb.read hd) h]

/-- A load of the working space through a pointer. -/
theorem readSrc_ptr (hb : Bx s base size) {r : Reg} {p d : Nat} (hp : Ptr s r p) (hd : p + d + 4 ≤ size) :
    readSrc s (.mem (at_ r d)) = some (s.mem.readW (off base (p + d)) 32) := by
  show s.load32 (s.ea (at_ r d)) = _
  rw [hb.ea_ptr hp (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (hb.read (by omega)) h]

/-! ## Steps of a row -/

/-- `[ebp + acc + 4j] += ecx · y + ebx`, the carry word to `ebx`. -/
theorem stepG_ok (hb : Bx s base size) {ys : Src} {y : BitVec 32} (hy : readSrc s ys = some y) {acc j : Nat}
    (ht : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (stepG ys acc j)) s fun u =>
      u.mem = s.mem.writeW (off base (acc + 4 * j)) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * y.toNat + (s.gpr .ebx).toNat + w32 s.mem base (acc + 4 * j))) ∧
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * y.toNat + (s.gpr .ebx).toNat +
          w32 s.mem base (acc + 4 * j)) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] s u := by
  simp only [stepG]
  refine wp_movS hy fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have k₄ : Keeps [.eax, .edx] s s₄ :=
    ((u₁.keeps.mono (by decide)).widen m₂.keeps).widen u₃.keeps |>.widen u₄.keeps
  have hb₄ := hb.of_keeps k₄ (by decide)
  refine wp_addS (readSrc_bp hb₄ ht) fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have k₆ : Keeps [.eax, .edx] s s₆ := (k₄.widen u₅.keeps).widen u₆.keeps
  have hb₆ := hb.of_keeps k₆ (by decide)
  refine wp_storeS (hb₆.ea (d := acc + 4 * j) (by omega)) (hb₆.write ht) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, m₄]
  have ecx₂ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₂] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .ebx := u₃.gpr
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s.mem.readW (off base (acc + 4 * j)) 32 := by
    rw [u₅.gpr, m₄]
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs y (s.gpr .ecx) (s.gpr .ebx) (s.mem.readW (off base (acc + 4 * j)) 32) _ _ rfl rfl
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 (y.toNat * (s.gpr .ecx).toNat) +
      s.gpr .ebx + s.mem.readW (off base (acc + 4 * j)) 32 := by
    rw [eax₆, eax₅, eax₄, eax₃, eax₂, ebx₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, eax₄, eax₃, eax₂, ebx₂, m₄] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * y.toNat +
      (s.gpr .ebx).toNat + w32 s.mem base (acc + 4 * j)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat]
  refine ⟨by rw [u₈.mem, m₇.mem, m₆, hx], by rw [u₈.gpr, m₇.gpr, dx₆, hpost.2], fun r hr => ?_,
    by rw [u₈.rd, m₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd],
    by rw [u₈.wr, m₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  rw [u₈.other _ h2, m₇.gpr, u₆.other _ h3, u₅.other _ h1, u₄.other _ h3, u₃.other _ h1, m₂.other _ h1 h3,
    u₁.other _ h1]

/-- The registers of a first step: `edx:eax = A C`, then `+ T` with the
carry into `edx`, are the low and high words of `C A + T`. -/
theorem step0_regs (A C T : BitVec 32) (c : Bool)
    (hc : c = decide (2 ^ 32 ≤ (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat + T.toNat)) :
    (BitVec.ofNat 32 (A.toNat * C.toNat) + T).toNat = (C.toNat * A.toNat + T.toNat) % 2 ^ 32 ∧
    (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32) + 0 + (BitVec.ofBool c).setWidth 32).toNat =
      (C.toNat * A.toNat + T.toNat) / 2 ^ 32 := by
  obtain ⟨hw, hq⟩ := mul_words A C
  have hT := T.isLt
  rw [Nat.mul_comm C.toNat]
  have he2 : (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat = A.toNat * C.toNat % 2 ^ 32 := BitVec.toNat_ofNat _ _
  have hd2 : (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32)).toNat = A.toNat * C.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  rw [h0, BitVec.toNat_add, BitVec.toNat_add, ofBool_toNat, he2, hd2]
  rw [he2] at hc
  subst hc
  generalize A.toNat * C.toNat = P at *
  by_cases h1 : 2 ^ 32 ≤ P % 2 ^ 32 + T.toNat <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    constructor <;> omega

/-- The first step of a row: `[ebp + acc] += ecx · y`, the carry word to `ebx`. -/
theorem step0G_ok (hb : Bx s base size) {ys : Src} {y : BitVec 32} (hy : readSrc s ys = some y) {acc : Nat}
    (ht : acc + 4 ≤ size) :
    WP isa (.block (step0G ys acc)) s fun u =>
      u.mem = s.mem.writeW (off base acc) (BitVec.ofNat 32 ((s.gpr .ecx).toNat * y.toNat + w32 s.mem base acc)) ∧
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * y.toNat + w32 s.mem base acc) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] s u := by
  simp only [step0G]
  refine wp_movS hy fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  have k₂ : Keeps [.eax, .edx] s s₂ := (u₁.keeps.mono (by decide)).widen m₂.keeps
  have hb₂ := hb.of_keeps k₂ (by decide)
  refine wp_addS (readSrc_bp hb₂ ht) fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have k₄ : Keeps [.eax, .edx] s s₄ := (k₂.widen u₃.keeps).widen u₄.keeps
  have hb₄ := hb.of_keeps k₄ (by decide)
  refine wp_storeS (hb₄.ea (d := acc) (by omega)) (hb₄.write ht) fun s₅ m₅ => ?_
  refine wp_movS rfl fun s₆ u₆ _ => WP.block_nil ?_
  have m₂' : s₂.mem = s.mem := by rw [m₂.mem, u₁.mem]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂']
  have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₁] at eax₂ edx₂
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s.mem.readW (off base acc) 32 := by rw [u₃.gpr, m₂']
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have hpost := step0_regs y (s.gpr .ecx) (s.mem.readW (off base acc) 32) _ rfl
  have hx : s₄.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * y.toNat + w32 s.mem base acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [eax₄, eax₃, eax₂, hpost.1, BitVec.toNat_ofNat]
  have dx₄ := edx₄
  rw [edx₃, edx₂, eax₂, m₂'] at dx₄
  refine ⟨by rw [u₆.mem, m₅.mem, m₄, hx], ?_, fun r hr => ?_,
    by rw [u₆.rd, m₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd], by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]⟩
  · rw [u₆.gpr, m₅.gpr, dx₄, hpost.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    rw [u₆.other _ h2, m₅.gpr, u₄.other _ h3, u₃.other _ h1, m₂.other _ h1 h3, u₁.other _ h1]

end VG.Proof.Weierstrass.X86.Mont
