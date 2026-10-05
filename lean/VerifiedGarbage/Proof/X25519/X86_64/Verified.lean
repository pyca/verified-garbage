import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Mem`. -/
section

/-!
# X25519 on x86-64: field elements in the working space

The working space is 4 KiB at `base`, which `rdi` holds (`Scr`); a field
element is the four words at an offset of it (`fe`), read as an element of
`GF(p)` by `F`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 4096⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 4096 ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (VG.Proof.X25519.X86_64.off base d) 64

/-- The field element at `base + o`: four little-endian words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat :=
  val4 (VG.Proof.X25519.X86_64.word m base o) (VG.Proof.X25519.X86_64.word m base (o + 8)) (VG.Proof.X25519.X86_64.word m base (o + 16)) (VG.Proof.X25519.X86_64.word m base (o + 24))

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = VG.Proof.X25519.X86_64.off (s.gpr .rdi) d := by
  simp only [State.ea, sc, at_, BitVec.ofInt_natCast]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 4096) :
    (⟨base, 4096⟩ : Region).Contains (VG.Proof.X25519.X86_64.off base d) n :=
  Offset.contains_base base h (by omega)

theorem load_sc {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    s.load64 (s.ea (sc d)) = some (VG.Proof.X25519.X86_64.word s.mem base d) := by
  rw [VG.Proof.X25519.X86_64.ea_sc, hs.rdi, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc hd⟩]

theorem readSrc_sc {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    VG.X86_64.readSrc s (.mem (sc d)) = some (VG.Proof.X25519.X86_64.word s.mem base d) := VG.Proof.X25519.X86_64.load_sc hs hd

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base)
    (h : Keeps rs s s') (hr : .rdi ∉ rs) : VG.Proof.X25519.X86_64.Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Stores and frames -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.X25519.X86_64.ofs base (VG.Proof.X25519.X86_64.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.X25519.X86_64.ofs, VG.Proof.X25519.X86_64.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X25519.X86_64.ofs base (VG.Proof.X25519.X86_64.off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X25519.X86_64.ofs base x < o ∨ o + n ≤ VG.Proof.X25519.X86_64.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.X25519.X86_64.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X25519.X86_64.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.X25519.X86_64.Outside base o n m₂ m₃) : VG.Proof.X25519.X86_64.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : VG.Proof.X25519.X86_64.word m' base d = VG.Proof.X25519.X86_64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base o n m m') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + n ≤ d) (hd' : d + 32 < 2 ^ 64) : VG.Proof.X25519.X86_64.fe m' base d = VG.Proof.X25519.X86_64.fe m base d := by
  simp only [X86_64.fe]
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega), h.word (by omega) (by omega),
    h.word (by omega) (by omega)]

/-- Four words stored at `base + o`. -/
def st4 (m : Mem) (base : Addr) (o : Nat) (w0 w1 w2 w3 : BitVec 64) : Mem :=
  (((m.writeW (VG.Proof.X25519.X86_64.off base o) w0).writeW (VG.Proof.X25519.X86_64.off base (o + 8)) w1).writeW (VG.Proof.X25519.X86_64.off base (o + 16)) w2).writeW
    (VG.Proof.X25519.X86_64.off base (o + 24)) w3

theorem sep_off (base : Addr) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : Mem.Sep (VG.Proof.X25519.X86_64.off base d) (64 / 8) (VG.Proof.X25519.X86_64.off base e) (64 / 8) :=
  Offset.sep base h hd he

theorem fe_st4 (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    VG.Proof.X25519.X86_64.fe (VG.Proof.X25519.X86_64.st4 m base o w0 w1 w2 w3) base o = val4 w0 w1 w2 w3 := by
  simp only [X86_64.fe, X86_64.word, VG.Proof.X25519.X86_64.st4]
  rw [Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64]

theorem write_outside (m : Mem) (base : Addr) {d o : Nat} (v : BitVec 64) (h1 : o ≤ d)
    (h2 : d + 8 ≤ o + 32) (h3 : o + 32 < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.X25519.X86_64.ofs base x < o ∨ o + 32 ≤ VG.Proof.X25519.X86_64.ofs base x) : (m.writeW (VG.Proof.X25519.X86_64.off base d) v) x = m x := by
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X25519.X86_64.ofs] at hx
  omega

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 < 2 ^ 64) :
    VG.Proof.X25519.X86_64.Outside base d 8 m (m.writeW (VG.Proof.X25519.X86_64.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X25519.X86_64.ofs] at hx
  omega

theorem st4_outside (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    VG.Proof.X25519.X86_64.Outside base o 32 m (VG.Proof.X25519.X86_64.st4 m base o w0 w1 w2 w3) := by
  intro x hx
  simp only [VG.Proof.X25519.X86_64.st4]
  rw [VG.Proof.X25519.X86_64.write_outside _ _ _ (by omega) (by omega) ho hx, VG.Proof.X25519.X86_64.write_outside _ _ _ (by omega) (by omega) ho hx,
    VG.Proof.X25519.X86_64.write_outside _ _ _ (by omega) (by omega) ho hx, VG.Proof.X25519.X86_64.write_outside _ _ _ (by omega) (by omega) ho hx]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Mul`. -/
section

/-!
# X25519 on x86-64: multiplication

A row of the product (`row`), for any five registers, from four
multiply-accumulate steps (`mulStep_ok`); the reduction of the eight-word
product (`reduce`); and the multiplication `mul o a b`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- A row of a product, into the registers `r0`–`r4`. -/
def rowR (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    (VG.Impl.X25519.X86_64.mulStep r0 .rbp .rcx (.mem (sc (b + 8 * 0))) ++ (VG.Impl.X25519.X86_64.mulStep r1 .rbp .rcx (.mem (sc (b + 8 * 1))) ++
      (VG.Impl.X25519.X86_64.mulStep r2 .rbp .rcx (.mem (sc (b + 8 * 2))) ++ (VG.Impl.X25519.X86_64.mulStep r3 .rbp .rcx (.mem (sc (b + 8 * 3))) ++
        [.mov r4 (.reg .rbp)]))))

theorem row_eq (a b i : Nat) :
    row a b i = VG.Proof.X25519.X86_64.rowR a b i (t i) (t (i + 1)) (t (i + 2)) (t (i + 3)) (t (i + 4)) := by
  simp only [row, VG.Proof.X25519.X86_64.rowR, List.append_assoc]
  rfl

/-- The start of a row: `rcx = a_i`, `rbp = 0`. -/
theorem rowStart_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    WP isa (.block [.mov .rcx (.mem (sc d)), .mov32 .rbp (.imm 0)]) s fun s' =>
      s'.gpr .rcx = VG.Proof.X25519.X86_64.word s.mem base d ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.readSrc_sc hs hd, VG.X86_64.readSrc32,
    Option.map_some, State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- A row: `r0 + 2⁶⁴ r1 + 2¹²⁸ r2 + 2¹⁹² r3 + a_i · b`, into `r0`–`r4`. -/
theorem rowR_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a b i : Nat}
    (ha : a + 8 * i + 8 ≤ 4096) (hb : b + 32 ≤ 4096) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp, .rdi] : List Reg).Nodup) :
    WP isa (.block (VG.Proof.X25519.X86_64.rowR a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (VG.Proof.X25519.X86_64.word s.mem base (a + 8 * i)).toNat * VG.Proof.X25519.X86_64.fe s.mem base b ∧
      Keeps [r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0d, h0c, h0b, h0i⟩, ⟨h12, h13, h14, h1a, h1d, h1c, h1b, h1i⟩,
    ⟨h23, h24, h2a, h2d, h2c, h2b, h2i⟩, ⟨h34, h3a, h3d, h3c, h3b, h3i⟩,
    ⟨h4a, h4d, h4c, h4b, h4i⟩, -⟩ := hd
  rw [VG.Proof.X25519.X86_64.rowR, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowStart_ok hs (by omega)) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ (VG.Proof.X25519.X86_64.readSrc_sc hs₁ (by omega)) h0a h0d (by decide) (by decide)
    (by decide) h0b) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by simp [Ne.symm h0i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ (VG.Proof.X25519.X86_64.readSrc_sc hs₂ (by omega)) h1a h1d (by decide) (by decide)
    (by decide) h1b) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by simp [Ne.symm h1i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ (VG.Proof.X25519.X86_64.readSrc_sc hs₃ (by omega)) h2a h2d (by decide) (by decide)
    (by decide) h2b) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by simp [Ne.symm h2i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₄ (VG.Proof.X25519.X86_64.readSrc_sc hs₄ (by omega)) h3a h3d (by decide) (by decide)
    (by decide) h3b) fun s₅ ⟨e5, k5⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  -- The memory and the registers along the way.
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  have M3 : s₃.mem = s.mem := k3.2.1.trans M2
  have M4 : s₄.mem = s.mem := k4.2.1.trans M3
  have C2 : s₂.gpr .rcx = s₁.gpr .rcx := k2.1 _ (by simp [Ne.symm h0c])
  have C3 : s₃.gpr .rcx = s₁.gpr .rcx := (k3.1 _ (by simp [Ne.symm h1c])).trans C2
  have C4 : s₄.gpr .rcx = s₁.gpr .rcx := (k4.1 _ (by simp [Ne.symm h2c])).trans C3
  have r0_1 : s₁.gpr r0 = s.gpr r0 := k1.1 _ (by simp [h0c, h0b])
  have r0_5 : s₅.gpr r0 = s₂.gpr r0 := by
    rw [k5.1 _ (by simp [h03, h0b, h0a, h0d]), k4.1 _ (by simp [h02, h0b, h0a, h0d]),
      k3.1 _ (by simp [h01, h0b, h0a, h0d])]
  have r1_2 : s₂.gpr r1 = s.gpr r1 := by
    rw [k2.1 _ (by simp [Ne.symm h01, h1b, h1a, h1d]), k1.1 _ (by simp [h1c, h1b])]
  have r1_5 : s₅.gpr r1 = s₃.gpr r1 := by
    rw [k5.1 _ (by simp [h13, h1b, h1a, h1d]), k4.1 _ (by simp [h12, h1b, h1a, h1d])]
  have r2_3 : s₃.gpr r2 = s.gpr r2 := by
    rw [k3.1 _ (by simp [Ne.symm h12, h2b, h2a, h2d]), k2.1 _ (by simp [Ne.symm h02, h2b, h2a, h2d]),
      k1.1 _ (by simp [h2c, h2b])]
  have r2_5 : s₅.gpr r2 = s₄.gpr r2 := k5.1 _ (by simp [h23, h2b, h2a, h2d])
  have r3_4 : s₄.gpr r3 = s.gpr r3 := by
    rw [k4.1 _ (by simp [Ne.symm h23, h3b, h3a, h3d]), k3.1 _ (by simp [Ne.symm h13, h3b, h3a, h3d]),
      k2.1 _ (by simp [Ne.symm h03, h3b, h3a, h3d]), k1.1 _ (by simp [h3c, h3b])]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, r0_1, r1_2, r2_3, r3_4, z, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.reduceMul, VG.Proof.X25519.X86_64.word] at e2 e3 e4 e5
    simp only [val4, VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word, RegUpd.gpr_setReg_of_ne _ _ h04, RegUpd.gpr_setReg_of_ne _ _ h14,
      RegUpd.gpr_setReg_of_ne _ _ h24, RegUpd.gpr_setReg_of_ne _ _ h34, r0_5, r1_5, r2_5]
    have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
        v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by intros; grind
    rw [hp]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.1]
    rw [k5.1 _ (by simp [hr.2.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k4.1 _ (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k3.1 _ (by simp [hr.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k2.1 _ (by simp [hr.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k1.1 _ (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · exact k5.2.1.trans M4
  · rw [RegUpd.rd_setReg, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [RegUpd.wr_setReg, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

/-! ## The reduction -/

/-- `reduce`, with its steps spelled out. -/
theorem reduce_eq : reduce =
    ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] : List Instr) ++ (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.reg .r12) ++
      (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.reg .r13) ++ (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.reg .r14) ++
        (VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.reg .r15) ++ fold)))) := by
  simp only [reduce, List.append_assoc]
  rfl

/-- `lo + 38 hi` of the eight words `r8–r15`: into `r8–r11` and the carry word
`rbp`. -/
theorem reduceSteps_ok (s : State) :
    WP isa (.block (([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] : List Instr) ++ (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.reg .r12) ++
      (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.reg .r13) ++ (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.reg .r14) ++
        VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.reg .r15)))))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .rbp).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) ∧
      s'.gpr .rcx = 38 ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)]) s
      (fun s' => s'.gpr .rcx = 38 ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left']
    refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]) fun s₁ ⟨c1, b1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine WP.mono (mulStep_ok s₄ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s₅ :=
    (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  refine ⟨?_, ?_, K⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [c1, g k1 .r12 (by decide), b1, g k1 .r8 (by decide)] at e2
    rw [g k2 .rcx (by decide), c1, g k2 .r13 (by decide), g k1 .r13 (by decide),
      g k2 .r9 (by decide), g k1 .r9 (by decide)] at e3
    rw [g k3 .rcx (by decide), g k2 .rcx (by decide), c1, g k3 .r14 (by decide),
      g k2 .r14 (by decide), g k1 .r14 (by decide), g k3 .r10 (by decide), g k2 .r10 (by decide),
      g k1 .r10 (by decide)] at e4
    rw [g k4 .rcx (by decide), g k3 .rcx (by decide), g k2 .rcx (by decide), c1,
      g k4 .r15 (by decide), g k3 .r15 (by decide), g k2 .r15 (by decide), g k1 .r15 (by decide),
      g k4 .r11 (by decide), g k3 .r11 (by decide), g k2 .r11 (by decide),
      g k1 .r11 (by decide)] at e5
    simp only [val4, g k5 .r8 (by decide), g k4 .r8 (by decide), g k3 .r8 (by decide),
      g k5 .r9 (by decide), g k4 .r9 (by decide), g k5 .r10 (by decide)]
    have h38 : (38 : BitVec 64).toNat = 38 := rfl
    rw [h38] at e2 e3 e4 e5
    rw [z] at e2
    omega
  · rw [g k5 .rcx (by decide), g k4 .rcx (by decide), g k3 .rcx (by decide), g k2 .rcx (by decide), c1]

/-- `fold`: `r8–r11 + 38 rbp`, with `rcx = 38` and `rbp < 2⁵²`. -/
theorem fold_ok (s : State) (hc : s.gpr .rcx = 38) (hb : (s.gpr .rbp).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % VG.Spec.X25519.P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 38 * (s.gpr .rbp).toNat) %
          VG.Spec.X25519.P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx] s s' := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rax (.reg .rbp), .mul .rcx]) s (fun s' =>
      (s'.gpr .rax).toNat = 38 * (s.gpr .rbp).toNat ∧ Keeps [.rax, .rdx] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some, execMul,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left', hc]
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [BitVec.toNat_ofNat, show (38 : BitVec 64).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (carry38_ok s₁ (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans (k2.mono (by decide))⟩
  rw [e2, e1, k1.1 .r8 (by decide), k1.1 .r9 (by decide), k1.1 .r10 (by decide),
    k1.1 .r11 (by decide)]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ops`. -/
section

/-!
# X25519 on x86-64: the field operations

Each field operation on the working space (`mul`, `mulSmall`, `add`, `sub`,
and `cswap`), as a change of the field elements `F` it reads and writes: the
element at `o` becomes the result, every byte outside it is unchanged, and so
are the registers but those the arithmetic uses (`Op`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (VG.Proof.X25519.X86_64.fe m base o)

/-- The registers the field arithmetic uses. -/
def clob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 32 bytes at `base + o` are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X25519.X86_64.Outside base o 32 s.mem s'.mem

theorem Op.scr {base : Addr} {o : Nat} {s s' : State} (h : VG.Proof.X25519.X86_64.Op base o s s') (hs : VG.Proof.X25519.X86_64.Scr s base) :
    VG.Proof.X25519.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- A field element's slot: 32 bytes of the working space. -/
abbrev Slot (o : Nat) : Prop := o + 32 ≤ 4096

/-- A field element at another slot is unchanged. -/
theorem Op.fe {base : Addr} {o : Nat} {s s' : State} (h : VG.Proof.X25519.X86_64.Op base o s s') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : VG.Proof.X25519.X86_64.Slot d) : VG.Proof.X25519.X86_64.fe s'.mem base d = VG.Proof.X25519.X86_64.fe s.mem base d :=
  h.mem.fe hd (by omega)

theorem stores_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun s' =>
      s'.mem = VG.Proof.X25519.X86_64.st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (VG.Proof.X25519.X86_64.off base d) 8 :=
    fun d hd => ⟨_, hs.wr, VG.Proof.X25519.X86_64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, State.store64,
    w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial⟩

theorem store4_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o : Nat} (ho : VG.Proof.X25519.X86_64.Slot o) :
    WP isa (.block (store4 o)) s fun s' =>
      s'.mem = VG.Proof.X25519.X86_64.st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  VG.Proof.X25519.X86_64.stores_ok hs ho _ _ _ _

theorem zero4_ok (s : State) :
    WP isa (.block zero4) s fun s' =>
      s'.gpr .r8 = 0 ∧ s'.gpr .r9 = 0 ∧ s'.gpr .r10 = 0 ∧ s'.gpr .r11 = 0 ∧
      Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [zero4, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem row0 (a b : Nat) : row a b 0 = VG.Proof.X25519.X86_64.rowR a b 0 .r8 .r9 .r10 .r11 .r12 := VG.Proof.X25519.X86_64.row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = VG.Proof.X25519.X86_64.rowR a b 1 .r9 .r10 .r11 .r12 .r13 := VG.Proof.X25519.X86_64.row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = VG.Proof.X25519.X86_64.rowR a b 2 .r10 .r11 .r12 .r13 .r14 := VG.Proof.X25519.X86_64.row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = VG.Proof.X25519.X86_64.rowR a b 3 .r11 .r12 .r13 .r14 .r15 := VG.Proof.X25519.X86_64.row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a : Nat) (B : Nat) :
    VG.Proof.X25519.X86_64.fe m base a * B = (VG.Proof.X25519.X86_64.word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((VG.Proof.X25519.X86_64.word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((VG.Proof.X25519.X86_64.word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((VG.Proof.X25519.X86_64.word m base (a + 8 * 3)).toNat * B) := by
  simp only [X86_64.fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.add_mul,
    Nat.mul_assoc]

theorem mul_mod_arith {L H V c AB : Nat} (h₁ : V + 2 ^ 256 * c = L + 38 * H)
    (h₂ : L + 2 ^ 256 * H = AB) : (V + 38 * c) % VG.Spec.X25519.P = AB % VG.Spec.X25519.P := by
  rw [← h₂, fold256, ← h₁, fold256]

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (ha : VG.Proof.X25519.X86_64.Slot a) (hb : VG.Proof.X25519.X86_64.Slot b) :
    WP isa (.block (VG.Impl.X25519.X86_64.mul o a b)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a * VG.Proof.X25519.X86_64.F s.mem base b := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [show VG.Impl.X25519.X86_64.mul o a b = zero4 ++ (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ (row a b 3 ++
    (reduce ++ store4 o))))) by simp only [VG.Impl.X25519.X86_64.mul, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.zero4_ok s) fun s₀ ⟨z8, z9, z10, z11, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff, VG.Proof.X25519.X86_64.row0]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR_ok hs₀ (by omega) hb (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff, VG.Proof.X25519.X86_64.row1]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR_ok hs₁ (by omega) hb (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff, VG.Proof.X25519.X86_64.row2]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR_ok hs₂ (by omega) hb (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff, VG.Proof.X25519.X86_64.row3]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR_ok hs₃ (by omega) hb (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [show reduce ++ store4 o = ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
      (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.reg .r12) ++ (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.reg .r13) ++
        (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.reg .r14) ++ VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.reg .r15))))) ++
      (fold ++ store4 o) by simp only [VG.Proof.X25519.X86_64.reduce_eq, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.reduceSteps_ok s₄) fun s₅ ⟨e5, c5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  have hB : val4 (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11) +
      38 * val4 (s₄.gpr .r12) (s₄.gpr .r13) (s₄.gpr .r14) (s₄.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s₄.gpr .r8).isLt; have := (s₄.gpr .r9).isLt; have := (s₄.gpr .r10).isLt
    have := (s₄.gpr .r11).isLt; have := (s₄.gpr .r12).isLt; have := (s₄.gpr .r13).isLt
    have := (s₄.gpr .r14).isLt; have := (s₄.gpr .r15).isLt
    omega
  have hc : (s₅.gpr .rbp).toNat < 39 := by
    simp only [val4] at e5 hB
    have := (s₅.gpr .r8).isLt; have := (s₅.gpr .r9).isLt; have := (s₅.gpr .r10).isLt
    have := (s₅.gpr .r11).isLt
    omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.fold_ok s₅ c5 (by omega)) fun s₆ ⟨e6, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₆ ho) fun s₇ ⟨m7, g7, rd7, wr7⟩ => ?_
  -- Memory is only read until the store.
  have M : s₆.mem = s.mem :=
    k6.2.1.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans k0.2.1)))))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [VG.Proof.X25519.X86_64.clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g7, g k6 r (by simp [h5, h6, h7, h8, h1, h3]), g k5 r (by simp [h5, h6, h7, h8, h1, h3, h2, h4]),
      g k4 r (by simp [h8, h9, h10, h11, h12, h1, h3, h2, h4]),
      g k3 r (by simp [h7, h8, h9, h10, h11, h1, h3, h2, h4]),
      g k2 r (by simp [h6, h7, h8, h9, h10, h1, h3, h2, h4]),
      g k1 r (by simp [h5, h6, h7, h8, h9, h1, h3, h2, h4]), g k0 r (by simp [h5, h6, h7, h8])]
  · rw [rd7, k6.2.2.1, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1, k0.2.2.1]
  · rw [wr7, k6.2.2.2, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2, k0.2.2.2]
  · rw [m7, M]; exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · simp only [VG.Proof.X25519.X86_64.F]
    apply toFe_mul
    rw [m7, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), e6]
    refine VG.Proof.X25519.X86_64.mul_mod_arith e5 ?_
    rw [VG.Proof.X25519.X86_64.fe_mul_expand]
    -- Every row read the same memory.
    rw [k0.2.1] at e1
    rw [k1.2.1, k0.2.1] at e2
    rw [k2.2.1, k1.2.1, k0.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1, k0.2.1] at e4
    -- The registers along the way.
    rw [z8, z9, z10, z11] at e1
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have r1 := g k2 .r8 (by decide); have r2 := g k3 .r8 (by decide); have r3 := g k4 .r8 (by decide)
    have q2 := g k3 .r9 (by decide); have q3 := g k4 .r9 (by decide); have q4 := g k4 .r10 (by decide)
    simp only [val4, hz, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e1 e2 e3 e4 ⊢
    rw [r3, r2, r1, q3, q2, q4]
    omega_using [e1, e2, e3, e4]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.AddSub`. -/
section

/-!
# X25519 on x86-64: addition and subtraction
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem ld_sc {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc hd⟩

/-- The sum of `[a]` and `[b]` into `r8–r11`, and `38 ×` its carry into `rax`. -/
theorem addPre_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a b : Nat} (ha : VG.Proof.X25519.X86_64.Slot a)
    (hb : VG.Proof.X25519.X86_64.Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * c =
          VG.Proof.X25519.X86_64.fe s.mem base a + VG.Proof.X25519.X86_64.fe s.mem base b ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.load64,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, VG.Proof.X25519.X86_64.ld_sc hs (d := a) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 8) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 8) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 16) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 16) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 24) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_add _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (ha : VG.Proof.X25519.X86_64.Slot a) (hb : VG.Proof.X25519.X86_64.Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a + VG.Proof.X25519.X86_64.F s.mem base b := by
  rw [show add o a b = [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ (carry38 ++ store4 o) from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.addPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s₁ (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [VG.Proof.X25519.X86_64.clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · simp only [VG.Proof.X25519.X86_64.F]
    apply toFe_add
    rw [m3, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), e2, x1, ← e1, fold256]

/-- The difference of `[a]` and `[b]` into `r8–r11`, and `38 ×` its borrow
into `rax`. -/
theorem subPre_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a b : Nat} (ha : VG.Proof.X25519.X86_64.Slot a)
    (hb : VG.Proof.X25519.X86_64.Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + VG.Proof.X25519.X86_64.fe s.mem base b =
          VG.Proof.X25519.X86_64.fe s.mem base a + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.load64,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, VG.Proof.X25519.X86_64.ld_sc hs (d := a) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 8) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 8) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 16) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 16) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 24) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_sub _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8–r11 - rax`, and `38 ×` its borrow into `rax`. -/
theorem borrow38_ok (s : State) :
    WP isa (.block [.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + (s.gpr .rax).toNat =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_sub (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [val4, hz, Nat.mul_zero, Nat.add_zero] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8 - rax`, when it does not borrow. -/
theorem subLow_ok (s : State) (h : (s.gpr .rax).toNat ≤ (s.gpr .r8).toNat) :
    WP isa (.block [.alu .sub .r8 (.reg .rax)]) s fun s' =>
      (s'.gpr .r8).toNat + (s.gpr .rax).toNat = (s.gpr .r8).toNat ∧ Keeps [.r8] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_sub]
    have := (s.gpr .r8).isLt
    rw [show 2 ^ 64 - (s.gpr .rax).toNat + (s.gpr .r8).toNat =
      (s.gpr .r8).toNat - (s.gpr .rax).toNat + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (ha : VG.Proof.X25519.X86_64.Slot a) (hb : VG.Proof.X25519.X86_64.Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a - VG.Proof.X25519.X86_64.F s.mem base b := by
  rw [show sub o a b = [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax)] ++ store4 o)) from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.borrow38_ok s₁) fun s₂ ⟨c', hc', e2, x2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hlow : (s₂.gpr .rax).toNat ≤ (s₂.gpr .r8).toNat := by
    rw [x2]
    rcases Nat.lt_or_ge c' 1 with h | h
    · omega
    · simp only [val4] at e2
      have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
      have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
      have := (s₁.gpr .r11).isLt
      omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subLow_ok s₂ hlow) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₃ ho) fun s₄ ⟨m4, g4, rd4, wr4⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [VG.Proof.X25519.X86_64.clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4, k3.1 r (by simp [hr.2.2.2.2.1]),
      k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]),
      k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd4, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr4, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m4, k3.2.1, k2.2.1, k1.2.1]; exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · simp only [VG.Proof.X25519.X86_64.F]
    apply toFe_sub
    rw [m4, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega)]
    have r9 := k3.1 .r9 (by decide); have r10 := k3.1 .r10 (by decide)
    have r11 := k3.1 .r11 (by decide)
    simp only [val4] at e1 e2 ⊢
    rw [r9, r10, r11]
    rw [x1] at e2
    rw [x2] at e3
    simp only [VG.Spec.X25519.P]
    omega

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Small`. -/
section

/-!
# X25519 on x86-64: multiplication by `a24`, and the swap
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem mulSmall_eq (o a : Nat) (k : BitVec 32) : mulSmall o a k =
    zero4 ++ (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.mem (sc (a + 8 * 0))) ++ (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.mem (sc (a + 8 * 1))) ++
        (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.mem (sc (a + 8 * 2))) ++
          (VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.mem (sc (a + 8 * 3))) ++
            (([.mov32 .rcx (.imm 38)] : List Instr) ++ (fold ++ store4 o))))))) := by
  simp only [mulSmall, List.append_assoc]
  rfl

/-- `k · [a]` into `r8–r11` and the carry word `rbp`, with `r8–r11 = 0`. -/
theorem smallSteps_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a)
    (k : BitVec 32) (h0 : s.gpr .r8 = 0) (h1 : s.gpr .r9 = 0) (h2 : s.gpr .r10 = 0)
    (h3 : s.gpr .r11 = 0) :
    WP isa (.block (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.mem (sc (a + 8 * 0))) ++ (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.mem (sc (a + 8 * 1))) ++
        (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.mem (sc (a + 8 * 2))) ++
          VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.mem (sc (a + 8 * 3)))))))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .rbp).toNat =
        k.toNat * VG.Proof.X25519.X86_64.fe s.mem base a ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)]) s
      (fun s' => s'.gpr .rcx = k.setWidth 64 ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left']
    refine ⟨by trivial, by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ (VG.Proof.X25519.X86_64.readSrc_sc hs₁ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ (VG.Proof.X25519.X86_64.readSrc_sc hs₂ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ (VG.Proof.X25519.X86_64.readSrc_sc hs₃ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  refine WP.mono (mulStep_ok s₄ (VG.Proof.X25519.X86_64.readSrc_sc hs₄ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide)) |>.trans (k5.mono (by decide))⟩
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  have M3 : s₃.mem = s.mem := k3.2.1.trans M2
  have M4 : s₄.mem = s.mem := k4.2.1.trans M3
  have C2 : s₂.gpr .rcx = s₁.gpr .rcx := g k2 .rcx (by decide)
  have C3 : s₃.gpr .rcx = s₁.gpr .rcx := (g k3 .rcx (by decide)).trans C2
  have C4 : s₄.gpr .rcx = s₁.gpr .rcx := (g k4 .rcx (by decide)).trans C3
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have hk : (k.setWidth 64).toNat = k.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  rw [g k1 .r8 (by decide), h0] at e2
  rw [g k2 .r9 (by decide), g k1 .r9 (by decide), h1] at e3
  rw [g k3 .r10 (by decide), g k2 .r10 (by decide), g k1 .r10 (by decide), h2] at e4
  rw [g k4 .r11 (by decide), g k3 .r11 (by decide), g k2 .r11 (by decide), g k1 .r11 (by decide),
    h3] at e5
  simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, z, hk, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.reduceMul, VG.Proof.X25519.X86_64.word] at e2 e3 e4 e5
  simp only [val4, VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word, g k5 .r8 (by decide), g k4 .r8 (by decide), g k3 .r8 (by decide),
    g k5 .r9 (by decide), g k4 .r9 (by decide), g k5 .r10 (by decide)]
  have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
      v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by intros; grind
  rw [hp]
  omega

/-- `[o] = a24 · [a]`. -/
theorem mulA24_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o a : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (mulSmall o a a24)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = Spec.X25519.a24 * VG.Proof.X25519.X86_64.F s.mem base a := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [VG.Proof.X25519.X86_64.mulSmall_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.zero4_ok s) fun s₀ ⟨z8, z9, z10, z11, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.smallSteps_ok hs₀ ha a24 z8 z9 z10 z11) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 38)]) s₁
      (fun s' => s'.gpr .rcx = 38 ∧ Keeps [.rcx] s₁ s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨c2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hc : (s₂.gpr .rbp).toNat < 2 ^ 52 := by
    rw [g k2 .rbp (by decide)]
    have hA : VG.Proof.X25519.X86_64.fe s₀.mem base a < 2 ^ 256 := by
      simp only [X86_64.fe, val4]
      have := (VG.Proof.X25519.X86_64.word s₀.mem base a).isLt; have := (VG.Proof.X25519.X86_64.word s₀.mem base (a + 8)).isLt
      have := (VG.Proof.X25519.X86_64.word s₀.mem base (a + 16)).isLt; have := (VG.Proof.X25519.X86_64.word s₀.mem base (a + 24)).isLt
      omega
    have h24 : a24.toNat = 121665 := rfl
    rw [h24] at e1
    simp only [val4] at e1
    omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.fold_ok s₂ c2 hc) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₃ ho) fun s₄ ⟨m4, g4, rd4, wr4⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [VG.Proof.X25519.X86_64.clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hr
    rw [g4, g k3 r (by simp [h1, h3, h5, h6, h7, h8]), g k2 r (by simp [h2]),
      g k1 r (by simp [h1, h2, h3, h4, h5, h6, h7, h8]), g k0 r (by simp [h5, h6, h7, h8])]
  · rw [rd4, k3.2.2.1, k2.2.2.1, k1.2.2.1, k0.2.2.1]
  · rw [wr4, k3.2.2.2, k2.2.2.2, k1.2.2.2, k0.2.2.2]
  · rw [m4, k3.2.1, k2.2.1, k1.2.1, k0.2.1]; exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · simp only [VG.Proof.X25519.X86_64.F]
    apply toFe_a24
    rw [m4, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), e3, ← k0.2.1, g k2 .r8 (by decide), g k2 .r9 (by decide),
      g k2 .r10 (by decide), g k2 .r11 (by decide), g k2 .rbp (by decide),
      show (121665 : Nat) = a24.toNat from rfl, ← e1, fold256]

/-! ## The conditional swap -/

/-- The mask of a swap bit: all ones for a swap, zero otherwise. -/
def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.X25519.X86_64.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.X25519.X86_64.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.X25519.X86_64.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.X25519.X86_64.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_eq (x y : Nat) : cswap x y =
    (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr)) ++
      (store4 x ++ stores y .r12 .r13 .r14 .r15) := by
  simp only [cswap, List.append_assoc]
  rfl

theorem cswapPre_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {x y : Nat} (hx : VG.Proof.X25519.X86_64.Slot x)
    (hy : VG.Proof.X25519.X86_64.Slot y) {sw : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if sw then VG.Proof.X25519.X86_64.fe s.mem base y else VG.Proof.X25519.X86_64.fe s.mem base x) ∧
      val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
        (if sw then VG.Proof.X25519.X86_64.fe s.mem base x else VG.Proof.X25519.X86_64.fe s.mem base y) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax] s s' := by
  apply WP.of_runBlock
  simp only [loads, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, VG.X86_64.readSrc, execAlu, State.load64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hm, VG.Proof.X25519.X86_64.ld_sc hs (d := x) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := y) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := x + 8) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := y + 8) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := x + 16) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := y + 16) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := x + 24) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := y + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.X25519.X86_64.xor_sel sw _ _).1, (VG.Proof.X25519.X86_64.xor_sel sw _ _).2]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases sw <;> rfl
  · cases sw <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- `[x], [y] = [y], [x]` if `sw` (the mask `rcx`), else unchanged. -/
theorem cswap_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {x y : Nat} (hx : VG.Proof.X25519.X86_64.Slot x)
    (hy : VG.Proof.X25519.X86_64.Slot y) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) {sw : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      (∀ r, r ∉ VG.Proof.X25519.X86_64.clob → s'.gpr r = s.gpr r) ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∃ m₁, VG.Proof.X25519.X86_64.Outside base x 32 s.mem m₁ ∧ VG.Proof.X25519.X86_64.Outside base y 32 m₁ s'.mem ∧
        VG.Proof.X25519.X86_64.fe m₁ base x = (if sw then VG.Proof.X25519.X86_64.fe s.mem base y else VG.Proof.X25519.X86_64.fe s.mem base x)) ∧
      VG.Proof.X25519.X86_64.fe s'.mem base x = (if sw then VG.Proof.X25519.X86_64.fe s.mem base y else VG.Proof.X25519.X86_64.fe s.mem base x) ∧
      VG.Proof.X25519.X86_64.fe s'.mem base y = (if sw then VG.Proof.X25519.X86_64.fe s.mem base x else VG.Proof.X25519.X86_64.fe s.mem base y) := by
  rw [VG.Proof.X25519.X86_64.cswap_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.cswapPre_ok hs hx hy hm) fun s₁ ⟨e1, e2, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₁ hx) fun s₂ ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs₂ : VG.Proof.X25519.X86_64.Scr s₂ base := ⟨(g2 _).trans hs₁.rdi, wr2 ▸ hs₁.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.X25519.X86_64.stores_ok hs₂ hy _ _ _ _) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  have o2 := VG.Proof.X25519.X86_64.st4_outside s₁.mem base (o := x) (by omega) (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10)
    (s₁.gpr .r11)
  have o3 := VG.Proof.X25519.X86_64.st4_outside s₂.mem base (o := y) (by omega) (s₂.gpr .r12) (s₂.gpr .r13) (s₂.gpr .r14)
    (s₂.gpr .r15)
  rw [← m2] at o2
  rw [← m3] at o3
  have hm1 : s₁.mem = s.mem := k1.2.1
  have fx : VG.Proof.X25519.X86_64.fe s₂.mem base x = (if sw then VG.Proof.X25519.X86_64.fe s.mem base y else VG.Proof.X25519.X86_64.fe s.mem base x) := by
    rw [m2, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), e1]
  refine ⟨fun r hr => ?_, by rw [g3, g2, k1.1 .rcx (by decide)], ?_, ?_, ⟨s₂.mem, hm1 ▸ o2, o3, fx⟩,
    ?_, ?_⟩
  · simp only [VG.Proof.X25519.X86_64.clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, g2, k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2])]
  · rw [rd3, rd2, k1.2.2.1]
  · rw [wr3, wr2, k1.2.2.2]
  · rw [o3.fe hxy (by omega), fx]
  · rw [m3, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), g2, g2, g2, g2, e2]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Sqr`. -/
section

/-!
# X25519 on x86-64: squaring

`sqr o a` in parts: the products `a_i a_j` (`i < j`) as rows of `mul`
(`sq1`–`sq3`), doubled (`sqDbl`), the squares added (`diag`, for any two
registers), and reduced as in `mul`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The square of four words, by the products of their words (with no
power of two above `2²⁵⁶`, which would exceed the threshold of exponents Lean evaluates). -/
theorem sq_words (x y z w : Nat) :
    (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
      x * x + 2 ^ 128 * (y * y) + 2 ^ 256 * (z * z) + 2 ^ 256 * (2 ^ 128 * (w * w)) +
        2 * (2 ^ 64 * (x * y) + 2 ^ 128 * (x * z) + 2 ^ 192 * (x * w) + 2 ^ 192 * (y * z) +
          2 ^ 256 * (y * w) + 2 ^ 256 * (2 ^ 64 * (z * w))) := by
  grind

theorem fe_lt (m : Mem) (base : Addr) (a : Nat) : VG.Proof.X25519.X86_64.fe m base a < 2 ^ 256 := by
  simp only [X86_64.fe, val4]
  have := (VG.Proof.X25519.X86_64.word m base a).isLt; have := (VG.Proof.X25519.X86_64.word m base (a + 8)).isLt
  have := (VG.Proof.X25519.X86_64.word m base (a + 16)).isLt; have := (VG.Proof.X25519.X86_64.word m base (a + 24)).isLt
  omega

/-- `mov32 r, 0`. -/
theorem zero_ok (s : State) (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun q hq => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-- `mov d, rbp`. -/
theorem movRbp_ok (s : State) (d : Reg) :
    WP isa (.block [.mov d (.reg .rbp)]) s fun s' => s'.gpr d = s.gpr .rbp ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun q hq => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-! ## The products `a_i a_j` -/

theorem sq1_eq (a : Nat) : sq1 a = ([.mov .rcx (.mem (sc a)), .mov32 .rbp (.imm 0)] : List Instr) ++
    (([.mov32 .r9 (.imm 0)] : List Instr) ++ (([.mov32 .r10 (.imm 0)] : List Instr) ++
      (([.mov32 .r11 (.imm 0)] : List Instr) ++ (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.mem (sc (a + 8))) ++
        (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.mem (sc (a + 16))) ++ (VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.mem (sc (a + 24))) ++
          ([.mov .r12 (.reg .rbp)] : List Instr))))))) := by
  simp only [sq1, List.append_assoc]; rfl

/-- `r9–r12 = a₀ · (a₁, a₂, a₃)`. -/
theorem sq1_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (sq1 a)) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat =
        (VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) ∧
      Keeps [.r9, .r10, .r11, .r12, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sq1_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowStart_ok hs (d := a) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.zero_ok s1 .r9) fun s2 ⟨z2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.zero_ok s2 .r10) fun s3 ⟨z3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.zero_ok s3 .r11) fun s4 ⟨z4, k4⟩ => ?_
  have hs4 := ((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s4 (VG.Proof.X25519.X86_64.readSrc_sc hs4 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s5 ⟨e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s5 (VG.Proof.X25519.X86_64.readSrc_sc hs5 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s6 (VG.Proof.X25519.X86_64.readSrc_sc hs6 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s7 ⟨e7, k7⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.movRbp_ok s7 .r12) fun s8 ⟨m8, k8⟩ => ?_
  refine ⟨?_, (((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide))⟩
  have M4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  have M6 : s6.mem = s.mem := k6.2.1.trans M5
  have C4 : s4.gpr .rcx = VG.Proof.X25519.X86_64.word s.mem base a := by
    rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), c1]
  have C5 : s5.gpr .rcx = VG.Proof.X25519.X86_64.word s.mem base a := (k5.1 _ (by decide)).trans C4
  have C6 : s6.gpr .rcx = VG.Proof.X25519.X86_64.word s.mem base a := (k6.1 _ (by decide)).trans C5
  have B4 : s4.gpr .rbp = 0 := by rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), b1]
  have R9 : s4.gpr .r9 = 0 := by rw [k4.1 _ (by decide), k3.1 _ (by decide), z2]
  have R10 : s5.gpr .r10 = 0 := by rw [k5.1 _ (by decide), k4.1 _ (by decide), z3]
  have R11 : s6.gpr .r11 = 0 := by rw [k6.1 _ (by decide), k5.1 _ (by decide), z4]
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [M4, C4, B4, R9, hz] at e5
  rw [M5, C5, R10, hz] at e6
  rw [M6, C6, R11, hz] at e7
  rw [m8, k8.1 .r9 (by decide), k7.1 .r9 (by decide), k6.1 .r9 (by decide),
    k8.1 .r10 (by decide), k7.1 .r10 (by decide), k8.1 .r11 (by decide)]
  omega

theorem sq2_eq (a : Nat) : sq2 a = ([.mov .rcx (.mem (sc (a + 8))), .mov32 .rbp (.imm 0)] : List Instr) ++
    (VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.mem (sc (a + 16))) ++ (VG.Impl.X25519.X86_64.mulStep .r12 .rbp .rcx (.mem (sc (a + 24))) ++
      ([.mov .r13 (.reg .rbp)] : List Instr))) := by
  simp only [sq2, List.append_assoc]

/-- `r11–r13 = r11–r12 + a₁ · (a₂, a₃)`. -/
theorem sq2_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (sq2 a)) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .r12).toNat + 2 ^ 128 * (s'.gpr .r13).toNat =
        (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
          (VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat +
          2 ^ 64 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) ∧
      Keeps [.r11, .r12, .r13, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sq2_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowStart_ok hs (d := a + 8) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s1 (VG.Proof.X25519.X86_64.readSrc_sc hs1 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s2 (VG.Proof.X25519.X86_64.readSrc_sc hs2 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.movRbp_ok s3 .r13) fun s4 ⟨m4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [k1.2.1, c1, b1, k1.1 .r11 (by decide), hz] at e2
  rw [k2.2.1, k1.2.1, k2.1 .rcx (by decide), c1, k2.1 .r12 (by decide), k1.1 .r12 (by decide)] at e3
  rw [m4, k4.1 .r11 (by decide), k3.1 .r11 (by decide), k4.1 .r12 (by decide)]
  omega

theorem sq3_eq (a : Nat) : sq3 a = ([.mov .rcx (.mem (sc (a + 16))), .mov32 .rbp (.imm 0)] : List Instr) ++
    (VG.Impl.X25519.X86_64.mulStep .r13 .rbp .rcx (.mem (sc (a + 24))) ++ ([.mov .r14 (.reg .rbp)] : List Instr)) := by
  simp only [sq3, List.append_assoc]

/-- `r13–r14 = r13 + a₂ a₃`. -/
theorem sq3_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (sq3 a)) s fun s' =>
      (s'.gpr .r13).toNat + 2 ^ 64 * (s'.gpr .r14).toNat =
        (s.gpr .r13).toNat + (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat ∧
      Keeps [.r13, .r14, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sq3_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowStart_ok hs (d := a + 16) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s1 (VG.Proof.X25519.X86_64.readSrc_sc hs1 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.movRbp_ok s2 .r14) fun s3 ⟨m3, k3⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [k1.2.1, c1, b1, k1.1 .r13 (by decide), hz] at e2
  rw [m3, k3.1 .r13 (by decide)]
  omega

/-! ## The doubling and the squares -/

/-- `r9–r15 = 2 · r9–r14`, `r8 = rbp = 0`. -/
theorem sqDbl_ok (s : State) :
    WP isa (.block sqDbl) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat + 2 ^ 256 * (s'.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s'.gpr .r14).toNat) + 2 ^ 256 * (2 ^ 128 * (s'.gpr .r15).toNat) =
        2 * ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
          2 ^ 192 * (s.gpr .r12).toNat + 2 ^ 256 * (s.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s.gpr .r14).toNat)) ∧
      s'.gpr .r8 = 0 ∧ s'.gpr .rbp = 0 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [sqDbl, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · have e9 := add_carry (s.gpr .r9) (s.gpr .r9)
    have e10 := adc_carry (s.gpr .r10) (s.gpr .r10) (decide (2 ^ 64 ≤ (s.gpr .r9).toNat +
      (s.gpr .r9).toNat))
    have e11 := adc_carry (s.gpr .r11) (s.gpr .r11) (decide (2 ^ 64 ≤ (s.gpr .r10).toNat +
      (s.gpr .r10).toNat + (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat))
    generalize (decide (2 ^ 64 ≤ (s.gpr .r11).toNat + (s.gpr .r11).toNat +
      (decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (s.gpr .r10).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat)).toNat)) = c11 at e11 ⊢
    have e12 := adc_carry (s.gpr .r12) (s.gpr .r12) c11
    generalize (decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r12).toNat + c11.toNat)) = c12
      at e12 ⊢
    have e13 := adc_carry (s.gpr .r13) (s.gpr .r13) c12
    generalize (decide (2 ^ 64 ≤ (s.gpr .r13).toNat + (s.gpr .r13).toNat + c12.toNat)) = c13
      at e13 ⊢
    have e14 := adc_carry (s.gpr .r14) (s.gpr .r14) c13
    generalize (decide (2 ^ 64 ≤ (s.gpr .r14).toNat + (s.gpr .r14).toNat + c13.toNat)) = c14
      at e14 ⊢
    have e15 := adc_carry (BitVec.setWidth 64 (0 : BitVec 32)) (BitVec.setWidth 64 (0 : BitVec 32))
      c14
    have hz : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [hz] at e15
    have := Bool.toNat_le c14
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- The high half of a square is at most `2⁶⁴ - 2`. -/
theorem sq_hi_le (w : BitVec 64) : w.toNat * w.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
  have h := w.isLt
  have : w.toNat * w.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `diag t u d`: the square of the word at `d` added at `t` and `u`, with
the carry word `rbp` in and out. -/
theorem diag_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {t u : Reg} {d : Nat}
    (hd : d + 8 ≤ 4096) (hta : t ≠ .rax) (htd : t ≠ .rdx) (htb : t ≠ .rbp) (hua : u ≠ .rax)
    (hud : u ≠ .rdx) (hub : u ≠ .rbp) (htu : t ≠ u) :
    WP isa (.block (diag t u d)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr u).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
        (s.gpr t).toNat + 2 ^ 64 * (s.gpr u).toNat + (s.gpr .rbp).toNat +
          (VG.Proof.X25519.X86_64.word s.mem base d).toNat * (VG.Proof.X25519.X86_64.word s.mem base d).toNat ∧
      Keeps [.rax, .rdx, t, u, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [diag, runBlock_cons, exec, VG.Proof.X25519.X86_64.readSrc_sc hs hd, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execMul,
    execAlu, Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    hta, htd, htb, hua, hud, hub, htu, Ne.symm htd, Ne.symm htb, Ne.symm hub, Ne.symm htu,
    ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · have hm := mulx_arith (VG.Proof.X25519.X86_64.word s.mem base d) (VG.Proof.X25519.X86_64.word s.mem base d)
    have hh := VG.Proof.X25519.X86_64.sq_hi_le (VG.Proof.X25519.X86_64.word s.mem base d)
    generalize hp : (VG.Proof.X25519.X86_64.word s.mem base d).toNat * (VG.Proof.X25519.X86_64.word s.mem base d).toNat = p at hm hh ⊢
    generalize hlo : BitVec.ofNat 64 p = lo at hm ⊢
    generalize hhi : BitVec.ofNat 64 (p / 2 ^ 64) = hi at hm ⊢
    have hhi' : hi.toNat ≤ 2 ^ 64 - 2 := by
      rw [← hhi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hh
    have e1 := add_carry lo (s.gpr .rbp)
    generalize decide (2 ^ 64 ≤ lo.toNat + (s.gpr .rbp).toNat) = c1 at e1 ⊢
    have e2 := adc_carry hi 0 c1
    have e3 := add_carry (s.gpr t) (lo + s.gpr .rbp)
    generalize decide (2 ^ 64 ≤ (s.gpr t).toNat + (lo + s.gpr .rbp).toNat) = c3 at e3 ⊢
    have e4 := adc_carry (s.gpr u) (hi + 0 + (BitVec.ofBool c1).setWidth 64) c3
    generalize decide (2 ^ 64 ≤ (s.gpr u).toNat + (hi + 0 + (BitVec.ofBool c1).setWidth 64).toNat +
      c3.toNat) = c4 at e4 ⊢
    have e5 := adc_carry ((0 : BitVec 32).setWidth 64) 0 c4
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have hz' : ((0 : BitVec 32).setWidth 64).toNat = 0 := rfl
    rw [hz] at e2 e5
    rw [hz'] at e5
    have := Bool.toNat_le c1; have := Bool.toNat_le c4
    have := Bool.toNat_le (decide (2 ^ 64 ≤ hi.toNat + 0 + c1.toNat))
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The square -/

open VG.Spec.X25519 (P) in
/-- `reduce`: `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [show reduce = ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
      (VG.Impl.X25519.X86_64.mulStep .r8 .rbp .rcx (.reg .r12) ++ (VG.Impl.X25519.X86_64.mulStep .r9 .rbp .rcx (.reg .r13) ++
        (VG.Impl.X25519.X86_64.mulStep .r10 .rbp .rcx (.reg .r14) ++ VG.Impl.X25519.X86_64.mulStep .r11 .rbp .rcx (.reg .r15))))) ++ fold by
      simp only [VG.Proof.X25519.X86_64.reduce_eq, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.reduceSteps_ok s) fun s₁ ⟨e1, c1, k1⟩ => ?_
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega
  have hc : (s₁.gpr .rbp).toNat < 39 := by
    simp only [val4] at e1 hB
    have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
    have := (s₁.gpr .r11).isLt
    omega
  refine WP.mono (VG.Proof.X25519.X86_64.fold_ok s₁ c1 (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans (k2.mono (by decide))⟩
  rw [e2, ← fold256, e1, fold256]

theorem sqr_eq (o a : Nat) : sqr o a = sq1 a ++ (sq2 a ++ (sq3 a ++ (sqDbl ++
    (diag .r8 .r9 a ++ (diag .r10 .r11 (a + 8) ++ (diag .r12 .r13 (a + 16) ++
      (diag .r14 .r15 (a + 24) ++ (reduce ++ store4 o)))))))) := by
  simp only [sqr, List.append_assoc]

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {o a : Nat} (ho : VG.Proof.X25519.X86_64.Slot o)
    (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a * VG.Proof.X25519.X86_64.F s.mem base a := by
  rw [VG.Proof.X25519.X86_64.sqr_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sq1_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sq2_ok hs₁ ha) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sq3_ok hs₂ ha) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqDbl_ok s₃) fun s₄ ⟨e4, z4, b4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.diag_ok hs₄ (d := a) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.diag_ok hs₅ (d := a + 8) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₆ ⟨e6, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.diag_ok hs₆ (d := a + 16) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₇ ⟨e7, k7⟩ => ?_
  have hs₇ := hs₆.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.diag_ok hs₇ (d := a + 24) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₈ ⟨e8, k8⟩ => ?_
  have hs₈ := hs₇.of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.reduce_ok s₈) fun s₉ ⟨e9, k9⟩ => ?_
  have hs₉ := hs₈.of_keeps k9 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₉ ho) fun s₁₀ ⟨m10, g10, rd10, wr10⟩ => ?_
  have M : s₉.mem = s.mem := k9.2.1.trans (k8.2.1.trans (k7.2.1.trans (k6.2.1.trans
    (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))))))
  have K : Keeps VG.Proof.X25519.X86_64.clob s s₉ :=
    ((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))
  refine ⟨⟨fun r hr => by rw [g10, K.1 r hr], by rw [rd10, K.2.2.1], by rw [wr10, K.2.2.2], ?_⟩,
    ?_⟩
  · rw [m10, M]; exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · simp only [VG.Proof.X25519.X86_64.F]
    apply toFe_mul
    rw [m10, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega), e9]
    congr 1
    -- Every part read the same memory.
    have M4 : s₄.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [M4] at e5
    rw [k5.2.1, M4] at e6
    rw [k6.2.1, k5.2.1, M4] at e7
    rw [k7.2.1, k6.2.1, k5.2.1, M4] at e8
    -- The registers along the way.
    rw [k3.1 .r9 (by decide), k2.1 .r9 (by decide), k3.1 .r10 (by decide), k2.1 .r10 (by decide),
      k3.1 .r11 (by decide), k3.1 .r12 (by decide)] at e4
    rw [z4, b4] at e5
    rw [k5.1 .r10 (by decide), k5.1 .r11 (by decide)] at e6
    rw [k6.1 .r12 (by decide), k5.1 .r12 (by decide), k6.1 .r13 (by decide),
      k5.1 .r13 (by decide)] at e7
    rw [k7.1 .r14 (by decide), k6.1 .r14 (by decide), k5.1 .r14 (by decide),
      k7.1 .r15 (by decide), k6.1 .r15 (by decide), k5.1 .r15 (by decide)] at e8
    have hb : VG.Proof.X25519.X86_64.fe s.mem base a * VG.Proof.X25519.X86_64.fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
      Nat.mul_lt_mul'' (VG.Proof.X25519.X86_64.fe_lt _ _ _) (VG.Proof.X25519.X86_64.fe_lt _ _ _)
    simp only [X86_64.fe, val4, VG.Proof.X25519.X86_64.sq_words] at hb ⊢
    rw [k8.1 .r8 (by decide), k7.1 .r8 (by decide), k6.1 .r8 (by decide), k8.1 .r9 (by decide),
      k7.1 .r9 (by decide), k6.1 .r9 (by decide), k8.1 .r10 (by decide), k7.1 .r10 (by decide),
      k8.1 .r11 (by decide), k7.1 .r11 (by decide), k8.1 .r12 (by decide), k8.1 .r13 (by decide)]
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz] at e5
    -- The products `a_i a_j` (`i < j`), then the squares added to their double.
    have hX : (s₁.gpr .r9).toNat + 2 ^ 64 * (s₁.gpr .r10).toNat + 2 ^ 128 * (s₂.gpr .r11).toNat +
        2 ^ 192 * (s₂.gpr .r12).toNat + 2 ^ 256 * (s₃.gpr .r13).toNat +
        2 ^ 256 * (2 ^ 64 * (s₃.gpr .r14).toNat) =
          (VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) +
          2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
          2 ^ 192 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) +
          2 ^ 256 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) := by
      omega_using [e1, e2, e3]
    have hS : (s₅.gpr .r8).toNat + 2 ^ 64 * (s₅.gpr .r9).toNat + 2 ^ 128 * (s₆.gpr .r10).toNat +
        2 ^ 192 * (s₆.gpr .r11).toNat + 2 ^ 256 * (s₇.gpr .r12).toNat +
        2 ^ 256 * (2 ^ 64 * (s₇.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₈.gpr .r14).toNat) +
        2 ^ 256 * (2 ^ 192 * (s₈.gpr .r15).toNat) + 2 ^ 256 * (2 ^ 256 * (s₈.gpr .rbp).toNat) =
          2 ^ 64 * (s₄.gpr .r9).toNat + 2 ^ 128 * (s₄.gpr .r10).toNat +
          2 ^ 192 * (s₄.gpr .r11).toNat + 2 ^ 256 * (s₄.gpr .r12).toNat +
          2 ^ 256 * (2 ^ 64 * (s₄.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₄.gpr .r14).toNat) +
          2 ^ 256 * (2 ^ 192 * (s₄.gpr .r15).toNat) +
          (VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base a).toNat +
          2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat) +
          2 ^ 256 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
          2 ^ 256 * (2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat *
            (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat)) := by
      omega_using [e5, e6, e7, e8]
    have hD : 2 ^ 64 * (s₄.gpr .r9).toNat + 2 ^ 128 * (s₄.gpr .r10).toNat +
        2 ^ 192 * (s₄.gpr .r11).toNat + 2 ^ 256 * (s₄.gpr .r12).toNat +
        2 ^ 256 * (2 ^ 64 * (s₄.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₄.gpr .r14).toNat) +
        2 ^ 256 * (2 ^ 192 * (s₄.gpr .r15).toNat) =
          2 * (2 ^ 64 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat) +
            2 ^ 128 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
            2 ^ 192 * ((VG.Proof.X25519.X86_64.word s.mem base a).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) +
            2 ^ 192 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat) +
            2 ^ 256 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 8)).toNat * (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat) +
            2 ^ 256 * (2 ^ 64 * ((VG.Proof.X25519.X86_64.word s.mem base (a + 16)).toNat *
              (VG.Proof.X25519.X86_64.word s.mem base (a + 24)).toNat))) := by
      omega_using [e4, hX]
    have := (s₈.gpr .rbp).toNat.zero_le
    omega_using [hS, hD, hb]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Env`. -/
section

/-!
# X25519 on x86-64: the working space as slots

The working space as 128 slots of 32 bytes (`E`), each read as a field
element: each field operation updates one slot (`Function.update`) and the
swap two, so that a sequence of operations is a chain of updates that `simp`
evaluates at any slot. The ladder's variables and temporaries are in the slots
2–19 (bytes 64–639), so the field operations change no byte outside `[64,
640)`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The working space as 128 field elements. -/
def E (m : Mem) (base : Addr) (i : Fin 128) : Spec.X25519.Fe := VG.Proof.X25519.X86_64.F m base (32 * i.val)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : VG.Proof.X25519.X86_64.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem E_update {base : Addr} {m m' : Mem} {o : Fin 128}
    (h : VG.Proof.X25519.X86_64.Outside base (32 * o.val) 32 m m') :
    VG.Proof.X25519.X86_64.E m' base = Function.update (VG.Proof.X25519.X86_64.E m base) o (VG.Proof.X25519.X86_64.F m' base (32 * o.val)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [VG.Proof.X25519.X86_64.E]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.X25519.X86_64.E, VG.Proof.X25519.X86_64.F]
    have : i.val ≠ o.val := fun h' => hi (Fin.ext h')
    rw [h.fe (by omega) (by omega)]

/-- What the field operations keep: the registers but `clob`, the regions,
and the memory outside `[64, 640)`. -/
structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X25519.X86_64.Outside base 64 576 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.X25519.X86_64.Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.X86_64.Keep base s₁ s₂) (h₂ : VG.Proof.X25519.X86_64.Keep base s₂ s₃) :
    VG.Proof.X25519.X86_64.Keep base s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem Keep.scr {base : Addr} {s s' : State} (h : VG.Proof.X25519.X86_64.Keep base s s') (hs : VG.Proof.X25519.X86_64.Scr s base) : VG.Proof.X25519.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.keep {base : Addr} {o : Nat} {s s' : State} (h : VG.Proof.X25519.X86_64.Op base o s s') (h₁ : 64 ≤ o)
    (h₂ : o + 32 ≤ 640) : VG.Proof.X25519.X86_64.Keep base s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono h₁ (by omega)⟩

/-! ## The field multiplications -/

/-- What the rest of the proof needs of the field multiplications `fld`:
each writes the field element at `o` and nothing else of the working space,
and changes only the registers `clob` (`Op`). -/
structure FieldOk (fld : Field) : Prop where
  mul : ∀ {s : State} {base : Addr}, VG.Proof.X25519.X86_64.Scr s base → ∀ {o a b : Nat}, VG.Proof.X25519.X86_64.Slot o → VG.Proof.X25519.X86_64.Slot a → VG.Proof.X25519.X86_64.Slot b →
    WP isa (.block (fld.mul o a b)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a * VG.Proof.X25519.X86_64.F s.mem base b
  sqr : ∀ {s : State} {base : Addr}, VG.Proof.X25519.X86_64.Scr s base → ∀ {o a : Nat}, VG.Proof.X25519.X86_64.Slot o → VG.Proof.X25519.X86_64.Slot a →
    WP isa (.block (fld.sqr o a)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = VG.Proof.X25519.X86_64.F s.mem base a * VG.Proof.X25519.X86_64.F s.mem base a
  a24 : ∀ {s : State} {base : Addr}, VG.Proof.X25519.X86_64.Scr s base → ∀ {o a : Nat}, VG.Proof.X25519.X86_64.Slot o → VG.Proof.X25519.X86_64.Slot a →
    WP isa (.block (fld.a24 o a)) s fun s' =>
      VG.Proof.X25519.X86_64.Op base o s s' ∧ VG.Proof.X25519.X86_64.F s'.mem base o = Spec.X25519.a24 * VG.Proof.X25519.X86_64.F s.mem base a

theorem baseline_ok : VG.Proof.X25519.X86_64.FieldOk baseline where
  mul hs _ _ _ ho ha hb := VG.Proof.X25519.X86_64.mul_ok hs ho ha hb
  sqr hs _ _ ho ha := VG.Proof.X25519.X86_64.sqr_ok hs ho ha
  a24 hs _ _ ho ha := VG.Proof.X25519.X86_64.mulA24_ok hs ho ha

/-! ## The field operations on the slots -/

variable {fld : Field} (hf : VG.Proof.X25519.X86_64.FieldOk fld)

/-- Environments: the working space's slots. -/
abbrev Env := Fin 128 → Spec.X25519.Fe

def opMul (o a b : Fin 128) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env := Function.update e o (e a * e b)
def opAdd (o a b : Fin 128) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env := Function.update e o (e a + e b)
def opSub (o a b : Fin 128) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env := Function.update e o (e a - e b)
def opA24 (o a : Fin 128) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env := Function.update e o (Spec.X25519.a24 * e a)
def opSwap (x y : Fin 128) (sw : Bool) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

/-- A slot of the ladder's: 2 to 19. -/
abbrev LSlot (o : Fin 128) : Prop := 2 ≤ o.val ∧ o.val < 20

include hf in
theorem mulE {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a b : Fin 128) (ho : VG.Proof.X25519.X86_64.LSlot o) :
    WP isa (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opMul o a b (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (hf.mul hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem sqrE {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a : Fin 128) (ho : VG.Proof.X25519.X86_64.LSlot o) :
    WP isa (.block (fld.sqr (32 * o.val) (32 * a.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opMul o a a (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (hf.sqr hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a b : Fin 128) (ho : VG.Proof.X25519.X86_64.LSlot o) :
    WP isa (.block (add (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opAdd o a b (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (VG.Proof.X25519.X86_64.add_ok hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a b : Fin 128) (ho : VG.Proof.X25519.X86_64.LSlot o) :
    WP isa (.block (sub (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opSub o a b (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (VG.Proof.X25519.X86_64.sub_ok hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem a24E {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a : Fin 128) (ho : VG.Proof.X25519.X86_64.LSlot o) :
    WP isa (.block (fld.a24 (32 * o.val) (32 * a.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opA24 o a (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (hf.a24 hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

theorem cswapE {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (x y : Fin 128) (hx : VG.Proof.X25519.X86_64.LSlot x)
    (hy : VG.Proof.X25519.X86_64.LSlot y) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (cswap (32 * x.val) (32 * y.val))) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ s'.gpr .rcx = s.gpr .rcx ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opSwap x y sw (VG.Proof.X25519.X86_64.E s.mem base) := by
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  refine WP.mono (VG.Proof.X25519.X86_64.cswap_ok hs (by omega) (by omega) (by omega) hm)
    fun s' ⟨g, gc, rd, wr, ⟨m₁, o₁, o₂, f₁⟩, fx, fy⟩ => ?_
  refine ⟨⟨g, rd, wr, (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))⟩, gc, ?_⟩
  rw [VG.Proof.X25519.X86_64.E_update o₂, VG.Proof.X25519.X86_64.E_update o₁]
  simp only [VG.Proof.X25519.X86_64.F, f₁, fy]
  cases sw <;> rfl

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Iter`. -/
section

/-!
# X25519 on x86-64: an iteration of the ladder

The start of an iteration (`stepPre`): the counter `rbx` counts down to the
bit `t`, whose byte of the array `BITS` is `k_t`; `swap ^ k_t` becomes the
mask in `rcx`, and `k_t` the new `swap` (a word at `SWAP`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

theorem ea_bits {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    s.ea { base := .rdi, index := some .rbx, disp := BITS } = VG.Proof.X25519.X86_64.off base (BITS + t) := by
  simp only [State.ea, hr, hb, VG.Proof.X25519.X86_64.off, BITS, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t 768]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      VG.Proof.X25519.X86_64.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {t : Nat} (ht : t < 255)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : VG.Proof.X25519.X86_64.word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block VG.Proof.X25519.X86_64.stepPre) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rcx = VG.Proof.X25519.X86_64.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.rbx, .rax, .rdx, .rcx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X25519.X86_64.off base SWAP) (BitVec.ofNat 64 kt) ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (VG.Proof.X25519.X86_64.off base SWAP) 8 := ⟨_, hs.wr, VG.Proof.X25519.X86_64.contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [VG.Proof.X25519.X86_64.stepPre, runBlock_cons, runStep_some, exec, VG.X86_64.readSrc, execAlu, State.load8,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hb', Option.bind_some]
  rw [VG.Proof.X25519.X86_64.ea_bits (base := base) (t := t) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
                           ite_false, reduceCtorEq, hs.rdi]) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
                           ite_true])]
  have hswap' : s.mem.readW (VG.Proof.X25519.X86_64.off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load64, State.store64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, hin, hbit, hr, hw, hswap', ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', State.setReg32]
  have e0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := rfl
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact VG.Proof.X25519.X86_64.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek], rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

variable {fld : Field} (hf : VG.Proof.X25519.X86_64.FieldOk fld)

def opsList (fld : Field) : List Instr :=
  cswap (32 * (3 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  cswap (32 * (4 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  add (32 * (7 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  sub (32 * (8 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  add (32 * (9 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  sub (32 * (10 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.sqr (32 * (11 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.sqr (32 * (12 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  fld.mul (32 * (14 : Fin 128).val) (32 * (10 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.mul (32 * (15 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  sub (32 * (13 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (12 : Fin 128).val) ++
  sub (32 * (6 : Fin 128).val) (32 * (14 : Fin 128).val) (32 * (15 : Fin 128).val) ++
  add (32 * (5 : Fin 128).val) (32 * (14 : Fin 128).val) (32 * (15 : Fin 128).val) ++
  fld.a24 (32 * (4 : Fin 128).val) (32 * (13 : Fin 128).val) ++
  fld.sqr (32 * (6 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.sqr (32 * (5 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  add (32 * (4 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  fld.mul (32 * (6 : Fin 128).val) (32 * (2 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.mul (32 * (3 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (12 : Fin 128).val) ++
  fld.mul (32 * (4 : Fin 128).val) (32 * (13 : Fin 128).val) (32 * (4 : Fin 128).val)

theorem step_eq : VG.Impl.X25519.X86_64.step fld = VG.Proof.X25519.X86_64.stepPre ++ (VG.Proof.X25519.X86_64.opsList fld ++ ([.alu .test .rbx (.reg .rbx)] : List Instr)) := by
  simp only [VG.Impl.X25519.X86_64.step, VG.Proof.X25519.X86_64.stepPre, VG.Proof.X25519.X86_64.opsList, List.append_assoc]
  rfl

/-- The slots after the field operations of an iteration. -/
def stepEnv (sw : Bool) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  VG.Proof.X25519.X86_64.opMul 4 13 4 (VG.Proof.X25519.X86_64.opMul 3 11 12 (VG.Proof.X25519.X86_64.opMul 6 2 6 (VG.Proof.X25519.X86_64.opAdd 4 11 4 (VG.Proof.X25519.X86_64.opMul 5 5 5 (VG.Proof.X25519.X86_64.opMul 6 6 6 (VG.Proof.X25519.X86_64.opA24 4 13
    (VG.Proof.X25519.X86_64.opAdd 5 14 15 (VG.Proof.X25519.X86_64.opSub 6 14 15 (VG.Proof.X25519.X86_64.opSub 13 11 12 (VG.Proof.X25519.X86_64.opMul 15 9 8 (VG.Proof.X25519.X86_64.opMul 14 10 7 (VG.Proof.X25519.X86_64.opMul 12 8 8
    (VG.Proof.X25519.X86_64.opMul 11 7 7 (VG.Proof.X25519.X86_64.opSub 10 5 6 (VG.Proof.X25519.X86_64.opAdd 9 5 6 (VG.Proof.X25519.X86_64.opSub 8 3 4 (VG.Proof.X25519.X86_64.opAdd 7 3 4 (VG.Proof.X25519.X86_64.opSwap 4 6 sw
    (VG.Proof.X25519.X86_64.opSwap 3 5 sw e)))))))))))))))))))

include hf in
/-- The field operations of an iteration, with the mask `rcx` of the swap
bit `sw`. -/
theorem ops_ok {s1 : State} {base : Addr} (hs1 : VG.Proof.X25519.X86_64.Scr s1 base) {sw : Bool}
    (hm : s1.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (VG.Proof.X25519.X86_64.opsList fld)) s1 fun s' =>
      VG.Proof.X25519.X86_64.Keep base s1 s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.stepEnv sw (VG.Proof.X25519.X86_64.E s1.mem base) := by
  simp only [VG.Proof.X25519.X86_64.opsList, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.cswapE hs1 3 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) hm) fun s2 ⟨k2, c2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.cswapE hs2 4 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (c2.trans hm)) fun s3 ⟨k3, c3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.addE hs3 7 3 4 ⟨by decide, by decide⟩) fun s4 ⟨k4, e4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subE hs4 8 3 4 ⟨by decide, by decide⟩) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.addE hs5 9 5 6 ⟨by decide, by decide⟩) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subE hs6 10 5 6 ⟨by decide, by decide⟩) fun s7 ⟨k7, e7⟩ => ?_
  have hs7 := k7.scr hs6
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrE hf hs7 11 7 ⟨by decide, by decide⟩) fun s8 ⟨k8, e8⟩ => ?_
  have hs8 := k8.scr hs7
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrE hf hs8 12 8 ⟨by decide, by decide⟩) fun s9 ⟨k9, e9⟩ => ?_
  have hs9 := k9.scr hs8
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs9 14 10 7 ⟨by decide, by decide⟩) fun s10 ⟨k10, e10⟩ => ?_
  have hs10 := k10.scr hs9
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs10 15 9 8 ⟨by decide, by decide⟩) fun s11 ⟨k11, e11⟩ => ?_
  have hs11 := k11.scr hs10
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subE hs11 13 11 12 ⟨by decide, by decide⟩) fun s12 ⟨k12, e12⟩ => ?_
  have hs12 := k12.scr hs11
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.subE hs12 6 14 15 ⟨by decide, by decide⟩) fun s13 ⟨k13, e13⟩ => ?_
  have hs13 := k13.scr hs12
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.addE hs13 5 14 15 ⟨by decide, by decide⟩) fun s14 ⟨k14, e14⟩ => ?_
  have hs14 := k14.scr hs13
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.a24E hf hs14 4 13 ⟨by decide, by decide⟩) fun s15 ⟨k15, e15⟩ => ?_
  have hs15 := k15.scr hs14
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrE hf hs15 6 6 ⟨by decide, by decide⟩) fun s16 ⟨k16, e16⟩ => ?_
  have hs16 := k16.scr hs15
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrE hf hs16 5 5 ⟨by decide, by decide⟩) fun s17 ⟨k17, e17⟩ => ?_
  have hs17 := k17.scr hs16
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.addE hs17 4 11 4 ⟨by decide, by decide⟩) fun s18 ⟨k18, e18⟩ => ?_
  have hs18 := k18.scr hs17
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs18 6 2 6 ⟨by decide, by decide⟩) fun s19 ⟨k19, e19⟩ => ?_
  have hs19 := k19.scr hs18
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs19 3 11 12 ⟨by decide, by decide⟩) fun s20 ⟨k20, e20⟩ => ?_
  have hs20 := k20.scr hs19
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs20 4 13 4 ⟨by decide, by decide⟩) fun s21 ⟨k21, e21⟩ => ?_
  refine ⟨(k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans (k9.trans (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans (k15.trans (k16.trans (k17.trans (k18.trans (k19.trans (k20.trans k21))))))))))))))))))), ?_⟩
  rw [e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2]
  rfl

/-- The ladder's loop invariant, with the counter `rbx = n`: the slots
`x1, x2, z2, x3, z3` (2–6) and the word `swap` hold the ladder's state after
the bits 254 down to `n`, and since the loop's start (`s₀`) nothing else
changed but the registers `clob` and the bytes `[64, 648)`. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : VG.Proof.X25519.X86_64.Scr s base
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X25519.X86_64.Outside base 64 584 s₀.mem s.mem
  x1 : VG.Proof.X25519.X86_64.E s.mem base 2 = u
  x2 : VG.Proof.X25519.X86_64.E s.mem base 3 = (ladderAfter k u n).x2
  z2 : VG.Proof.X25519.X86_64.E s.mem base 4 = (ladderAfter k u n).z2
  x3 : VG.Proof.X25519.X86_64.E s.mem base 5 = (ladderAfter k u n).x3
  z3 : VG.Proof.X25519.X86_64.E s.mem base 6 = (ladderAfter k u n).z3
  swap : VG.Proof.X25519.X86_64.word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap

theorem cswap_fst (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

/-- The slots of the ladder's variables after an iteration's field operations
are those of `ladderStep`. -/
theorem stepEnv_eval (e : VG.Proof.X25519.X86_64.Env) (st : Spec.X25519.Ladder) (k : Nat) (u : Spec.X25519.Fe) (t : Nat)
    (h2 : e 2 = u) (h3 : e 3 = st.x2) (h4 : e 4 = st.z2) (h5 : e 5 = st.x3) (h6 : e 6 = st.z3) :
    VG.Proof.X25519.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X25519.bit k t = 1)) e 2 = u ∧
    VG.Proof.X25519.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X25519.bit k t = 1)) e 3 = (Spec.X25519.ladderStep k u st t).x2 ∧
    VG.Proof.X25519.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X25519.bit k t = 1)) e 4 = (Spec.X25519.ladderStep k u st t).z2 ∧
    VG.Proof.X25519.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X25519.bit k t = 1)) e 5 = (Spec.X25519.ladderStep k u st t).x3 ∧
    VG.Proof.X25519.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X25519.bit k t = 1)) e 6 = (Spec.X25519.ladderStep k u st t).z3 := by
  rw [ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X25519.X86_64.stepEnv, VG.Proof.X25519.X86_64.opMul, VG.Proof.X25519.X86_64.opAdd, VG.Proof.X25519.X86_64.opSub, VG.Proof.X25519.X86_64.opA24, VG.Proof.X25519.X86_64.opSwap,
    Function.update_apply, VG.Proof.X25519.X86_64.cswap_fst, VG.Proof.X25519.X86_64.cswap_snd, h2, h3, h4, h5, h6]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

include hf in
/-- One iteration of the ladder: from the state after the bits down to
`n + 1` to the state after the bits down to `n`. -/
theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {n : Nat} (hn : n < 255)
    (hbits : ∀ t < 255, s₀.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t))
    (hi : VG.Proof.X25519.X86_64.LInv base k u s₀ s (n + 1)) :
    WP isa (.block (VG.Impl.X25519.X86_64.step fld)) s fun s' => VG.Proof.X25519.X86_64.LInv base k u s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hbit : s.mem (VG.Proof.X25519.X86_64.off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact hbits n hn
  rw [VG.Proof.X25519.X86_64.step_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.stepPre_ok hs hn hi.rbx (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) hbit hi.swap)
    fun s1 ⟨b1, m1, g1, rd1, wr1, mem1, _, _⟩ => ?_
  have hs1 : VG.Proof.X25519.X86_64.Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  have o8 : VG.Proof.X25519.X86_64.Outside base 640 8 s.mem s1.mem := by
    rw [mem1]; exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by omega)
  have e1 : VG.Proof.X25519.X86_64.E s1.mem base = Function.update (VG.Proof.X25519.X86_64.E s.mem base) 20 (VG.Proof.X25519.X86_64.F s1.mem base (32 * 20)) :=
    VG.Proof.X25519.X86_64.E_update (o := 20) (o8.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.ops_ok hf hs1 m1) fun s2 ⟨K, e2⟩ => ?_
  have hs2 := K.scr hs1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have zf : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    rw [BitVec.and_self]
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  obtain ⟨v2, v3, v4, v5, v6⟩ := VG.Proof.X25519.X86_64.stepEnv_eval (VG.Proof.X25519.X86_64.E s1.mem base) (ladderAfter k u (n + 1)) k u n
    (by rw [e1]; exact hi.x1) (by rw [e1]; exact hi.x2) (by rw [e1]; exact hi.z2)
    (by rw [e1]; exact hi.x3) (by rw [e1]; exact hi.z3)
  rw [← ladderAfter_step k u hn, ← e2] at v3 v4 v5 v6
  rw [← e2] at v2
  refine ⟨⟨⟨hs2.rdi, hs2.wr, hs2.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_, ?_, v2, v3, v4, v5, v6, ?_⟩,
    ?_⟩
  · have h' : r ∉ [Reg.rbx, .rax, .rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hb, fun h => hr (h ▸ by decide), fun h => hr (h ▸ by decide),
        fun h => hr (h ▸ by decide)⟩
    rw [RegUpd.gpr_arithFlags, K.gpr r hr, g1 r h', hi.gpr r hr hb]
  · rw [RegUpd.gpr_arithFlags, K.gpr _ (by decide), b1]
  · rw [RegUpd.rd_arithFlags, K.rd, rd1, hi.rd]
  · rw [RegUpd.wr_arithFlags, K.wr, wr1, hi.wr]
  · rw [RegUpd.mem_arithFlags]
    exact hi.mem.trans ((o8.mono (by omega) (by omega)).trans (K.mem.mono (by omega) (by omega)))
  · rw [RegUpd.mem_arithFlags, K.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega),
      mem1, ladderAfter_step k u hn]
    simp only [X86_64.word, Mem.readW_writeW_self64]
    rfl
  · rw [RegUpd.zf_arithFlags, K.gpr .rbx (by decide), b1, zf]

include hf in
/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hbits : ∀ t < 255, s₀.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 255 → VG.Proof.X25519.X86_64.LInv base k u s₀ s n →
      WP isa (.loop (.block (VG.Impl.X25519.X86_64.step fld)) .ne) s fun s' => VG.Proof.X25519.X86_64.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block (VG.Impl.X25519.X86_64.step fld)) (c := .ne)
    (Q := fun s' => VG.Proof.X25519.X86_64.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 255 ∧ VG.Proof.X25519.X86_64.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X25519.X86_64.step_ok hf (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

include hf in
/-- The ladder: the counter set to 255, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hbits : ∀ t < 255, s₀.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t))
    (hi : ∀ s', s'.gpr .rbx = BitVec.ofNat 64 255 → (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X25519.X86_64.LInv base k u s₀ s' 255) :
    WP isa (ladder fld) s fun s' => VG.Proof.X25519.X86_64.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 255)]) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X25519.X86_64.loop_ok hf hbits 255 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

/-- What a ladder leaves (`ladder`'s, or `vg_x25519_ifma`'s): the slots
`x2, z2, x3, z3` (3–6) and the word `swap` hold the ladder's final state,
and since its start (`s₀`) nothing else changed but the registers `clob` and
`rbx`, and the bytes `[64, 2216)`. -/
structure LPost (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) : Prop where
  scr : VG.Proof.X25519.X86_64.Scr s base
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X25519.X86_64.Outside base 64 2152 s₀.mem s.mem
  x2 : VG.Proof.X25519.X86_64.E s.mem base 3 = (ladderAfter k u 0).x2
  z2 : VG.Proof.X25519.X86_64.E s.mem base 4 = (ladderAfter k u 0).z2
  x3 : VG.Proof.X25519.X86_64.E s.mem base 5 = (ladderAfter k u 0).x3
  z3 : VG.Proof.X25519.X86_64.E s.mem base 6 = (ladderAfter k u 0).z3
  swap : VG.Proof.X25519.X86_64.word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u 0).swap

theorem LInv.post {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {s₀ s : State} (h : VG.Proof.X25519.X86_64.LInv base k u s₀ s 0) :
    VG.Proof.X25519.X86_64.LPost base k u s₀ s :=
  ⟨h.scr, h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.x2, h.z2, h.x3, h.z3, h.swap⟩

/-- What a ladder starts from: the bits of `k` in `BITS`, `x1 = u` and the
ladder's first state in the slots 2–6, and `swap = 0`. -/
structure LPre (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s : State) : Prop where
  scr : VG.Proof.X25519.X86_64.Scr s base
  bits : ∀ t < 255, s.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)
  x1 : VG.Proof.X25519.X86_64.E s.mem base 2 = u
  x2 : VG.Proof.X25519.X86_64.E s.mem base 3 = 1
  z2 : VG.Proof.X25519.X86_64.E s.mem base 4 = 0
  x3 : VG.Proof.X25519.X86_64.E s.mem base 5 = u
  z3 : VG.Proof.X25519.X86_64.E s.mem base 6 = 1
  swap : VG.Proof.X25519.X86_64.word s.mem base SWAP = 0

include hf in
/-- `ladder`, as a ladder: from `LPre` to `LPost`. -/
theorem ladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : VG.Proof.X25519.X86_64.LPre base k u s) :
    WP isa (ladder fld) s (VG.Proof.X25519.X86_64.LPost base k u s) :=
  WP.mono (VG.Proof.X25519.X86_64.ladder_ok hf h.bits fun s' hb g m rd wr => ⟨⟨by rw [g _ (by decide)]; exact h.scr.rdi,
      by rw [wr]; exact h.scr.wr, h.scr.nowrap⟩, fun r _ hr => g r hr, hb, rd, wr,
      by rw [m]; exact Outside.refl _ _ _ _, by rw [m, h.x1], by rw [m, h.x2]; rfl, by rw [m, h.z2]; rfl,
      by rw [m, h.x3]; rfl, by rw [m, h.z3]; rfl, by rw [m, h.swap]; rfl⟩)
    fun _ hl => hl.post

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Bits`. -/
section

/-!
# X25519 on x86-64: the bits of the scalar

`bits` stores bit `j` of byte `i` of the scalar at byte `8i + j` of `BITS`,
then the clamped bits; so byte `t` of `BITS` is bit `t` of the decoded scalar
(`scalar_bit`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The body of `bits`' loop. -/
def bitsBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 32)]

theorem bitsBody_eq : VG.Proof.X25519.X86_64.bitsBody =
    [.movzx8 .rax { base := .rsi, index := some .rbx },
    .mov .rdx (.reg .rax),
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 0) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 1,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 1) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 2,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 2) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 3,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 3) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 4,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 4) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 5,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 5) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 6,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 6) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 7,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 7) .rdx,
    .alu .add .rbx (.imm 1),
    .alu .cmp .rbx (.imm 32)] := rfl

theorem bits_eq : bits = .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block VG.Proof.X25519.X86_64.bitsBody) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .store8 (sc (BITS + 2)) .rax, .mov32 .rax (.imm 1), .store8 (sc (BITS + 254)) .rax])) := rfl

theorem ea_scalar (s : State) {k : Addr} (hk : s.gpr .rsi = k) {i : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    s.ea { base := .rsi, index := some .rbx } = k + BitVec.ofNat 64 i := by
  simp only [State.ea, hk, hb]
  rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]

theorem ea_bitAt (s : State) (j : Nat) :
    s.ea (bitAt j) = s.gpr .rdi + s.gpr .rbx * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) := by
  simp only [State.ea, bitAt, BitVec.ofInt_natCast]

theorem addr_bit (base : Addr) (i j : Nat) :
    base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) =
      VG.Proof.X25519.X86_64.off base (BITS + (8 * i + j)) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.X25519.X86_64.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    VG.Proof.X25519.X86_64.off base d = VG.Proof.X25519.X86_64.off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => VG.Proof.X25519.X86_64.ofs base x) h
    simp only [VG.Proof.X25519.X86_64.ofs_off' base hd, VG.Proof.X25519.X86_64.ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& BitVec.signExtend 64 (1 : BitVec 32)).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

/-- Bit `j` of `rax` (a byte) into `BITS[8 rbx + j]`. -/
def bitJ (j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1), .store8 (bitAt j) .rdx]

theorem bitJ_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {i : Nat} (hi : i < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {j : Nat} (hj : j < 8) :
    WP isa (.block (VG.Proof.X25519.X86_64.bitJ j)) s fun s' =>
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X25519.X86_64.off base (BITS + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have w : InRegions s.wr (VG.Proof.X25519.X86_64.off base (BITS + (8 * i + j))) 1 :=
    ⟨_, hs.wr, VG.Proof.X25519.X86_64.contains_sc (by simp only [BITS]; omega)⟩
  have e := VG.Proof.X25519.X86_64.bit_byte b j hj
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [VG.Proof.X25519.X86_64.bitJ, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.store8, VG.Proof.X25519.X86_64.ea_bitAt, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.X25519.X86_64.addr_bit, w, ite_false, reduceCtorEq, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun r hr => ?_, rfl, by first | rfl | trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; try rfl
  · simp only [VG.Proof.X25519.X86_64.bitJ, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, execShift, State.store8,
    VG.Proof.X25519.X86_64.ea_bitAt, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.X25519.X86_64.addr_bit, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩,
    ite_true, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_self]
    refine ⟨fun r hr => ?_, rfl, by first | rfl | trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; try rfl

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.X25519.X86_64.ofs base x ≠ d) : (m.writeW (VG.Proof.X25519.X86_64.off base d) v) x = m x := by
  rw [VG.Proof.X25519.X86_64.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (VG.Proof.X25519.X86_64.ofs_off' base hd) hx

theorem bitsBody_eq' : VG.Proof.X25519.X86_64.bitsBody = ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (VG.Proof.X25519.X86_64.bitJ 0 ++ (VG.Proof.X25519.X86_64.bitJ 1 ++ (VG.Proof.X25519.X86_64.bitJ 2 ++ (VG.Proof.X25519.X86_64.bitJ 3 ++ (VG.Proof.X25519.X86_64.bitJ 4 ++ (VG.Proof.X25519.X86_64.bitJ 5 ++ (VG.Proof.X25519.X86_64.bitJ 6 ++ (VG.Proof.X25519.X86_64.bitJ 7 ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 32)] : List Instr))))))))) := by
  rw [VG.Proof.X25519.X86_64.bitsBody_eq]; rfl

theorem inc_eq (i : Nat) :
    BitVec.ofNat 64 i + BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (i + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add]

theorem cmp32 : ∀ i < 32,
    (BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (32 : BitVec 32) == 0) = decide (i + 1 = 32) := by
  decide +kernel

theorem bitsBody_ok {s : State} {base k : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (hk : s.gpr .rsi = k)
    {i : Nat} (hi : i < 32) (hb : s.gpr .rbx = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 i) 1) :
    WP isa (.block VG.Proof.X25519.X86_64.bitsBody) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = 32)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ j < 8, s'.mem (VG.Proof.X25519.X86_64.off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 i)).toNat >>> j) &&& 1)) ∧
      VG.Proof.X25519.X86_64.Outside base (BITS + 8 * i) 8 s.mem s'.mem := by
  rw [VG.Proof.X25519.X86_64.bitsBody_eq', WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun s' => s'.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_scalar s hk hb, State.load8, hkr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s₀ ⟨a0, g0, m0, rd0, wr0⟩ => ?_
  have hs₀ : VG.Proof.X25519.X86_64.Scr s₀ base := ⟨(g0 _ (by decide)).trans hs.rdi, wr0 ▸ hs.wr, hs.nowrap⟩
  have hb₀ : s₀.gpr .rbx = BitVec.ofNat 64 i := (g0 _ (by decide)).trans hb
  -- The eight bits, each kept by the ones after it.
  have keep : ∀ {x y : State}, (∀ r, r ≠ .rdx → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr →
      VG.Proof.X25519.X86_64.Scr x base → x.gpr .rbx = BitVec.ofNat 64 i → x.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 →
      VG.Proof.X25519.X86_64.Scr y base ∧ y.gpr .rbx = BitVec.ofNat 64 i ∧ y.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 :=
    fun g _ wr hx hbx hax => ⟨⟨(g _ (by decide)).trans hx.rdi, wr ▸ hx.wr, hx.nowrap⟩,
      (g _ (by decide)).trans hbx, (g _ (by decide)).trans hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₀ (by omega) hb₀ a0 (j := 0) (by omega)) fun s₁ ⟨g1, rd1, wr1, m1⟩ => ?_
  obtain ⟨hs₁, hb₁, ha₁⟩ := keep g1 rd1 wr1 hs₀ hb₀ a0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₁ (by omega) hb₁ ha₁ (j := 1) (by omega)) fun s₂ ⟨g2, rd2, wr2, m2⟩ => ?_
  obtain ⟨hs₂, hb₂, ha₂⟩ := keep g2 rd2 wr2 hs₁ hb₁ ha₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₂ (by omega) hb₂ ha₂ (j := 2) (by omega)) fun s₃ ⟨g3, rd3, wr3, m3⟩ => ?_
  obtain ⟨hs₃, hb₃, ha₃⟩ := keep g3 rd3 wr3 hs₂ hb₂ ha₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₃ (by omega) hb₃ ha₃ (j := 3) (by omega)) fun s₄ ⟨g4, rd4, wr4, m4⟩ => ?_
  obtain ⟨hs₄, hb₄, ha₄⟩ := keep g4 rd4 wr4 hs₃ hb₃ ha₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₄ (by omega) hb₄ ha₄ (j := 4) (by omega)) fun s₅ ⟨g5, rd5, wr5, m5⟩ => ?_
  obtain ⟨hs₅, hb₅, ha₅⟩ := keep g5 rd5 wr5 hs₄ hb₄ ha₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₅ (by omega) hb₅ ha₅ (j := 5) (by omega)) fun s₆ ⟨g6, rd6, wr6, m6⟩ => ?_
  obtain ⟨hs₆, hb₆, ha₆⟩ := keep g6 rd6 wr6 hs₅ hb₅ ha₅
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₆ (by omega) hb₆ ha₆ (j := 6) (by omega)) fun s₇ ⟨g7, rd7, wr7, m7⟩ => ?_
  obtain ⟨hs₇, hb₇, ha₇⟩ := keep g7 rd7 wr7 hs₆ hb₆ ha₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.bitJ_ok hs₇ (by omega) hb₇ ha₇ (j := 7) (by omega)) fun s₈ ⟨g8, rd8, wr8, m8⟩ => ?_
  obtain ⟨hs₈, hb₈, ha₈⟩ := keep g8 rd8 wr8 hs₇ hb₇ ha₇
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₈, VG.Proof.X25519.X86_64.inc_eq,
    ite_true, RegUpd.zf_arithFlags, RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, VG.Proof.X25519.X86_64.cmp32 i hi]
  have hm : s₀.mem = s.mem := m0
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ite_eq_right hr.2.2, g8 r hr.2.1, g7 r hr.2.1, g6 r hr.2.1, g5 r hr.2.1, g4 r hr.2.1, g3 r hr.2.1,
      g2 r hr.2.1, g1 r hr.2.1, g0 r hr.1]
  · rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0]
  · rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
    have ne : ∀ a b, a < 8 → b < 8 → a ≠ b →
        VG.Proof.X25519.X86_64.off base (BITS + (8 * i + a)) ≠ VG.Proof.X25519.X86_64.off base (BITS + (8 * i + b)) := by
      intro a b ha hb hab h
      rw [VG.Proof.X25519.X86_64.off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)] at h
      omega
    have ne' : ∀ a b, a < 8 → b < 8 → a ≠ b →
        (VG.Proof.X25519.X86_64.off base (BITS + (8 * i + a)) = VG.Proof.X25519.X86_64.off base (BITS + (8 * i + b))) = False :=
      fun a b ha hb hab => eq_false (ne a b ha hb hab)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [VG.Proof.X25519.X86_64.writeW8_apply, ite_true, ne', ite_false]
  · intro x hx
    have hd : ∀ j < 8, VG.Proof.X25519.X86_64.ofs base x ≠ BITS + (8 * i + j) := fun j hj h => by omega
    have hb : ∀ j < 8, BITS + (8 * i + j) < 2 ^ 64 := fun j hj => by simp only [BITS]; omega
    rw [m8, m7, m6, m5, m4, m3, m2, m1, VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 7 (by omega)) (hd 7 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 6 (by omega)) (hd 6 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 5 (by omega)) (hd 5 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 4 (by omega)) (hd 4 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 3 (by omega)) (hd 3 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 2 (by omega)) (hd 2 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 1 (by omega)) (hd 1 (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (hb 0 (by omega)) (hd 0 (by omega)), hm]

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : VG.Proof.X25519.X86_64.Scr s base
  rsi : s.gpr .rsi = k
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X25519.X86_64.Outside base BITS 256 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 32, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 32, 4096 ≤ VG.Proof.X25519.X86_64.ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 32 → VG.Proof.X25519.X86_64.BInv base k s₀ s i →
      WP isa (.loop (.block VG.Proof.X25519.X86_64.bitsBody) .ne) s fun s' => VG.Proof.X25519.X86_64.BInv base k s₀ s' 32 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block VG.Proof.X25519.X86_64.bitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.X25519.X86_64.BInv base k s₀ s' 32)
    (fun m (s : State) => ∃ i, m = 32 - i ∧ i < 32 ∧ VG.Proof.X25519.X86_64.BInv base k s₀ s i) ?_ (32 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.X25519.X86_64.bitsBody_ok hb.scr hb.rsi hi hb.rbx (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', g', rd', wr', bits', o'⟩ => ?_
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.X25519.X86_64.BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.rdi, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.rsi, b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
  rcases Nat.lt_or_ge (i + 1) 32 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 32), Bool.not_false],
      32 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 31 := by omega
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 32) :
    (Spec.X25519.bytesAt m k 32).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 255`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 32, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 32, 4096 ≤ VG.Proof.X25519.X86_64.ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base BITS 256 s.mem s'.mem ∧
      ∀ t < 255, s'.mem (VG.Proof.X25519.X86_64.off base (BITS + t)) =
        BitVec.ofNat 8 (VG.Proof.X25519.bit (Spec.X25519.decodeScalar25519 (Spec.X25519.bytesAt s.mem k 32)) t) := by
  rw [VG.Proof.X25519.X86_64.bits_eq]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      VG.Proof.X25519.X86_64.BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, hk, rfl, fun r hr => ?_, rfl, rfl, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  have hs₂ := h₂.scr
  have w : ∀ d, d + 1 ≤ 4096 → InRegions s₂.wr (VG.Proof.X25519.X86_64.off base d) 1 :=
    fun d hd => ⟨_, hs₂.wr, VG.Proof.X25519.X86_64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, State.store8, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hs₂.rdi, w BITS (by simp only [BITS]; omega), w (BITS + 1) (by simp only [BITS]; omega),
    w (BITS + 2) (by simp only [BITS]; omega), w (BITS + 254) (by simp only [BITS]; omega),
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, by rw [RegUpd.rd_setReg]; exact h₂.rd, h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [hr'.1, ite_false]
    exact h₂.gpr r hr
  · have o : ∀ d, BITS ≤ d → d < BITS + 256 → VG.Proof.X25519.X86_64.ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 254) (by omega) (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 2) (by omega) (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      VG.Proof.X25519.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [VG.Proof.X25519.X86_64.writeW8_apply, VG.Proof.X25519.X86_64.off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 254 ∨ (3 ≤ t ∧ t < 254)) with
      rfl | rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 254 by omega, show t ≠ 2 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 3 by omega, ite_false]
      rw [h₂.bits t (by omega), VG.Proof.X25519.X86_64.getD_bytesAt _ _ (by omega)]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Inv`. -/
section

/-!
# X25519 on x86-64: the inversion

The inversion `invert` writes only the temporaries `T0`–`T3` (slots 16–19,
bytes `[512, 640)`) and, in its runs of squarings, the counter `rbx`; slot 17
(`T1`) ends as `VG.Proof.X25519.invert` of slot 4 (`Z2`). Each part of it is
an `ISpec`: a change of the slots by a function of them, keeping everything
else.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- What the inversion keeps: the registers but `clob` and `rbx`, the regions,
and the memory outside `[512, 640)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → r ≠ .rbx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X25519.X86_64.Outside base 512 128 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.X86_64.IKeep base s₁ s₂)
    (h₂ : VG.Proof.X25519.X86_64.IKeep base s₂ s₃) : VG.Proof.X25519.X86_64.IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : VG.Proof.X25519.X86_64.IKeep base s s') (hs : VG.Proof.X25519.X86_64.Scr s base) :
    VG.Proof.X25519.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : VG.Proof.X25519.X86_64.Env → VG.Proof.X25519.X86_64.Env) : Prop :=
  ∀ s, VG.Proof.X25519.X86_64.Scr s base → WP isa c s fun s' => VG.Proof.X25519.X86_64.IKeep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = f (VG.Proof.X25519.X86_64.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X25519.X86_64.Env → VG.Proof.X25519.X86_64.Env} (h₁ : VG.Proof.X25519.X86_64.ISpec base c₁ f)
    (h₂ : VG.Proof.X25519.X86_64.ISpec base c₂ g) : VG.Proof.X25519.X86_64.ISpec base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : VG.Proof.X25519.X86_64.Env → VG.Proof.X25519.X86_64.Env}
    (h₁ : VG.Proof.X25519.X86_64.ISpec base (.block l₁) f) (h₂ : VG.Proof.X25519.X86_64.ISpec base (.block l₂) g) :
    VG.Proof.X25519.X86_64.ISpec base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 16 to 19. -/
abbrev ISlot (o : Fin 128) : Prop := 16 ≤ o.val ∧ o.val < 20

variable {fld : Field} (hf : VG.Proof.X25519.X86_64.FieldOk fld)

include hf in
/-- A multiplication into a slot of the inversion's, which also keeps `rbx`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a b : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o) :
    WP isa (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      VG.Proof.X25519.X86_64.IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opMul o a b (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (hf.mul hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by omega) (by omega)⟩,
      h.gpr _ (by decide), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

include hf in
/-- A square into a slot of the inversion's, which also keeps `rbx`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) (o a : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o) :
    WP isa (.block (fld.sqr (32 * o.val) (32 * a.val))) s fun s' =>
      VG.Proof.X25519.X86_64.IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ VG.Proof.X25519.X86_64.E s'.mem base = VG.Proof.X25519.X86_64.opMul o a a (VG.Proof.X25519.X86_64.E s.mem base) :=
  WP.mono (hf.sqr hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by omega) (by omega)⟩,
      h.gpr _ (by decide), by rw [VG.Proof.X25519.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem mulI (base : Addr) (o a b : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o) :
    VG.Proof.X25519.X86_64.ISpec base (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val))) (VG.Proof.X25519.X86_64.opMul o a b) :=
  fun _ hs => WP.mono (VG.Proof.X25519.X86_64.mulI_ok hf hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

include hf in
theorem sqrI (base : Addr) (o a : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o) :
    VG.Proof.X25519.X86_64.ISpec base (.block (fld.sqr (32 * o.val) (32 * a.val))) (VG.Proof.X25519.X86_64.opMul o a a) :=
  fun _ hs => WP.mono (VG.Proof.X25519.X86_64.sqrI_ok hf hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

/-- `rbx = k`. -/
theorem setRbx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 k))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- `rbx -= 1`, from `rbx = k + 1`: the flag `ZF` says whether `k = 0`. -/
theorem decRbx_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k = 0)) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zf : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb', RegUpd.gpr_setReg_self, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, zf]
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false,
    RegUpd.gpr_arithFlags], trivial, trivial, trivial, trivial⟩

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : Fin 128) (n : Nat) (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Fin 128) (e : VG.Proof.X25519.X86_64.Env) (v : Spec.X25519.Fe) :
    VG.Proof.X25519.X86_64.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X25519.X86_64.opMul, Function.update_self, Function.update_idem]

include hf in
/-- The loop of `sqn`, with the counter `rbx = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : VG.Proof.X25519.X86_64.Scr s₀ base) (o : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → VG.Proof.X25519.X86_64.IKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      VG.Proof.X25519.X86_64.E s.mem base = Function.update (VG.Proof.X25519.X86_64.E s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fld.sqr (32 * o.val) (32 * o.val) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun s' =>
        VG.Proof.X25519.X86_64.IKeep base s₀ s' ∧ VG.Proof.X25519.X86_64.E s'.mem base = Function.update (VG.Proof.X25519.X86_64.E s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ VG.Proof.X25519.X86_64.IKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    VG.Proof.X25519.X86_64.E s.mem base = Function.update (VG.Proof.X25519.X86_64.E s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrI_ok hf (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.decRbx_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : VG.Proof.X25519.X86_64.IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have e2 : VG.Proof.X25519.X86_64.E s2.mem base = Function.update (VG.Proof.X25519.X86_64.E s₀.mem base) o (sqn x (n - m)) := by
    rw [m2, e1, he, VG.Proof.X25519.X86_64.opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, k2, b2, e2⟩

include hf in
/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Fin 128) (ho : VG.Proof.X25519.X86_64.ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    VG.Proof.X25519.X86_64.ISpec base (Impl.X25519.X86_64.sqn fld (32 * o.val) (32 * a.val) n) (VG.Proof.X25519.X86_64.opSqn o a n) := by
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrI_ok hf hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.setRbx_ok s1 (n - 1) (by omega)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : VG.Proof.X25519.X86_64.IKeep base s s2 := k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine VG.Proof.X25519.X86_64.sqLoop_ok hf hs o ho (VG.Proof.X25519.X86_64.E s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega]
  rfl

/-! ## The inversion -/

/-- The slots after the inversion. -/
def invEnv (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  VG.Proof.X25519.X86_64.opMul 17 17 16 (VG.Proof.X25519.X86_64.opSqn 17 17 5 (VG.Proof.X25519.X86_64.opMul 17 18 17 (VG.Proof.X25519.X86_64.opSqn 18 18 50 (VG.Proof.X25519.X86_64.opMul 18 19 18 (VG.Proof.X25519.X86_64.opSqn 19 18 100
    (VG.Proof.X25519.X86_64.opMul 18 18 17 (VG.Proof.X25519.X86_64.opSqn 18 17 50 (VG.Proof.X25519.X86_64.opMul 17 18 17 (VG.Proof.X25519.X86_64.opSqn 18 18 10 (VG.Proof.X25519.X86_64.opMul 18 19 18 (VG.Proof.X25519.X86_64.opSqn 19 18 20
    (VG.Proof.X25519.X86_64.opMul 18 18 17 (VG.Proof.X25519.X86_64.opSqn 18 17 10 (VG.Proof.X25519.X86_64.opMul 17 18 17 (VG.Proof.X25519.X86_64.opSqn 18 17 5 (VG.Proof.X25519.X86_64.opMul 17 17 18
    (VG.Proof.X25519.X86_64.opMul 18 16 16 (VG.Proof.X25519.X86_64.opMul 16 16 17 (VG.Proof.X25519.X86_64.opMul 17 4 17 (VG.Proof.X25519.X86_64.opMul 17 17 17 (VG.Proof.X25519.X86_64.opMul 17 16 16
    (VG.Proof.X25519.X86_64.opMul 16 4 4 e))))))))))))))))))))))

include hf in
theorem invert_spec (base : Addr) : VG.Proof.X25519.X86_64.ISpec base (Impl.X25519.X86_64.invert fld) VG.Proof.X25519.X86_64.invEnv := by
  have h : VG.Proof.X25519.X86_64.ISpec base _ _ :=
    (VG.Proof.X25519.X86_64.sqrI hf base 16 4 ⟨by decide, by decide⟩).seq <|
    ((VG.Proof.X25519.X86_64.sqrI hf base 17 16 ⟨by decide, by decide⟩).append
      (VG.Proof.X25519.X86_64.sqrI hf base 17 17 ⟨by decide, by decide⟩)).seq <|
    ((((VG.Proof.X25519.X86_64.mulI hf base 17 4 17 ⟨by decide, by decide⟩).append
      (VG.Proof.X25519.X86_64.mulI hf base 16 16 17 ⟨by decide, by decide⟩)).append
      (VG.Proof.X25519.X86_64.sqrI hf base 18 16 ⟨by decide, by decide⟩)).append
      (VG.Proof.X25519.X86_64.mulI hf base 17 17 18 ⟨by decide, by decide⟩)).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 18 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 18 17 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 19 18 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 18 18 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 18 17 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 19 18 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 18 18 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.X25519.X86_64.mulI hf base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.X25519.X86_64.sqnI hf base 17 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (VG.Proof.X25519.X86_64.mulI hf base 17 17 16 ⟨by decide, by decide⟩)
  exact h

theorem invEnv_eval (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.invEnv e 17 = VG.Proof.X25519.invert (e 4) := by
  simp only [↓reduceIte, VG.Proof.X25519.X86_64.invEnv, VG.Proof.X25519.X86_64.opMul, VG.Proof.X25519.X86_64.opSqn, Function.update_apply]
  rfl

include hf in
theorem invert_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) :
    WP isa (Impl.X25519.X86_64.invert fld) s fun s' =>
      (∀ r, r ∉ VG.Proof.X25519.X86_64.clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base 512 128 s.mem s'.mem ∧
      VG.Proof.X25519.X86_64.E s'.mem base 17 = VG.Proof.X25519.invert (VG.Proof.X25519.X86_64.E s.mem base 4) :=
  WP.mono (VG.Proof.X25519.X86_64.invert_spec hf base s hs) fun _ ⟨k, e⟩ =>
    ⟨k.gpr, k.rd, k.wr, k.mem, by rw [e, VG.Proof.X25519.X86_64.invEnv_eval]⟩

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Freeze`. -/
section

/-!
# X25519 on x86-64: the full reduction

`freeze a` leaves in `r8–r11` the residue of `[a]` below `p`: bit 255 folded
in as 19 gives `x < 2²⁵⁵ + 19`, then `x + 19 - 2²⁵⁵` (which is `x - p`) is
selected if it is not negative.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Spec.X25519 (P)

/-- The fold of bit 255. -/
def freezeA (a : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .mov .r9 (.mem (sc (a + 8))), .mov .r10 (.mem (sc (a + 16))),
    .mov .r11 (.mem (sc (a + 24))),
    .mov .rax (.reg .r11), .shift .shr .rax 63, .movImm64 .rdx low63, .alu .and .r11 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .and .rcx (.imm 19),
    .alu .add .r8 (.reg .rcx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)]

theorem fold_top (a0 a1 a2 a3 a3' m : BitVec 64) (hm : m.toNat = 19 * (a3.toNat / 2 ^ 63))
    (hl : a3'.toNat = a3.toNat % 2 ^ 63) :
    let c0 := decide (2 ^ 64 ≤ a0.toNat + m.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + (0 : BitVec 64).toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + (0 : BitVec 64).toNat + c1.toNat)
    let v := val4 (a0 + m) (a1 + 0 + (BitVec.ofBool c0).setWidth 64)
      (a2 + 0 + (BitVec.ofBool c1).setWidth 64) (a3' + 0 + (BitVec.ofBool c2).setWidth 64)
    v % P = val4 a0 a1 a2 a3 % P ∧ v < 2 ^ 255 + 19 := by
  intro c0 c1 c2 v
  have e := chain_add a0 a1 a2 a3' m 0 0 0
  change v + 2 ^ 256 * _ = _ at e
  clear_value v c2 c1 c0
  have h0 := a0.isLt; have h1 := a1.isLt; have h2 := a2.isLt; have h3 := a3.isLt
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [val4, hz] at e
  have hv : val4 a0 a1 a2 a3 = v + P * (a3.toNat / 2 ^ 63) := by
    simp only [val4, P]; omega
  exact ⟨by rw [hv, Nat.add_mul_mod_self_left], by omega⟩

theorem and_low63 (x : BitVec 64) : (x &&& low63).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and, show low63.toNat = 2 ^ 63 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem freezeA_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (VG.Proof.X25519.X86_64.freezeA a)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P = VG.Proof.X25519.X86_64.fe s.mem base a % P ∧
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) < 2 ^ 255 + 19 ∧
      s'.gpr .rdx = low63 ∧ Keeps [.r8, .r9, .r10, .r11, .rax, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [VG.Proof.X25519.X86_64.freezeA, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    execShift, State.load64, State.setReg32, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, hs.rdi, VG.Proof.X25519.X86_64.ld_sc hs (d := a) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 8) (by omega),
    VG.Proof.X25519.X86_64.ld_sc hs (d := a + 16) (by omega), VG.Proof.X25519.X86_64.ld_sc hs (d := a + 24) (by omega),
    show 1 ≤ 63 ∧ 63 ≤ 63 from ⟨by omega, by omega⟩, ite_true, ite_false, reduceCtorEq, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', se0]
  have ht : ∀ x : BitVec 64, (x >>> 63).toNat = x.toNat / 2 ^ 63 := fun x => by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hm : ∀ x : BitVec 64,
      (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 &&& BitVec.signExtend 64 (19 : BitVec 32)).toNat =
        19 * (x.toNat / 2 ^ 63) := fun x => by
    have hx := x.isLt
    rcases (by omega : x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1) with h | h
    · rw [BitVec.eq_of_toNat_eq (show (x >>> 63).toNat = (0 : BitVec 64).toNat by rw [ht, h]; rfl), h]
      decide
    · rw [BitVec.eq_of_toNat_eq (show (x >>> 63).toNat = (1 : BitVec 64).toNat by rw [ht, h]; rfl), h]
      decide
  obtain ⟨e₁, e₂⟩ := VG.Proof.X25519.X86_64.fold_top _ _ _ _ _ _ (hm _) (VG.Proof.X25519.X86_64.and_low63 (s.mem.readW (VG.Proof.X25519.X86_64.off base (a + 24)) 64))
  refine ⟨e₁, e₂, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- `x + 19` into `r12–r15`, and the mask of its bit 255 (`x ≥ p`) into `rcx`,
with the bit cleared. -/
def freezeB : List Instr :=
  [.mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11),
    .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)]

theorem add19_top (a0 a1 a2 a3 : BitVec 64) (hx : val4 a0 a1 a2 a3 < 2 ^ 255 + 19) :
    let b := BitVec.signExtend 64 (19 : BitVec 32)
    let c0 := decide (2 ^ 64 ≤ a0.toNat + b.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + (0 : BitVec 64).toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + (0 : BitVec 64).toNat + c1.toNat)
    let w3 := a3 + 0 + (BitVec.ofBool c2).setWidth 64
    BitVec.setWidth 64 (0 : BitVec 32) - w3 >>> 63 = VG.Proof.X25519.X86_64.mask (decide (P ≤ val4 a0 a1 a2 a3)) ∧
    (P ≤ val4 a0 a1 a2 a3 → val4 (a0 + b) (a1 + 0 + (BitVec.ofBool c0).setWidth 64)
      (a2 + 0 + (BitVec.ofBool c1).setWidth 64) (w3 &&& low63) = val4 a0 a1 a2 a3 - P) := by
  intro b c0 c1 c2 w3
  have e := chain_add a0 a1 a2 a3 b 0 0 0
  change val4 _ _ _ w3 + 2 ^ 256 * _ = _ at e
  clear_value w3 c2
  generalize a0 + b = w0 at e ⊢
  generalize a1 + 0 + (BitVec.ofBool c0).setWidth 64 = w1 at e ⊢
  generalize a2 + 0 + (BitVec.ofBool c1).setWidth 64 = w2 at e ⊢
  have hb : b.toNat = 19 := rfl
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  simp only [val4, hb, hz] at e hx ⊢
  have ht : (w3 >>> 63).toNat = w3.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl := VG.Proof.X25519.X86_64.and_low63 w3
  by_cases h : P ≤ a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
  · have h1' : w3.toNat / 2 ^ 63 = 1 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (1 : BitVec 64).toNat by rw [ht, h1']; rfl),
      decide_eq_true h]
    refine ⟨by decide, fun _ => ?_⟩
    rw [hl]; simp only [P] at h ⊢; omega
  · have h0' : w3.toNat / 2 ^ 63 = 0 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (0 : BitVec 64).toNat by rw [ht, h0']; rfl),
      decide_eq_false h]
    exact ⟨by decide, fun h' => absurd h' h⟩

theorem freezeB_ok (s : State)
    (hx : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) < 2 ^ 255 + 19)
    (hd : s.gpr .rdx = low63) :
    WP isa (.block VG.Proof.X25519.X86_64.freezeB) s fun s' =>
      s'.gpr .rcx = VG.Proof.X25519.X86_64.mask (decide (P ≤ val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11))) ∧
      (P ≤ val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) →
        val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) - P) ∧
      Keeps [.r12, .r13, .r14, .r15, .rax, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [VG.Proof.X25519.X86_64.freezeB, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    execShift, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, hd, show 1 ≤ 63 ∧ 63 ≤ 63 from ⟨by omega, by omega⟩,
    ite_true, ite_false, reduceCtorEq, and_self, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se0]
  obtain ⟨e₁, e₂⟩ := VG.Proof.X25519.X86_64.add19_top _ _ _ _ hx
  refine ⟨e₁, e₂, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- The selection by the mask `rcx`. -/
def freezeC : List Instr :=
  [.alu .xor .r12 (.reg .r8), .alu .and .r12 (.reg .rcx), .alu .xor .r8 (.reg .r12),
    .alu .xor .r13 (.reg .r9), .alu .and .r13 (.reg .rcx), .alu .xor .r9 (.reg .r13),
    .alu .xor .r14 (.reg .r10), .alu .and .r14 (.reg .rcx), .alu .xor .r10 (.reg .r14),
    .alu .xor .r15 (.reg .r11), .alu .and .r15 (.reg .rcx), .alu .xor .r11 (.reg .r15)]

theorem xor_sel' (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((b ^^^ a) &&& VG.Proof.X25519.X86_64.mask sw) = if sw then b else a := by
  rw [BitVec.xor_comm b a]; exact (VG.Proof.X25519.X86_64.xor_sel sw a b).1

theorem freezeC_ok (s : State) {sw : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block VG.Proof.X25519.X86_64.freezeC) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if sw then val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)
          else val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  apply WP.of_runBlock
  simp only [VG.Proof.X25519.X86_64.freezeC, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hm, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.X25519.X86_64.xor_sel']
  refine ⟨by cases sw <;> rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem freeze_eq (a : Nat) : freeze a = VG.Proof.X25519.X86_64.freezeA a ++ (VG.Proof.X25519.X86_64.freezeB ++ VG.Proof.X25519.X86_64.freezeC) := rfl

/-- `freeze a`: `r8–r11` is `[a] mod p`. -/
theorem freeze_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X25519.X86_64.Slot a) :
    WP isa (.block (freeze a)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) = VG.Proof.X25519.X86_64.fe s.mem base a % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx] s s' := by
  rw [VG.Proof.X25519.X86_64.freeze_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.freezeA_ok hs ha) fun s₁ ⟨e₁, l₁, d₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.freezeB_ok s₁ l₁ d₁) fun s₂ ⟨m₂, y₂, k₂⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.freezeC_ok s₂ m₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [k₂.1 .r8 (by decide), k₂.1 .r9 (by decide), k₂.1 .r10 (by decide),
    k₂.1 .r11 (by decide)] at v₃
  refine ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))⟩
  rw [v₃, ← e₁]
  generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = x at l₁ y₂ ⊢
  by_cases h : P ≤ x
  · simp only [decide_eq_true h, ite_true]
    rw [y₂ h]; simp only [P] at h l₁ ⊢; omega
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega)).symm

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Setup`. -/
section

/-!
# X25519 on x86-64: reading the arguments

`setup` reads the u-coordinate, saves the callee-saved registers at the start
of the working space, and sets the ladder's variables to their initial values.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = VG.Proof.X25519.X86_64.off (s.gpr b) d := rfl

/-- The u-coordinate, decoded. -/
theorem loadU_ok (s : State) {p : Addr} (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off p d) 8) :
    WP isa (.block loadU) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [loadU, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.load64,
    VG.Proof.X25519.X86_64.ea_at, hp, hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega),
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _), leNum_bytesAt_words64,
      show VG.Proof.X25519.X86_64.off p 0 = p from BitVec.add_zero p, show p + 8 = VG.Proof.X25519.X86_64.off p 8 from rfl,
      show p + 16 = VG.Proof.X25519.X86_64.off p 16 from rfl, show p + 24 = VG.Proof.X25519.X86_64.off p 24 from rfl]
    have := VG.Proof.X25519.X86_64.and_low63 ((s.mem.readW (VG.Proof.X25519.X86_64.off p 24) 64))
    simp only [val4]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-! ## Saving the callee-saved registers -/

theorem word_writeW_sep (m : Mem) (base : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    VG.Proof.X25519.X86_64.word (m.writeW (VG.Proof.X25519.X86_64.off base e) v) base d = VG.Proof.X25519.X86_64.word m base d :=
  Mem.readW_writeW_sep (VG.Proof.X25519.X86_64.sep_off base h hd he) (by decide)

theorem word_writeW_self (m : Mem) (base : Addr) (v : BitVec 64) (d : Nat) :
    VG.Proof.X25519.X86_64.word (m.writeW (VG.Proof.X25519.X86_64.off base d) v) base d = v :=
  Mem.readW_writeW_self64 _ _ _

theorem Outside.writeW {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base o n m m')
    {d : Nat} (ho : o ≤ d) (hd : d + 8 ≤ o + n) (hn : d + 8 < 2 ^ 64) (v : BitVec 64) :
    VG.Proof.X25519.X86_64.Outside base o n m (m'.writeW (VG.Proof.X25519.X86_64.off base d) v) :=
  h.trans ((VG.Proof.X25519.X86_64.writeW_outside m' base v hn).mono ho hd)

/-- The callee-saved registers of `g`, saved at the start of the working space. -/
abbrev Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved m base g saved

theorem saved_lt : ∀ rd ∈ saved, rd.2 + 8 ≤ 48 := by decide

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Saved base g m)
    {o n : Nat} (ho : VG.Proof.X25519.X86_64.Outside base o n m m') (h48 : 48 ≤ o) : VG.Proof.X25519.X86_64.Saved base g m' := fun rd hrd => by
  have := VG.Proof.X25519.X86_64.saved_lt rd hrd
  exact (ho.word (by omega) (by omega)).trans (h rd hrd)

theorem save_ok {s : State} {base : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.X25519.X86_64.Outside base 0 48 s.mem s'.mem ∧
      VG.Proof.X25519.X86_64.Saved base s.gpr s'.mem := by
  refine WP.mono (Spill.save_ok .rcx saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := VG.Proof.X25519.X86_64.saved_lt p hp; rw [hc]; exact ⟨_, hw, VG.Proof.X25519.X86_64.contains_sc (by omega)⟩
  · rw [hm, hc]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ VG.Proof.X25519.X86_64.saved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, VG.Proof.X25519.X86_64.ofs] at hx hx'
    omega
  · rw [hm, hc]; exact Spill.saveMem_saved _ _ _ _ (by decide)

/-! ## The initial values -/

theorem E_st4 (m : Mem) (base : Addr) {o : Nat} (i : Fin 128) (hi : o = 32 * i.val)
    (w0 w1 w2 w3 : BitVec 64) :
    VG.Proof.X25519.X86_64.E (VG.Proof.X25519.X86_64.st4 m base o w0 w1 w2 w3) base = Function.update (VG.Proof.X25519.X86_64.E m base) i (toFe (val4 w0 w1 w2 w3)) := by
  subst hi
  rw [VG.Proof.X25519.X86_64.E_update (VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _), VG.Proof.X25519.X86_64.F, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega)]

theorem movs_ok (s : State) :
    WP isa (.block ([.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr)) s fun s' =>
      s'.gpr .r12 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .rcx ∧ Keeps [.r12, .rdi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem consts_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rax = 0 ∧ s'.gpr .rdx = 1 ∧ Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem storeSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) :
    WP isa (.block ([.store (sc SWAP) .rax] : List Instr)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.X25519.X86_64.off base SWAP) (s.gpr .rax) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, State.store64,
    show InRegions s.wr (VG.Proof.X25519.X86_64.off base SWAP) 8 from ⟨_, hs.wr, VG.Proof.X25519.X86_64.contains_sc (by decide)⟩, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem setup_eq : setup = loadU ++ (save ++ (([.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] :
    List Instr) ++ (store4 X1 ++ (store4 X3 ++ (([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] :
    List Instr) ++ (stores X2 .rdx .rax .rax .rax ++ (stores Z2 .rax .rax .rax .rax ++
    (stores Z3 .rdx .rax .rax .rax ++ ([.store (sc SWAP) .rax] : List Instr))))))))) := by
  simp only [setup, List.append_assoc]

/-- `setup`: the ladder's initial state, from the u-coordinate at `p`. -/
theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) (hn : base.toNat + 4096 ≤ 2 ^ 64) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off p d) 8) :
    WP isa (.block setup) s fun s' =>
      VG.Proof.X25519.X86_64.Scr s' base ∧ s'.gpr .r12 = s.gpr .rdi ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.X25519.X86_64.Outside base 0 4096 s.mem s'.mem ∧ VG.Proof.X25519.X86_64.Saved base s.gpr s'.mem ∧
      VG.Proof.X25519.X86_64.E s'.mem base 2 = toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) ∧
      VG.Proof.X25519.X86_64.E s'.mem base 3 = 1 ∧ VG.Proof.X25519.X86_64.E s'.mem base 4 = 0 ∧
      VG.Proof.X25519.X86_64.E s'.mem base 5 = toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) ∧
      VG.Proof.X25519.X86_64.E s'.mem base 6 = 1 ∧ VG.Proof.X25519.X86_64.word s'.mem base SWAP = 0 := by
  rw [VG.Proof.X25519.X86_64.setup_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.loadU_ok s hp hr) fun s₁ ⟨u₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.save_ok (s := s₁) (base := base) (by rw [k₁.1 _ (by decide)]; exact hc)
    (by rw [k₁.2.2.2]; exact hw)) fun s₂ ⟨g₂, rd₂, wr₂, o₂, sv₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movs_ok s₂) fun s₃ ⟨r12₃, rdi₃, k₃⟩ => ?_
  have hs₃ : VG.Proof.X25519.X86_64.Scr s₃ base :=
    ⟨by rw [rdi₃, g₂, k₁.1 _ (by decide), hc], by rw [k₃.2.2.2, wr₂, k₁.2.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₃ (o := X1) (by decide)) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  have hs₄ : VG.Proof.X25519.X86_64.Scr s₄ base := ⟨(g₄ _).trans hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hs₄ (o := X3) (by decide)) fun s₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
  have hs₅ : VG.Proof.X25519.X86_64.Scr s₅ base := ⟨(g₅ _).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.consts_ok s₅) fun s₆ ⟨rax₆, rdx₆, k₆⟩ => ?_
  have hs₆ : VG.Proof.X25519.X86_64.Scr s₆ base := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.stores_ok hs₆ (o := X2) (by decide) .rdx .rax .rax .rax)
    fun s₇ ⟨m₇, g₇, rd₇, wr₇⟩ => ?_
  have hs₇ : VG.Proof.X25519.X86_64.Scr s₇ base := ⟨(g₇ _).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.stores_ok hs₇ (o := Z2) (by decide) .rax .rax .rax .rax)
    fun s₈ ⟨m₈, g₈, rd₈, wr₈⟩ => ?_
  have hs₈ : VG.Proof.X25519.X86_64.Scr s₈ base := ⟨(g₈ _).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.stores_ok hs₈ (o := Z3) (by decide) .rdx .rax .rax .rax)
    fun s₉ ⟨m₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : VG.Proof.X25519.X86_64.Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (VG.Proof.X25519.X86_64.storeSwap_ok hs₉) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have G : ∀ r, r ∉ [Reg.rax, .rdx] → s'.gpr r = s₃.gpr r := fun r hr => by
    rw [g', g₉, g₈, g₇, k₆.1 r hr, g₅, g₄]
  have G₁ : ∀ r, r ∉ [Reg.r8, .r9, .r10, .r11, .rax] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂, k₁.1 r hr]
  have e' : VG.Proof.X25519.X86_64.E s'.mem base = Function.update (VG.Proof.X25519.X86_64.E s₉.mem base) 20 (VG.Proof.X25519.X86_64.F s'.mem base (32 * 20)) := by
    rw [m']; exact VG.Proof.X25519.X86_64.E_update ((VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  have e₉ := VG.Proof.X25519.X86_64.E_st4 (o := Z3) s₈.mem base 6 rfl (s₈.gpr .rdx) (s₈.gpr .rax) (s₈.gpr .rax) (s₈.gpr .rax)
  have e₈ := VG.Proof.X25519.X86_64.E_st4 (o := Z2) s₇.mem base 4 rfl (s₇.gpr .rax) (s₇.gpr .rax) (s₇.gpr .rax) (s₇.gpr .rax)
  have e₇ := VG.Proof.X25519.X86_64.E_st4 (o := X2) s₆.mem base 3 rfl (s₆.gpr .rdx) (s₆.gpr .rax) (s₆.gpr .rax) (s₆.gpr .rax)
  have e₅ := VG.Proof.X25519.X86_64.E_st4 (o := X3) s₄.mem base 5 rfl (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11)
  have e₄ := VG.Proof.X25519.X86_64.E_st4 (o := X1) s₃.mem base 2 rfl (s₃.gpr .r8) (s₃.gpr .r9) (s₃.gpr .r10) (s₃.gpr .r11)
  rw [← m₉] at e₉; rw [← m₈] at e₈; rw [← m₇] at e₇; rw [← m₅] at e₅; rw [← m₄] at e₄
  have hu : ∀ t : State, (∀ r, r ∉ [Reg.rax, .rdx] → t.gpr r = s₃.gpr r) →
      toFe (val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11)) =
        toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) := fun t ht => by
    rw [ht _ (by decide), ht _ (by decide), ht _ (by decide), ht _ (by decide),
      k₃.1 _ (by decide), k₃.1 _ (by decide), k₃.1 _ (by decide), k₃.1 _ (by decide), g₂, u₁]
  have one : toFe (val4 1 0 0 0) = 1 := rfl
  have zero : toFe (val4 0 0 0 0) = 0 := rfl
  have r₈ : s₈.gpr .rdx = 1 ∧ s₈.gpr .rax = 0 := ⟨by rw [g₈, g₇, rdx₆], by rw [g₈, g₇, rax₆]⟩
  have r₇ : s₇.gpr .rax = 0 := by rw [g₇, rax₆]
  have o₃ : VG.Proof.X25519.X86_64.Outside base 0 4096 s.mem s₃.mem := by
    rw [k₃.2.1]; exact fun x hx => (o₂.mono (by omega) (by omega) x hx).trans (by rw [k₁.2.1])
  have o' : VG.Proof.X25519.X86_64.Outside base 64 4032 s₃.mem s'.mem := by
    rw [m', m₉, m₈, m₇, k₆.2.1, m₅, m₄]
    exact (((((VG.Proof.X25519.X86_64.st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)).trans
      ((VG.Proof.X25519.X86_64.st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((VG.Proof.X25519.X86_64.st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((VG.Proof.X25519.X86_64.st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((VG.Proof.X25519.X86_64.st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)) |>.trans
      ((VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  refine ⟨⟨by rw [g']; exact hs₉.rdi, wr' ▸ hs₉.wr, hn⟩, ?_, fun r hr => ?_, ?_, ?_,
    o₃.trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
  · rw [G _ (by decide), r12₃, G₁ _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [G r (by simp [hr.1, hr.2.2.1]), k₃.1 r (by simp [hr.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      G₁ r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd', rd₉, rd₈, rd₇, k₆.2.2.1, rd₅, rd₄, k₃.2.2.1, rd₂, k₁.2.2.1]
  · rw [wr', wr₉, wr₈, wr₇, k₆.2.2.2, wr₅, wr₄, k₃.2.2.2, wr₂, k₁.2.2.2]
  · have sv : VG.Proof.X25519.X86_64.Saved base s.gpr s₃.mem := by
      rw [k₃.2.1]; intro rd hrd
      rw [sv₂ rd hrd]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
      rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁.1 _ (by decide)
    exact sv.outside o' (by omega)
  · rw [e', e₉, e₈, e₇, k₆.2.1, e₅, e₄]
    simp (config := {decide := true}) only [Function.update_apply, ite_true, ite_false]
    rw [hu s₄ (fun r _ => g₄ r), hu s₃ (fun _ _ => rfl), r₈.1, r₈.2, r₇, rdx₆, rax₆, one, zero]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [m', VG.Proof.X25519.X86_64.word_writeW_self, g₉, r₈.2]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Finish`. -/
section

/-!
# X25519 on x86-64: the last swap and the result
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 32) - BitVec.ofNat 64 a =
    VG.Proof.X25519.X86_64.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : VG.Proof.X25519.X86_64.word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] :
      List Instr)) s fun s' => s'.gpr .rcx = VG.Proof.X25519.X86_64.mask (decide (sw = 1)) ∧ Keeps [.rdx, .rcx] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (VG.Proof.X25519.X86_64.off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load64, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hr, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hw, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X25519.X86_64.mask_of sw hsw, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem lastSwap_eq : lastSwap = ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)] : List Instr) ++ (cswap X2 X3 ++ cswap Z2 Z3) := by
  simp only [lastSwap, List.append_assoc]

/-- The swap after the loop, by the ladder's `swap`. -/
theorem lastSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {st : Spec.X25519.Ladder}
    (hsw : st.swap < 2) (hw : VG.Proof.X25519.X86_64.word s.mem base SWAP = BitVec.ofNat 64 st.swap)
    (h3 : VG.Proof.X25519.X86_64.E s.mem base 3 = st.x2) (h4 : VG.Proof.X25519.X86_64.E s.mem base 4 = st.z2) (h5 : VG.Proof.X25519.X86_64.E s.mem base 5 = st.x3)
    (h6 : VG.Proof.X25519.X86_64.E s.mem base 6 = st.z3) :
    WP isa (.block lastSwap) s fun s' =>
      VG.Proof.X25519.X86_64.Keep base s s' ∧ VG.Proof.X25519.X86_64.E s'.mem base 3 = (Spec.X25519.cswap st.swap st.x2 st.x3).1 ∧
        VG.Proof.X25519.X86_64.E s'.mem base 4 = (Spec.X25519.cswap st.swap st.z2 st.z3).1 := by
  rw [VG.Proof.X25519.X86_64.lastSwap_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.swapMask_ok hs hsw hw) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
  have K₁ : VG.Proof.X25519.X86_64.Keep base s s₁ := ⟨g₁, k₁.2.2.1, k₁.2.2.2, by rw [k₁.2.1]; exact Outside.refl _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.cswapE hs₁ 3 5 (by decide) (by decide) (by decide) m₁)
    fun s₂ ⟨K₂, c₂, e₂⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.cswapE (K₂.scr hs₁) 4 6 (by decide) (by decide) (by decide) (c₂.trans m₁))
    fun s₃ ⟨K₃, _, e₃⟩ => ?_
  refine ⟨(K₁.trans K₂).trans K₃, ?_, ?_⟩
  · rw [e₃, e₂, VG.Proof.X25519.X86_64.cswap_fst, ← h3, ← h5, ← k₁.2.1]
    simp (config := {decide := true}) only [VG.Proof.X25519.X86_64.opSwap, Function.update_apply, ite_true, ite_false]
  · rw [e₃, e₂, VG.Proof.X25519.X86_64.cswap_fst, ← h4, ← h6, ← k₁.2.1]
    simp (config := {decide := true}) only [VG.Proof.X25519.X86_64.opSwap, Function.update_apply, ite_true, ite_false]

/-! ## The result -/

theorem restore_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.X86_64.Scr s base) {g : Reg → BitVec 64}
    (hsv : VG.Proof.X25519.X86_64.Saved base g s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ rd ∈ saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (Spill.restore_ok .rdi saved g s (by decide) (fun p hp => ?_) (by rw [hs.rdi]; exact hsv))
    fun s' ⟨h₁, h₂, hm, hrd, hwr⟩ => ⟨fun rd hrd => h₁ _ (List.mem_map_of_mem hrd), h₂, hm, hrd, hwr⟩
  have := VG.Proof.X25519.X86_64.saved_lt p hp
  rw [hs.rdi]; exact ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X25519.X86_64.contains_sc (by omega)⟩

theorem outStores_ok {s : State} {q : Addr} (hq : s.gpr .rsi = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block ([.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
      .store (at_ .rsi 24) .r11] : List Instr)) s fun s' =>
      s'.mem = VG.Proof.X25519.X86_64.st4 s.mem q 0 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (VG.Proof.X25519.X86_64.off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_at, hq, State.store64,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem bytesAt_st4 (m : Mem) (q : Addr) (w0 w1 w2 w3 : BitVec 64) :
    Spec.X25519.bytesAt (VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3) q 32 = leBytes 32 (val4 w0 w1 w2 w3) := by
  have e : ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (VG.Proof.X25519.X86_64.off q 0) 64).toNat +
      2 ^ 64 * ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).toNat +
      2 ^ 128 * ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).toNat +
      2 ^ 192 * ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).toNat = val4 w0 w1 w2 w3 :=
    VG.Proof.X25519.X86_64.fe_st4 m q (by decide) w0 w1 w2 w3
  rw [show VG.Proof.X25519.X86_64.off q 0 = q from BitVec.add_zero q] at e
  have := ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW q 64).isLt
  have := ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).isLt
  have := ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).isLt
  have := ((VG.Proof.X25519.X86_64.st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).isLt
  exact bytesAt_leBytes_words64 _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem movRsi_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r12)] : List Instr)) s fun s' =>
      s'.gpr .rsi = s.gpr .r12 ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Main`. -/
section

/-!
# X25519 on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.X25519.x25519Contract` it uses, stated for x86-64), and the correctness
of `vg_x25519` against it: every write is in the working space but the
result's, so the arguments are read unchanged, the callee-saved registers
restored from the working space, and the return address kept.
-/

namespace VG.Proof.X25519

open VG VG.X86_64 in
/-- `vg_x25519(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`. -/
def x25519X86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 32⟩
    let scalar : Region := ⟨s.gpr .rsi, 32⟩
    let point : Region := ⟨s.gpr .rdx, 32⟩
    let scratch : Region := ⟨s.gpr .rcx, 4096⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 4096 ≤ 2 ^ 64
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .rdi) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .rsi) 32)
      (Spec.X25519.bytesAt s.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.X25519

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .rdi, 32⟩
abbrev scalarR : Region := ⟨s₀.gpr .rsi, 32⟩
abbrev pointR : Region := ⟨s₀.gpr .rdx, 32⟩
abbrev scR : Region := ⟨s₀.gpr .rcx, 4096⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X25519.X86_64.scalarR s₀, VG.Proof.X25519.X86_64.pointR s₀]
  wr : s₀.wr = [VG.Proof.X25519.X86_64.outR s₀, VG.Proof.X25519.X86_64.scR s₀]
  out_sc : (VG.Proof.X25519.X86_64.outR s₀).Disjoint (VG.Proof.X25519.X86_64.scR s₀)
  scalar_sc : (VG.Proof.X25519.X86_64.scalarR s₀).Disjoint (VG.Proof.X25519.X86_64.scR s₀)
  point_sc : (VG.Proof.X25519.X86_64.pointR s₀).Disjoint (VG.Proof.X25519.X86_64.scR s₀)
  ret_out : (VG.Proof.X25519.X86_64.retR s₀).Disjoint (VG.Proof.X25519.X86_64.outR s₀)
  ret_sc : (VG.Proof.X25519.X86_64.retR s₀).Disjoint (VG.Proof.X25519.X86_64.scR s₀)
  sc_fit : (s₀.gpr .rcx).toNat + 4096 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519X86_64.pre s₀) : VG.Proof.X25519.X86_64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 4096⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 4096 ≤ VG.Proof.X25519.X86_64.ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [VG.Proof.X25519.X86_64.ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base 0 4096 m m')
    (hp : ∀ i < 32, 4096 ≤ VG.Proof.X25519.X86_64.ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X25519.bytesAt m' p 32 = Spec.X25519.bytesAt m p 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base o n m m') (i : Fin 128)
    (hi : 32 * i.val + 32 ≤ o ∨ o + n ≤ 32 * i.val) : VG.Proof.X25519.X86_64.E m' base i = VG.Proof.X25519.X86_64.E m base i := by
  simp only [VG.Proof.X25519.X86_64.E, VG.Proof.X25519.X86_64.F]; rw [h.fe hi (by omega)]

theorem Outside.frame {base : Addr} {m m' : Mem} (h : VG.Proof.X25519.X86_64.Outside base 0 4096 m m') :
    Frame [⟨base, 4096⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 4096 ≤ (x - base).toNat; omega))

variable {fld : Field} (hf : VG.Proof.X25519.X86_64.FieldOk fld)

theorem finish_eq : finish fld = fld.mul X2 X2 T1 ++ (freeze X2 ++ (restore ++
    ([.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
      .store (at_ .rsi 24) .r11] : List Instr))) := by
  simp only [finish, List.append_assoc]

theorem x25519_eq' (lad : Prog isa) : x25519Of fld lad = .seq (.block setup) (.seq bits (.seq
    (.block ([.mov .rsi (.reg .r12)] : List Instr)) (.seq lad (.seq (.block lastSwap)
    (.seq (Impl.X25519.X86_64.invert fld) (.block (finish fld))))))) := rfl

include hf in
/-- X25519 with any ladder `lad` that leaves the ladder's final state as
`ladder` does (`LPost`). -/
theorem correct_of {lad : Prog isa}
    (hlad : ∀ {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}, VG.Proof.X25519.X86_64.LPre base k u s →
      WP isa lad s (VG.Proof.X25519.X86_64.LPost base k u s))
    {s₀ : State} (hp : VG.Proof.X25519.X86_64.Pre s₀) :
    WP isa (x25519Of fld lad) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X25519.x25519X86_64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .rcx = b := ⟨_, rfl⟩
  have hn : base.toNat + 4096 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 4096⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hwo : VG.Proof.X25519.X86_64.outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hr : ∀ d, d + 8 ≤ 32 → InRegions (s₀.rd ++ s₀.wr) (VG.Proof.X25519.X86_64.off (s₀.gpr .rdx) d) 8 := fun d hd =>
    ⟨VG.Proof.X25519.X86_64.pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ hd (by omega)⟩
  rw [VG.Proof.X25519.X86_64.x25519_eq']
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.setup_ok hbase hw₀ hn rfl hr)
    fun s₁ ⟨hs₁, r12₁, g₁, rd₁, wr₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have hkr : ∀ q < 32, InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 q) 1 :=
    fun q hq => ⟨VG.Proof.X25519.X86_64.scalarR s₀, by rw [rd₁, hp.rd]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 32) (by omega) (by omega)⟩
  have hkd : ∀ q < 32, 4096 ≤ VG.Proof.X25519.X86_64.ofs base (s₀.gpr .rsi + BitVec.ofNat 64 q) :=
    fun q hq => VG.Proof.X25519.X86_64.far (hbase ▸ hp.scalar_sc) hq (by decide)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.bits_ok hs₁ (g₁ _ (by decide)) hkr hkd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.movRsi_ok s₂) fun s₃ ⟨rsi₃, k₃⟩ => ?_)
  have hs₃ : VG.Proof.X25519.X86_64.Scr s₃ base :=
    ⟨by rw [k₃.1 _ (by decide), g₂ _ (by decide)]; exact hs₁.rdi,
      by rw [k₃.2.2.2, wr₂]; exact hs₁.wr, hn⟩
  have hkb := VG.Proof.X25519.X86_64.bytesAt_outside o₁ hkd
  have e₃ : ∀ i : Fin 128, i.val < 24 → VG.Proof.X25519.X86_64.E s₃.mem base i = VG.Proof.X25519.X86_64.E s₁.mem base i :=
    fun i h₂ => by rw [k₃.2.1]; exact VG.Proof.X25519.X86_64.E_outside o₂ i (Or.inl (by simp only [BITS]; omega))
  refine WP.seq (WP.mono (hlad (s := s₃)
    (k := Spec.X25519.decodeScalar25519 (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rsi) 32))
    (u := toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rdx) 32)))
    ⟨hs₃, fun t ht => by rw [k₃.2.1, b₂ t ht, hkb],
      by rw [e₃ 2 (by decide), x1₁], by rw [e₃ 3 (by decide), x2₁], by rw [e₃ 4 (by decide), z2₁],
      by rw [e₃ 5 (by decide), x3₁], by rw [e₃ 6 (by decide), z3₁],
      by rw [k₃.2.1, o₂.word (by decide) (by decide), sw₁]⟩) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.lastSwap_ok L.scr
    (by have := ladderAfter_swap_le
          (Spec.X25519.decodeScalar25519 (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rsi) 32))
          (toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rdx) 32)))
          (n := 0) (by omega)
        omega) L.swap L.x2 L.z2 L.x3 L.z3) fun s₅ ⟨K₅, e3₅, e4₅⟩ => ?_)
  have hs₅ := K₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.invert_ok hf hs₅) fun s₆ ⟨g₆, rd₆, wr₆, o₆, e₆⟩ => ?_)
  have hs₆ : VG.Proof.X25519.X86_64.Scr s₆ base := ⟨(g₆ _ (by decide) (by decide)).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  rw [VG.Proof.X25519.X86_64.finish_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulE hf hs₆ 3 3 17 (by decide)) fun s₇ ⟨K₇, e₇⟩ => ?_
  have hs₇ := K₇.scr hs₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.freeze_ok hs₇ (a := X2) (by decide)) fun s₈ ⟨v₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  have sv₈ : VG.Proof.X25519.X86_64.Saved base s₀.gpr s₈.mem := by
    have sv₃ : VG.Proof.X25519.X86_64.Saved base s₀.gpr s₃.mem := by rw [k₃.2.1]; exact sv₁.outside o₂ (by decide)
    rw [k₈.2.1]
    exact (((sv₃.outside L.mem (by decide)).outside K₅.mem (by decide)).outside o₆
      (by decide)).outside K₇.mem (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.restore_ok hs₈ sv₈) fun s₉ ⟨r₉, g₉, m₉, rd₉, wr₉⟩ => ?_
  have rsi₉ : s₉.gpr .rsi = s₀.gpr .rdi := by
    rw [g₉ _ (by decide), k₈.1 _ (by decide), K₇.gpr _ (by decide), g₆ _ (by decide) (by decide),
      K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide), rsi₃, g₂ _ (by decide), r12₁]
  have hwo₉ : VG.Proof.X25519.X86_64.outR s₀ ∈ s₉.wr := by
    rw [wr₉, k₈.2.2.2, K₇.wr, wr₆, K₅.wr, L.wr, k₃.2.2.2, wr₂, wr₁]; exact hwo
  refine WP.mono (VG.Proof.X25519.X86_64.outStores_ok rsi₉ hwo₉) fun s' ⟨m', g', _, _⟩ => ?_
  have O₃ : VG.Proof.X25519.X86_64.Outside base 0 4096 s₀.mem s₃.mem := by
    rw [k₃.2.1]; exact o₁.trans (o₂.mono (by decide) (by decide))
  have O : VG.Proof.X25519.X86_64.Outside base 0 4096 s₀.mem s₉.mem := by
    rw [m₉, k₈.2.1]
    exact (((O₃.trans (L.mem.mono (by decide) (by decide))).trans
      (K₅.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (K₇.mem.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g']
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₉ (.rbx, 0) (by decide)
    · exact r₉ (.rbp, 8) (by decide)
    · rw [g₉ _ (by decide), k₈.1 _ (by decide), K₇.gpr _ (by decide),
        g₆ _ (by decide) (by decide), K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide),
        k₃.1 _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
    · exact r₉ (.r12, 16) (by decide)
    · exact r₉ (.r13, 24) (by decide)
    · exact r₉ (.r14, 32) (by decide)
    · exact r₉ (.r15, 40) (by decide)
  · have F₁ : Frame [VG.Proof.X25519.X86_64.scR s₀, VG.Proof.X25519.X86_64.outR s₀] s₀.mem s'.mem := by
      rw [m']
      have c : ∀ d, d + 8 ≤ 32 → (VG.Proof.X25519.X86_64.outR s₀).Contains (VG.Proof.X25519.X86_64.off (s₀.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hmem : VG.Proof.X25519.X86_64.outR s₀ ∈ [VG.Proof.X25519.X86_64.scR s₀, VG.Proof.X25519.X86_64.outR s₀] := by simp
      exact ((((hbase ▸ O.frame).mono (by simp)).writeW hmem _ (c 0 (by omega))).writeW hmem _
        (c 8 (by omega))).writeW hmem _ (c 16 (by omega)) |>.writeW hmem _ (c 24 (by omega))
    exact F₁.readW (r := VG.Proof.X25519.X86_64.retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_sc
      · exact hp.ret_out) (by decide)
  · show Spec.X25519.bytesAt s'.mem (s₀.gpr .rdi) 32 = _
    rw [m', VG.Proof.X25519.X86_64.bytesAt_st4, x25519_eq]
    dsimp only
    rw [encodeUCoordinate_eq]
    refine congrArg (leBytes 32) ?_
    rw [g₉ .r8 (by decide), g₉ .r9 (by decide), g₉ .r10 (by decide), g₉ .r11 (by decide), v₈,
      ← toFe_val]
    change (VG.Proof.X25519.X86_64.E s₇.mem base 3).val = _
    rw [e₇]
    simp only [VG.Proof.X25519.X86_64.opMul, Function.update_self]
    rw [VG.Proof.X25519.X86_64.E_outside o₆ 3 (by decide), e3₅, e₆, e4₅]

include hf in
theorem correct {s₀ : State} (hp : VG.Proof.X25519.X86_64.Pre s₀) :
    WP isa (x25519With fld) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X25519.x25519X86_64.post s₀ s' :=
  VG.Proof.X25519.X86_64.correct_of hf (fun h => VG.Proof.X25519.X86_64.ladder_post hf h) hp

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Verified`. -/
section

/-!
# X25519 on x86-64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519 s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.X25519.X86_64.correct VG.Proof.X25519.X86_64.baseline_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub
    Impl.X25519.X86_64.x25519 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519 (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.X25519.X86_64.x25519_ok VG.Proof.X25519.X86_64.x25519_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using VG.Proof.X25519.X86_64.satState)

end VG.Proof.X25519.X86_64

end
