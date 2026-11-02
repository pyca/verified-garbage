module

public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-! # Argon2's modified addition and GB on RISC-V registers -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64
open VG.RISCV64.Wp (Upd WP.cons wp_add wp_xor)

theorem shr_or_shl (x : BitVec 64) {r : Nat} (hr : r < 64) :
    x >>> r ||| x <<< (64 - r) = x.rotateRight r := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hr]

theorem toNat_shl32 (a : BitVec 64) : (a <<< 32).toNat = a.toNat % 2 ^ 32 * 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := a.isLt
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by rw [← Nat.pow_add], Nat.mul_mod_mul_right]

theorem toNat_lo32 (a : BitVec 64) : (a &&& 0xffffffff).toNat = a.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `mulhu` of the two low halves shifted up by 32 bits is their product. -/
theorem lo_mul (a b : BitVec 64) :
    BitVec.ofNat 64 ((a <<< 32).toNat * (b <<< 32).toNat / 2 ^ 64) =
      (a &&& 0xffffffff) * (b &&& 0xffffffff) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_mul, toNat_shl32, toNat_shl32, toNat_lo32, toNat_lo32]
  have e : a.toNat % 2 ^ 32 * 2 ^ 32 * (b.toNat % 2 ^ 32 * 2 ^ 32) =
      a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) * 2 ^ 64 := by
    rw [Nat.mul_mul_mul_comm, ← Nat.pow_add]
  rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos 64)]

theorem addMul_value (a b : BitVec 64) :
    a + b + (a &&& 0xffffffff) * (b &&& 0xffffffff) + (a &&& 0xffffffff) * (b &&& 0xffffffff) =
      Spec.Argon2.addMul a b := by
  rw [Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = p
  grind

/-- GB's four registers and its two temporaries are distinct. -/
structure Distinct (a b c d t u : Reg) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  ad : a ≠ d
  a_t : a ≠ t
  au : a ≠ u
  bc : b ≠ c
  bd : b ≠ d
  b_t : b ≠ t
  bu : b ≠ u
  cd : c ≠ d
  c_t : c ≠ t
  cu : c ≠ u
  d_t : d ≠ t
  du : d ≠ u
  tu : t ≠ u

/-- The effect of a block on registers: every register outside `ws` keeps its
value. -/
structure Eff (s s' : State) (ws : List Reg) : Prop where
  other : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Eff.of_upd {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Eff s s' ws :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.mem, h.rd, h.wr, h.sp⟩

theorem Eff.trans {s s' s'' : State} {ws : List Reg} (h : Eff s s' ws) (h' : Eff s' s'' ws) :
    Eff s s'' ws :=
  ⟨fun r hr => (h'.other r hr).trans (h.other r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Eff.refl (s : State) (ws : List Reg) : Eff s s ws := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Eff.mono {s s' : State} {ws ws' : List Reg} (h : Eff s s' ws) (hw : ∀ r ∈ ws, r ∈ ws') :
    Eff s s' ws' :=
  ⟨fun r hr => h.other r fun h' => hr (hw r h'), h.mem, h.rd, h.wr, h.sp⟩

theorem addMul_ok {a b t u : Reg} (hat : a ≠ t) (hau : a ≠ u) (hbt : b ≠ t) (hbu : b ≠ u)
    (htu : t ≠ u) (s : State) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) → Eff s s' [a, t, u] →
      WP isa (.block is) s' Q) :
    WP isa (.block (addMul a b t u ++ is)) s Q := by
  simp only [addMul, List.cons_append, List.nil_append]
  refine wp_sll (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_mulhu fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_add fun s₆ u₆ => k s₆ ?_ ?_
  · rw [u₆.gpr, u₅.gpr, u₅.other t hat.symm, u₄.gpr, u₄.other t hat.symm, u₃.other a hat,
      u₃.other b hbt, u₃.gpr, u₂.other a hau, u₂.other b hbu, u₂.other t htu, u₂.gpr,
      u₁.other a hat, u₁.other b hbt, u₁.gpr, lo_mul]
    exact addMul_value _ _
  · exact (((((Eff.of_upd u₁ (by simp)).trans (.of_upd u₂ (by simp))).trans (.of_upd u₃ (by simp))).trans
      (.of_upd u₄ (by simp))).trans (.of_upd u₅ (by simp))).trans (.of_upd u₆ (by simp))

/-- A register XOR followed by one of GB's rotations, through `t`. -/
theorem xorRotate_ok {a d t : Reg} (hdt : d ≠ t) {n : Nat} (h0 : 0 < n) (hn : n < 64) (s : State)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n → Eff s s' [d, t] →
      WP isa (.block is) s' Q) :
    WP isa (.block ((.logic .xor d d a :: rot d t n) ++ is)) s Q := by
  simp only [rot, List.cons_append, List.nil_append]
  refine wp_xor fun s₁ u₁ => wp_srl hn fun s₂ u₂ => wp_sll (by omega) fun s₃ u₃ =>
    wp_or fun s₄ u₄ => k s₄ ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₃.other t hdt.symm, u₂.gpr, u₂.other d hdt, u₁.gpr, BitVec.or_comm]
    exact shr_or_shl _ hn
  · exact (((Eff.of_upd u₁ (by simp)).trans (.of_upd u₂ (by simp))).trans (.of_upd u₃ (by simp))).trans
      (.of_upd u₄ (by simp))

/-- One half of GB. -/
theorem halfGB_ok {a b c d t u : Reg} (h : Distinct a b c d t u) {r1 r2 : Nat}
    (h01 : 0 < r1) (h1 : r1 < 64) (h02 : 0 < r2) (h2 : r2 < 64) (s : State) {is : List Instr} {Q : State → Prop}
    (k : ∀ s',
      let va := Spec.Argon2.addMul (s.gpr a) (s.gpr b)
      let vd := (s.gpr d ^^^ va).rotateRight r1
      let vc := Spec.Argon2.addMul (s.gpr c) vd
      let vb := (s.gpr b ^^^ vc).rotateRight r2
      s'.gpr a = va → s'.gpr b = vb → s'.gpr c = vc → s'.gpr d = vd → Eff s s' [a, b, c, d, t, u] →
      WP isa (.block is) s' Q) :
    WP isa (.block (halfGB a b c d t u r1 r2 ++ is)) s Q := by
  simp only [halfGB, List.append_assoc]
  refine addMul_ok h.a_t h.au h.b_t h.bu h.tu s fun s₁ ha e₁ => ?_
  refine xorRotate_ok (a := a) (d := d) (t := t) h.d_t h01 h1 s₁ fun s₂ hd e₂ => ?_
  refine addMul_ok h.c_t h.cu h.d_t h.du h.tu s₂ fun s₃ hc e₃ => ?_
  refine xorRotate_ok (a := c) (d := b) (t := t) h.b_t h02 h2 s₃ fun s₄ hb e₄ => ?_
  have m : ∀ r, r ∉ [a, b, c, d, t, u] → r ∉ [a, t, u] ∧ r ∉ [d, t] ∧ r ∉ [c, t, u] ∧ r ∉ [b, t] :=
    fun r hr => ⟨fun h' => hr ((by simp : [a, t, u] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [d, t] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [c, t, u] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [b, t] ⊆ [a, b, c, d, t, u]) h')⟩
  have hd' : s₂.gpr d = (s.gpr d ^^^ Spec.Argon2.addMul (s.gpr a) (s.gpr b)).rotateRight r1 := by
    rw [hd, ha, e₁.other d (by simp [h.ad.symm, h.d_t, h.du])]
  have hc' : s₃.gpr c = Spec.Argon2.addMul (s.gpr c) (s₂.gpr d) := by
    rw [hc, e₂.other c (by simp [h.cd, h.c_t]), e₁.other c (by simp [h.ac.symm, h.c_t, h.cu])]
  refine k s₄ ?_ ?_ ?_ ?_ ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₄.other a (by simp [h.ab, h.a_t]), e₃.other a (by simp [h.ac, h.a_t, h.au]),
      e₂.other a (by simp [h.ad, h.a_t]), ha]
  · rw [hb, hc', hd', e₃.other b (by simp [h.bc, h.b_t, h.bu]), e₂.other b (by simp [h.bd, h.b_t]),
      e₁.other b (by simp [h.ab.symm, h.b_t, h.bu])]
  · rw [e₄.other c (by simp [h.bc.symm, h.c_t]), hc', hd']
  · rw [e₄.other d (by simp [h.bd.symm, h.d_t]), e₃.other d (by simp [h.cd.symm, h.d_t, h.du]), hd']
  · obtain ⟨m1, m2, m3, m4⟩ := m r hr
    rw [e₄.other r m4, e₃.other r m3, e₂.other r m2, e₁.other r m1]
  · rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  · rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd]
  · rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]
  · rw [e₄.sp, e₃.sp, e₂.sp, e₁.sp]

/-- The complete GB operation agrees with the four-word specification. -/
theorem gb_ok {a b c d t u : Reg} (h : Distinct a b c d t u) (s : State) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s',
      let v := Proof.Argon2.mix (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d)
      s'.gpr a = v.1 → s'.gpr b = v.2.1 → s'.gpr c = v.2.2.1 → s'.gpr d = v.2.2.2 →
      Eff s s' [a, b, c, d, t, u] → WP isa (.block is) s' Q) :
    WP isa (.block (gb a b c d t u ++ is)) s Q := by
  rw [gb, List.append_assoc]
  refine halfGB_ok h (by decide) (by decide) (by decide) (by decide) s fun s₁ ha hb hc hd e₁ => ?_
  refine halfGB_ok h (by decide) (by decide) (by decide) (by decide) s₁ fun s₂ ha' hb' hc' hd' e₂ => ?_
  refine k s₂ ?_ ?_ ?_ ?_ (e₁.trans e₂)
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl

end VG.Proof.Argon2.RISCV64
