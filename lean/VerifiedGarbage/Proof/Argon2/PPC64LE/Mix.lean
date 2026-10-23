module

public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Compress
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.MdStream.Spec

/-! # Argon2's modified addition and GB on PPC64LE registers -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd WP.cons wp_add)

theorem rotateRight_zero (x : BitVec 32) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight_def]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lo {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& 0xffffffff) → WP isa (.block is) s' Q) :
    WP isa (.block (.rotr .w d n 0 :: is)) s Q := by
  refine WP.cons (exec_rotr_w (by decide)) ?_
  have e : (((s.gpr n).setWidth 32).rotateRight 0).setWidth 64 = s.gpr n &&& 0xffffffff := by
    rw [rotateRight_zero, BitVec.setWidth_eq_append (by decide)]
    exact (BitVec.and_setWidth_allOnes 32 32 _).symm
  rw [e]
  exact k _ (Upd.write _ _ _)

theorem wp_rotr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).rotateRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.rotr .d d n sh :: is)) s Q :=
  WP.cons (exec_rotr_d h) (k _ (Upd.write _ _ _))

end

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

/-- The effect of a block on registers: `d` gets `v`, and every register
outside `ws` keeps its value. -/
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
  refine wp_lo fun s₁ u₁ => wp_lo fun s₂ u₂ => wp_mul fun s₃ u₃ => wp_add fun s₄ u₄ =>
    wp_add fun s₅ u₅ => wp_add fun s₆ u₆ => k s₆ ?_ ?_
  · rw [u₆.gpr, u₅.gpr, u₅.other t hat.symm, u₄.gpr, u₄.other t hat.symm, u₃.other a hat,
      u₃.other b hbt, u₃.gpr, u₂.other a hau, u₂.other b hbu, u₂.other t htu, u₂.gpr,
      u₁.other a hat, u₁.other b hbt, u₁.gpr]
    exact addMul_value _ _
  · exact (((((Eff.of_upd u₁ (by simp)).trans (.of_upd u₂ (by simp))).trans (.of_upd u₃ (by simp))).trans
      (.of_upd u₄ (by simp))).trans (.of_upd u₅ (by simp))).trans (.of_upd u₆ (by simp))

/-- A register XOR followed by one of GB's rotations. -/
theorem xorRotate_ok {a d : Reg} {n : Nat} (hn : n < 64) (s : State) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s', s'.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n → Eff s s' [d] →
      WP isa (.block is) s' Q) :
    WP isa (.block (([.logic .xor d d a, .rotr .d d d n] : List Instr) ++ is)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine wp_xor fun s₁ u₁ => wp_rotr hn fun s₂ u₂ => k s₂ ?_ ?_
  · rw [u₂.gpr, u₁.gpr]
  · exact (Eff.of_upd u₁ (by simp)).trans (.of_upd u₂ (by simp))

/-- One half of GB. -/
theorem halfGB_ok {a b c d t u : Reg} (h : Distinct a b c d t u) {r1 r2 : Nat}
    (h1 : r1 < 64) (h2 : r2 < 64) (s : State) {is : List Instr} {Q : State → Prop}
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
  refine xorRotate_ok (a := a) (d := d) h1 s₁ fun s₂ hd e₂ => ?_
  refine addMul_ok h.c_t h.cu h.d_t h.du h.tu s₂ fun s₃ hc e₃ => ?_
  refine xorRotate_ok (a := c) (d := b) h2 s₃ fun s₄ hb e₄ => ?_
  have m : ∀ r, r ∉ [a, b, c, d, t, u] → r ∉ [a, t, u] ∧ r ∉ [d] ∧ r ∉ [c, t, u] ∧ r ∉ [b] :=
    fun r hr => ⟨fun h' => hr ((by simp : [a, t, u] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [d] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [c, t, u] ⊆ [a, b, c, d, t, u]) h'),
      fun h' => hr ((by simp : [b] ⊆ [a, b, c, d, t, u]) h')⟩
  have hd' : s₂.gpr d = (s.gpr d ^^^ Spec.Argon2.addMul (s.gpr a) (s.gpr b)).rotateRight r1 := by
    rw [hd, ha, e₁.other d (by simp [h.ad.symm, h.d_t, h.du])]
  have hc' : s₃.gpr c = Spec.Argon2.addMul (s.gpr c) (s₂.gpr d) := by
    rw [hc, e₂.other c (by simp [h.cd]), e₁.other c (by simp [h.ac.symm, h.c_t, h.cu])]
  refine k s₄ ?_ ?_ ?_ ?_ ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₄.other a (by simp [h.ab]), e₃.other a (by simp [h.ac, h.a_t, h.au]),
      e₂.other a (by simp [h.ad]), ha]
  · rw [hb, hc', hd', e₃.other b (by simp [h.bc, h.b_t, h.bu]), e₂.other b (by simp [h.bd]),
      e₁.other b (by simp [h.ab.symm, h.b_t, h.bu])]
  · rw [e₄.other c (by simp [h.bc.symm]), hc', hd']
  · rw [e₄.other d (by simp [h.bd.symm]), e₃.other d (by simp [h.cd.symm, h.d_t, h.du]), hd']
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
  refine halfGB_ok h (by decide) (by decide) s fun s₁ ha hb hc hd e₁ => ?_
  refine halfGB_ok h (by decide) (by decide) s₁ fun s₂ ha' hb' hc' hd' e₂ => ?_
  refine k s₂ ?_ ?_ ?_ ?_ (e₁.trans e₂)
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl

end VG.Proof.Argon2.PPC64LE
