module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Compress
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Argon2.PPC64LE.Rounds`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Mix`, which only this module used -/

section

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

end

end


/-! # Argon2 compression on PPC64LE: the row and column permutations -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.MdStream.PPC64LE (Upd)

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (working m p)[i] = word m p i.val := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .r6 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega_using [hd])⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega_using [hd])⟩

theorem lane_injective : Function.Injective lane := by
  intro i j h
  revert i j
  decide

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg :=
  [.r3, .r4, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21,
    .r0, .r22]

theorem lane_mem (j : Fin 16) : lane j ∈ roundRegs := by revert j; decide

theorem r0_mem : Reg.r0 ∈ roundRegs := by decide
theorem r22_mem : Reg.r22 ∈ roundRegs := by decide

theorem lane_ne_r6 (j : Fin 16) : lane j ≠ .r6 := by revert j; decide
theorem lane_ne_r0 (j : Fin 16) : lane j ≠ .r0 := by revert j; decide
theorem lane_ne_r22 (j : Fin 16) : lane j ≠ .r22 := by revert j; decide

theorem word_offset (i : Nat) (hi : i < 128) : 1024 + 8 * i < 2 ^ 15 ∧ (1024 + 8 * i) % 4 = 0 := by
  omega_using [hi]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    working (m.writeW (off p (1024 + 8 * i.val)) v) p = (working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega_using [h]) (by omega_using [hj]) (by omega_using [])) (by decide)

/-- Load one word of the permuted block into its register. -/
theorem loadWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [loadWord index j]) s fun t =>
      t = s.write (lane j) (word s.mem p (index j).val) := by
  have ld := hs.read (d := 1024 + 8 * (index j).val) (n := 8) (by omega_using [])
  rw [← hs.reg] at ld
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) (word_offset _ (index j).isLt) ld,
    WP.block_nil ?_⟩
  rw [hs.reg]

/-- Load the words `js` of a row or column, each into its own register. -/
theorem loads_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (hn : js.Nodup)
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (.block (js.map (loadWord index))) s fun t =>
      (∀ j ∈ js, t.gpr (lane j) = word s.mem p (index j).val) ∧
      (∀ r, (∀ j ∈ js, lane j ≠ r) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction js generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    obtain ⟨hj, hn'⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (loadWord_ok index j s hs).mono ?_
    rintro s1 rfl
    have u := Upd.write s (lane j) (word s.mem p (index j).val)
    have hs1 : Scratch (s.write (lane j) (word s.mem p (index j).val)) p :=
      ⟨by rw [u.other _ (lane_ne_r6 j).symm, hs.reg], hs.wr⟩
    refine (ih hn' _ hs1).mono ?_
    rintro t ⟨hl, hk, hm, hr, hw, hsp⟩
    refine ⟨?_, ?_, hm, hr, hw, hsp⟩
    · intro k hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hk _ (fun i hi he => hj (by rw [← lane_injective he]; exact hi)), u.gpr]
      · exact hl k hk'
    · intro r hr
      rw [hk r (fun i hi => hr i (List.mem_cons_of_mem _ hi)),
        u.other _ (fun he => hr j (List.mem_cons_self ..) he.symm)]

/-- Store one register into its word of the permuted block. -/
theorem storeWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [storeWord index j]) s fun t =>
      t = { s with mem := s.mem.writeW (off p (1024 + 8 * (index j).val)) (s.gpr (lane j)) } := by
  have st := hs.write (d := 1024 + 8 * (index j).val) (n := 8) (by omega_using [])
  rw [← hs.reg] at st
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (by decide) (word_offset _ (index j).isLt) st,
    WP.block_nil ?_⟩
  rw [hs.reg]

/-- Store the registers of the words `js` of a row or column, in order. -/
theorem stores_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block (js.map (storeWord index))) s fun t =>
      working t.mem p =
        js.foldl (fun b j => b.set (index j) (s.gpr (lane j))) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (storeWord_ok index j s hs).mono ?_
    intro s1 h1
    have hs1 : Scratch s1 p := by subst h1; exact ⟨hs.reg, hs.wr⟩
    refine (ih s1 hs1).mono ?_
    rintro t ⟨hw, hf, hg, hr, hwr, hsp⟩
    subst h1
    refine ⟨?_, ?_, hg, hr, hwr, hsp⟩
    · rw [hw, List.foldl_cons, working_write]
    · exact ((Frame.refl [⟨off p 1024, 1024⟩] s.mem).writeW (by simp) _
        (Offset.contains p (d := 1024 + 8 * (index j).val) (n := 8) (e := 1024) (k := 1024)
          (by omega_using []) (by omega_using []) (by omega_using []))).trans hf

/-- The sixteen words of a row or column, in their registers. -/
def InRegs (s : State) (v : Vector Word 16) : Prop := ∀ j : Fin 16, s.gpr (lane j) = v[j]

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ∉ roundRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr),
    h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : Scratch s p)
    (hk : Keeps s t) : Scratch t p :=
  ⟨(hk.1 .r6 (by decide)).trans hs.reg, hk.2.2.1 ▸ hs.wr⟩

/-- One GB on registers advances the row or column. -/
theorem gbOn_ok (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa (gbOn a b c d) s fun t =>
      InRegs t (GB v a b c d) ∧ Keeps s t ∧ t.mem = s.mem := by
  have ne {i j : Fin 16} (h : i.val ≠ j.val) : lane i ≠ lane j :=
    fun e => h (congrArg Fin.val (lane_injective e))
  have dist : Distinct (lane a) (lane b) (lane c) (lane d) .r0 .r22 :=
    ⟨ne hab, ne hac, ne had, lane_ne_r0 a, lane_ne_r22 a, ne hbc, ne hbd, lane_ne_r0 b,
      lane_ne_r22 b, ne hcd, lane_ne_r0 c, lane_ne_r22 c, lane_ne_r0 d, lane_ne_r22 d, by decide⟩
  unfold gbOn
  rw [← List.append_nil (gb _ _ _ _ _ _)]
  refine gb_ok dist s fun t ha hb hc hd e => WP.block_nil ?_
  refine ⟨?_, ⟨fun r hr => e.other r fun h => hr ?_, e.rd, e.wr, e.sp⟩, e.mem⟩
  · intro j
    rw [GB_eq_mixWords v hab hac had hbc hbd hcd]
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ← hv a, ← hv b, ← hv c, ← hv d]
    by_cases hdj : d.val = j.val
    · obtain rfl := Fin.ext hdj
      simpa only [↓reduceIte] using hd
    simp only [hdj, ite_false]
    by_cases hcj : c.val = j.val
    · obtain rfl := Fin.ext hcj
      simpa only [↓reduceIte] using hc
    simp only [hcj, ite_false]
    by_cases hbj : b.val = j.val
    · obtain rfl := Fin.ext hbj
      simpa only [↓reduceIte] using hb
    simp only [hbj, ite_false]
    by_cases haj : a.val = j.val
    · obtain rfl := Fin.ext haj
      simpa only [↓reduceIte] using ha
    simp only [haj, ite_false]
    rw [e.other _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨ne (Ne.symm haj), ne (Ne.symm hbj), ne (Ne.symm hcj), ne (Ne.symm hdj),
        lane_ne_r0 j, lane_ne_r22 j⟩), hv j, Fin.getElem_fin]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [lane_mem a, lane_mem b, lane_mem c, lane_mem d, r0_mem, r22_mem]

/-- P on the sixteen registers. -/
theorem permute_ok (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa Impl.Argon2.PPC64LE.permute s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
  have advance (t : State) (v' : Vector Word 16)
      (h : InRegs t v' ∧ Keeps s t ∧ t.mem = s.mem) (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (gbOn a b c d) t fun u =>
        InRegs u (GB v' a b c d) ∧ Keeps s u ∧ u.mem = s.mem := by
    refine (gbOn_ok a b c d hab hac had hbc hbd hcd t v' h.1).mono ?_
    rintro u ⟨hu, hk, hm⟩
    exact ⟨hu, h.2.1.trans hk, hm.trans h.2.2⟩
  unfold Impl.Argon2.PPC64LE.permute
  apply WP.seq
  refine (advance s _ ⟨hv, Keeps.refl s, rfl⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (Impl.Argon2.PPC64LE.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  unfold Impl.Argon2.PPC64LE.permuteAt
  apply WP.seq
  refine (loads_ok index (List.finRange 16) (List.nodup_finRange 16) s hs).mono ?_
  rintro s1 ⟨hl, hk1, hm1, hr1, hw1, hsp1⟩
  have k1 : Keeps s s1 := ⟨fun r hr => hk1 r (fun j _ he => hr (he ▸ lane_mem j)), hr1, hw1, hsp1⟩
  have in1 : InRegs s1 (gather index (working s.mem p)) := by
    intro j
    rw [hl j (List.mem_finRange j)]
    simp only [gather, working, Fin.getElem_fin, Vector.getElem_ofFn]
  apply WP.seq
  refine (permute_ok s1 _ in1).mono ?_
  rintro s2 ⟨in2, k2, hm2⟩
  refine (stores_ok index (List.finRange 16) s2 ((hs.of_keeps k1).of_keeps k2)).mono ?_
  rintro t ⟨hw, hf, hg, hr, hwr, hsp⟩
  refine ⟨?_, ?_, (k1.trans k2).trans ⟨fun r _ => congrFun hg r, hr, hwr, hsp⟩⟩
  · rw [hw, hm2, hm1]
    simp only [in2 _]
    rfl
  · rw [hm2, hm1] at hf
    exact hf

/-- Compose a list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.PPC64LE.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok (index i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.PPC64LE

end

end

/-! # Argon2 compression on PPC64LE: the initial and final XORs -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE VG.Spec.Argon2
open VG.Proof.MdStream.PPC64LE (Upd)

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- The copying blocks change only `r0`, `r22` and memory. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .r0 → r ≠ .r22 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (h' : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h0 h22 => (h'.1 r h0 h22).trans (h.1 r h0 h22), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : Scratch s p) (h : CopyKeeps s t) :
    Scratch t p := ⟨(h.1 .r6 (by decide) (by decide)).trans hs.reg, h.2.2.1 ▸ hs.wr⟩

theorem off8 (i : Nat) (hi : i < 128) : 8 * i < 2 ^ 15 ∧ (8 * i) % 4 = 0 := by omega_arith

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .r3) (8 * i)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .r4) (8 * i)) 8) :
    let a := s.mem.readW (off (s.gpr .r3) (8 * i)) 64 ^^^ s.mem.readW (off (s.gpr .r4) (8 * i)) 64
    WP isa (.block (initWord i)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i)) a).writeW (off p (1024 + 8 * i)) a ∧
      CopyKeeps s t := by
  dsimp only
  have w1 := hs.write (d := 8 * i) (n := 8) (by omega_arith)
  have w2 := hs.write (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at w1 w2
  unfold initWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) (off8 i hi) hx, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) (off8 i hi) hy, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (by decide) (off8 i hi) w1, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (by decide) (word_offset i hi) w2, ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hout : InRegions s.wr (off (s.gpr .r5) (8 * i)) 8) :
    WP isa (.block (finishWord i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .r5) (8 * i))
          (word s.mem p i ^^^ s.mem.readW (off p (8 * i)) 64) ∧
      CopyKeeps s t := by
  have r1 := hs.read (d := 8 * i) (n := 8) (by omega_arith)
  have r2 := hs.read (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at r1 r2
  unfold finishWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) (word_offset i hi) r2, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) (off8 i hi) r1, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (by decide) (off8 i hi) (by simpa [State.write] using hout), ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .r3 = x
  yreg : s.gpr .r4 = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : CopyKeeps s t) :
    Inputs t x y p := ⟨(hk.1 .r3 (by decide) (by decide)).trans h.xreg,
      (hk.1 .r4 (by decide) (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2.1] using h.xread,
      by simpa only [hk.2.1, hk.2.2.1] using h.yread, h.xsep, h.ysep⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} {n : Nat} (hf : Frame [⟨p, n⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, n⟩) (i : Fin 128) :
    m'.readW (off x (8 * i.val)) 64 = m.readW (off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega_arith) (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Initialized m p r n) :
    Initialized ((m.writeW (off p (8 * n)) r[n]).writeW (off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  obtain ⟨k, hk⟩ := i
  simp only at hi
  simp only [word]
  rcases (by omega_arith : k = n ∨ k < n) with rfl | he
  · refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
    rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
    rfl
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h ⟨k, hk⟩ he

/-- Initialize a prefix of the words, framing the first half of scratch. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : Scratch s p) (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initWord)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 2048⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (off (t.gpr .r3) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact ⟨_, htIn.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
    have ly : InRegions (t.rd ++ t.wr) (off (t.gpr .r4) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact ⟨_, htIn.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
    refine (initWord_ok t (hs.of_copy hk) n hn' lx ly).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : t.mem.readW (off x (8 * n)) 64 ^^^ t.mem.readW (off y (8 * n)) 64 =
        (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] := by
      rw [show (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] =
          (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, blockAt_get, blockAt_get,
        input_unchanged hf (hin.xsep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩,
        input_unchanged hf (hin.ysep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact initialized_step hn' ht
    · rw [hm]
      exact (hf.writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 128) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← working_get m p ⟨i, hi⟩] at he
    exact he

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Written m out r n) :
    Written (m.writeW (off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h i (by omega_arith)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (off p d) 64 = m.readW (off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish a prefix of the words. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .r5 = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap finishWord)) s fun t =>
      Written t.mem out (xorBlock (working s.mem p) (blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have ho' : t.gpr .r5 = out := (hk.1 .r5 (by decide) (by decide)).trans ho
    have hout : InRegions t.wr (off (t.gpr .r5) (8 * n)) 8 := by
      rw [ho', hk.2.2.1]
      exact ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
    refine (finishWord_ok t (hs.of_copy hk) n hn' hout).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : word t.mem p n ^^^ t.mem.readW (off p (8 * n)) 64 =
        (xorBlock (working s.mem p) (blockAt s.mem p))[n] := by
      rw [show (xorBlock (working s.mem p) (blockAt s.mem p))[n] =
          (xorBlock (working s.mem p) (blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, working_get, blockAt_get]
      simp only [word, scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega_arith),
        scratch_unchanged hf hd (d := 8 * n) (by omega_arith)]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, ho', hv]
      exact written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _ (Offset.contains_base out (by omega_arith) (by omega_arith))

theorem written_block {m : Mem} {out : Addr} {r : Block} (h : Written m out r 128) :
    blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.PPC64LE
