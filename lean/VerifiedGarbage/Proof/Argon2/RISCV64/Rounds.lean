module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops

/-! # Argon2 compression on RISC-V: the row and column permutations -/

@[expose] public section

/-! # Argon2's modified addition and GB on RISC-V registers -/

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

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64 VG.Spec.Argon2
open VG.Proof.Argon2
open VG.RISCV64.Wp (Upd)

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (working m p)[i] = word m p i.val := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .a3 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr
  al : p.toNat % 8 = 0

theorem Scratch.al_off {s : State} {p : Addr} (h : Scratch s p) {d : Nat} (hd : d % 8 = 0) :
    (s.gpr .a3 + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [h.reg]; exact Spill.al8 h.al hd

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem lane_injective : Function.Injective lane := by
  intro i j h
  revert i j
  decide

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a4, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4, .t5, .t6]

theorem lane_mem (j : Fin 16) : lane j ∈ roundRegs := by revert j; decide

theorem t5_mem : Reg.t5 ∈ roundRegs := by decide
theorem t6_mem : Reg.t6 ∈ roundRegs := by decide

theorem lane_ne_r6 (j : Fin 16) : lane j ≠ .a3 := by revert j; decide
theorem lane_ne_t5 (j : Fin 16) : lane j ≠ .t5 := by revert j; decide
theorem lane_ne_t6 (j : Fin 16) : lane j ≠ .t6 := by revert j; decide

theorem word_offset (i : Nat) (hi : i < 128) : 1024 + 8 * i < 2048 := by
  omega

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
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Load one word of the permuted block into its register. -/
theorem loadWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [loadWord index j]) s fun t =>
      t = s.write (lane j) (word s.mem p (index j).val) := by
  have ld := hs.read (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at ld
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (word_offset _ (index j).isLt) (hs.al_off (by omega)) ld,
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
      ⟨by rw [u.other _ (lane_ne_r6 j).symm, hs.reg], hs.wr, hs.al⟩
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
  have st := hs.write (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at st
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (word_offset _ (index j).isLt) (hs.al_off (by omega)) st,
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
    have hs1 : Scratch s1 p := by subst h1; exact ⟨hs.reg, hs.wr, hs.al⟩
    refine (ih s1 hs1).mono ?_
    rintro t ⟨hw, hf, hg, hr, hwr, hsp⟩
    subst h1
    refine ⟨?_, ?_, hg, hr, hwr, hsp⟩
    · rw [hw, List.foldl_cons, working_write]
    · exact ((Frame.refl [⟨off p 1024, 1024⟩] s.mem).writeW (by simp) _
        (Offset.contains p (d := 1024 + 8 * (index j).val) (n := 8) (e := 1024) (k := 1024)
          (by omega) (by omega) (by omega))).trans hf

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
  ⟨(hk.1 .a3 (by decide)).trans hs.reg, hk.2.2.1 ▸ hs.wr, hs.al⟩

/-- One GB on registers advances the row or column. -/
theorem gbOn_ok (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa (gbOn a b c d) s fun t =>
      InRegs t (GB v a b c d) ∧ Keeps s t ∧ t.mem = s.mem := by
  have ne {i j : Fin 16} (h : i.val ≠ j.val) : lane i ≠ lane j :=
    fun e => h (congrArg Fin.val (lane_injective e))
  have dist : Distinct (lane a) (lane b) (lane c) (lane d) .t5 .t6 :=
    ⟨ne hab, ne hac, ne had, lane_ne_t5 a, lane_ne_t6 a, ne hbc, ne hbd, lane_ne_t5 b,
      lane_ne_t6 b, ne hcd, lane_ne_t5 c, lane_ne_t6 c, lane_ne_t5 d, lane_ne_t6 d, by decide⟩
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
        lane_ne_t5 j, lane_ne_t6 j⟩), hv j, Fin.getElem_fin]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [lane_mem a, lane_mem b, lane_mem c, lane_mem d, t5_mem, t6_mem]

/-- P on the sixteen registers. -/
theorem permute_ok (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa Impl.Argon2.RISCV64.permute s fun t =>
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
  unfold Impl.Argon2.RISCV64.permute
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
    WP isa (Impl.Argon2.RISCV64.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  unfold Impl.Argon2.RISCV64.permuteAt
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
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.RISCV64.permuteAt (index i)) rest)
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

end VG.Proof.Argon2.RISCV64
