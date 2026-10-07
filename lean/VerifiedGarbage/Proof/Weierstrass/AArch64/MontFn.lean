import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Montgomery products modulo a curve's `p` or `n`, as functions, on AArch64

`mulFn n m` (`Impl/Weierstrass/AArch64/Mont.lean`), from a state `Pre n m`
(`ws` in `x0` and the offsets in `w1`–`w3`, the working space the only
region, the numbers below the function's own working space), runs the entry
(`entry_ok`): the offsets zero-extended, the callee-saved registers saved in
vector lanes, the pointers to the numbers (`Ptr`, `PtrW`) and the modulus
stored (`ModOkW`); then the product (`mulR_okW`) and the registers restored
(`mulFn_ok`). The function keeps the callee-saved registers, `x30`, `sp` and
the low halves of `v8`–`v15` (`abiPreserved`), changes the memory only at
`[o]` and at the modulus (`Kept`), and leaves `x0 = ws`, `x19` and `x20`.
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- An offset argument: the low 32 bits of its register. -/
abbrev arg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- The function's own working space. -/
abbrev own (n : Nat) : Nat := Spec.Weierstrass.Mont.ownAt n

/-- What the function needs of the modulus `m` of `n` words: four, six or
nine words, `m` below `2^(64 n)`, `minv m` its inverse's negation, and what
the multiplication needs of it; and that its code writes no vector register. -/
structure ModOk (n m : Nat) : Prop where
  hn : n = 4 ∨ n = 6 ∨ n = 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true
  novec : ∀ i ∈ mulR (mod n m) (ptrs n).1 (ptrs n).2.1 (ptrs n).2.2 0 0 0 ++ setConst n (moAt n) m,
    vdstOf i = none

/-- The precondition, on the registers. -/
structure Pre (n W : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨s.gpr .x0, W⟩]
  fit : (s.gpr .x0).toNat + W ≤ 2 ^ 64
  w : moAt n + 8 * n ≤ W
  w8 : W ≤ 8192
  o : arg s .x1 + 8 * n ≤ own n
  a : arg s .x2 + 8 * n ≤ own n
  b : arg s .x3 + 8 * n ≤ own n

/-- The memory changes only at `[o]` and at the modulus. -/
def Kept (n : Nat) (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + 8 * n ≤ ofs base x) →
    (ofs base x < moAt n ∨ moAt n + 8 * n ≤ ofs base x) → m' x = m x

theorem own_eq {n : Nat} (h : n ≤ 9) : own n + 64 * n = 4096 := by
  simp only [own, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega

theorem ModOk.n9 {n m : Nat} (h : ModOk n m) : n ≤ 9 := by rcases h.hn with h | h | h <;> omega
theorem ModOk.n4 {n m : Nat} (h : ModOk n m) : 4 ≤ n := by rcases h.hn with h | h | h <;> omega

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-! ## Facts of the registers, for each number of words -/

theorem regs_facts : ∀ n, (n = 4 ∨ n = 6 ∨ n = 9) →
    PtrOk n (ptrs n).1 ∧ PtrOk n (ptrs n).2.1 ∧ (ptrs n).2.2 ∉ clob n ∧
    (saved n).length ≤ 8 ∧ (saved n).Nodup ∧
    (∀ r ∈ preserved, r ∉ saved n → r ∉ clob n ∧ r ∉ [Reg.x1, .x2, .x3] ∧
      r ∉ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2]) ∧
    (∀ r ∈ saved n, r ∈ preserved) ∧
    (ptrs n).1 ∉ [Reg.x0, .x1, .x2, .x3] ∧ (ptrs n).2.1 ∉ [Reg.x0, .x1, .x2, .x3] ∧
    (ptrs n).2.2 ∉ [Reg.x0, .x1, .x2, .x3] ∧
    [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2].Nodup ∧
    (∀ r ∈ [Reg.x0, .x19, .x20], r ∉ clob n ∧ r ∉ saved n ∧ r ∉ [Reg.x1, .x2, .x3] ∧
      r ∉ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2]) := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;>
    refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩ <;> decide

/-! ## Words through pointers -/

theorem off_off (p : Addr) (e d : Nat) : off (off p e) d = off p (e + d) :=
  VG.Offset.add_ofNat_add_ofNat p e d

theorem wordsVal_off (m : Mem) (p : Addr) (e : Nat) : ∀ d k, wordsVal m (off p e) d k = wordsVal m p (e + d) k
  | _, 0 => rfl
  | d, k + 1 => by
    simp only [wordsVal, word, off_off, wordsVal_off m p e (d + 8) k, Nat.add_assoc]

theorem ofs_off_sub (p x : Addr) (e : Nat) (he : e < 2 ^ 64) :
    ofs (off p e) x = (2 ^ 64 - e + ofs p x) % 2 ^ 64 := by
  simp only [ofs, off]
  rw [VG.Offset.sub_add_eq, VG.Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt he]

/-- The changes at `[off p e]`, `len` bytes, are at `[e, e + len)` of `p`. -/
theorem Outside.of_off {p : Addr} {e len : Nat} {m m' : Mem} (h : Outside (off p e) 0 len m m')
    (he : e + len < 2 ^ 64) : Outside p e len m m' := fun x hx => h x (Or.inr (by
  rw [ofs_off_sub p x e (by omega)]
  have := (x - p).isLt
  simp only [ofs] at hx ⊢
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - e + (x - p).toNat = ((x - p).toNat - e) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]; omega))

/-! ## The entry -/

/-- The value of a zero-extended offset. -/
theorem zext_val (v : BitVec 64) :
    ((v.setWidth 32 + BitVec.ofNat 32 0).setWidth 64 : BitVec 64) = BitVec.ofNat 64 (v.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The offsets zero-extended. -/
theorem zext_ok (s : State) :
    WP isa (.block [.addImm .w .x1 .x1 0, .addImm .w .x2 .x2 0, .addImm .w .x3 .x3 0]) s fun s' =>
      s'.gpr .x1 = BitVec.ofNat 64 (arg s .x1) ∧ s'.gpr .x2 = BitVec.ofNat 64 (arg s .x2) ∧
      s'.gpr .x3 = BitVec.ofNat 64 (arg s .x3) ∧ Keeps [.x1, .x2, .x3] s s' ∧ s'.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show (0 : Nat) < 4096 by decide,
    ite_true, Option.some.injEq, exists_eq_left', State.read]
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Weierstrass.AArch64.Mont

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- The pointers: `ro = x0 + x1`, `ra = x0 + x2`, `rb = x0 + x3`. -/
theorem ptrs_ok (s : State) {ra rb ro : Reg} (ha : ra ∉ [Reg.x0, .x1, .x2, .x3])
    (hb : rb ∉ [Reg.x0, .x1, .x2, .x3]) (ho : ro ∉ [Reg.x0, .x1, .x2, .x3])
    (hd : [ra, rb, ro].Nodup) :
    WP isa (.block [.add .x ro .x0 .x1, .add .x ra .x0 .x2, .add .x rb .x0 .x3]) s fun s' =>
      s'.gpr ro = s.gpr .x0 + s.gpr .x1 ∧ s'.gpr ra = s.gpr .x0 + s.gpr .x2 ∧
      s'.gpr rb = s.gpr .x0 + s.gpr .x3 ∧ Keeps [ra, rb, ro] s s' ∧ s'.v = s.v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    State.read, BitVec.setWidth_eq]
  have e1 : ro ≠ rb := fun h => hd.2.1 h.symm
  have e2 : ro ≠ ra := fun h => hd.1.2 h.symm
  have e3 : ra ≠ rb := hd.1.1
  have := Ne.symm ha.1; have := Ne.symm ha.2.1; have := Ne.symm ha.2.2.1; have := Ne.symm ha.2.2.2
  have := Ne.symm hb.1; have := Ne.symm hb.2.1; have := Ne.symm hb.2.2.1; have := Ne.symm hb.2.2.2
  have := Ne.symm ho.1; have := Ne.symm ho.2.1; have := Ne.symm ho.2.2.1; have := Ne.symm ho.2.2.2
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  all_goals simp only [RegUpd.gpr_write]
  all_goals simp_all

theorem setConst_eq (n o x : Nat) : setConst n o x = (List.range n).flatMap (constStep o x) := rfl

/-- Word `k` of `x` in `x1`: loaded, or already there as word `k - 1`. -/
theorem constLoad_ok {s : State} {x k : Nat} (h : 0 < k → s.gpr .x1 = wordOf x (k - 1)) :
    WP isa (.block (if 0 < k ∧ wordOf x k = wordOf x (k - 1) then [] else const64 .x1 (wordOf x k))) s
      fun t => t.gpr .x1 = wordOf x k ∧ Keeps [.x1] s t := by
  split
  · rename_i e
    exact WP.block_nil ⟨(h e.1).trans e.2.symm, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · exact const64_ok s .x1 _

theorem constSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x : Nat}
    (ho8 : o % 8 = 0) : ∀ k, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (constStep o x))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = wordOf x j) ∧ (0 < k → s'.gpr .x1 = wordOf x (k - 1)) ∧
      KeepRegs [.x1] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (constSteps_ok hs ho8 k (by omega)) fun s₁ ⟨e₁, x₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [constStep, WP.block_append_iff]
    refine WP.mono (constLoad_ok x₁) fun s₂ ⟨v₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_ok hs₂ (d := o + 8 * k) (by omega) (by omega) .x1) fun s₃ e₃ => ?_
    have m₃ : s₃.mem = s₂.mem.writeW (off base (o + 8 * k)) (s₂.gpr .x1) := by rw [e₃]
    have k₃ : KeepRegs [] s₂ s₃ := by subst e₃; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have g₃ : s₃.gpr .x1 = s₂.gpr .x1 := k₃.gpr .x1 (by simp)
    rw [v₂, k₂.mem] at m₃
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₃.mem := by
      rw [m₃]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, fun _ => g₃.trans v₂, (k₁.trans ((Keeps.regs k₂).trans (k₃.mono (by simp)))),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₃, word_writeW_self]

/-- `[o] = x`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o x : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun s' =>
      wordsVal s'.mem base o n = x ∧ KeepRegs [.x1] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [setConst_eq]
  exact WP.mono (constSteps_ok hs ho8 n ho) fun s' ⟨e, _, k, O⟩ =>
    ⟨VG.Proof.Weierstrass.wordsVal_of_shifts _ _ o n x hx e, k, O⟩

/-- What the entry leaves: the working space, the modulus, the pointers to
the numbers, the saved registers in their lanes, the other registers but the
offsets' and the pointers', the memory but the modulus's, and the vector
registers but the lanes'. -/
structure Entered (n m W : Nat) (s s₁ : State) : Prop where
  scr : Scr s₁ (s.gpr .x0) W
  mod : ModOkW (mod n m) W m s₁.mem (s.gpr .x0)
  pa : Ptr s₁ (ptrs n).1 (off (s.gpr .x0) (arg s .x2)) (8 * n)
  pb : Ptr s₁ (ptrs n).2.1 (off (s.gpr .x0) (arg s .x3)) (8 * n)
  po : PtrW s₁ (ptrs n).2.2 (off (s.gpr .x0) (arg s .x1)) (8 * n)
  lanes : ∀ i (h : i < (saved n).length), lane s₁.v i = s.gpr (saved n)[i]
  gpr : ∀ r, r ∉ [Reg.x1, .x2, .x3] → r ∉ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2] →
    s₁.gpr r = s.gpr r
  mem : Outside (s.gpr .x0) (moAt n) (8 * n) s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  v : ∀ d, (∀ i < 8, d ≠ (slot i).1) → s₁.v d = s.v d

theorem moAt_facts {n : Nat} (h : n ≤ 9) (h4 : 4 ≤ n) :
    own n ≤ moAt n ∧ moAt n + 16 * n = 4096 ∧ moAt n % 8 = 0 := by
  simp only [own, moAt, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega

theorem entry_ok {n m W : Nat} (hM : ModOk n m) {s : State} (hp : Pre n W s) :
    WP isa (.block (entry n m)) s (Entered n m W s) := by
  have hw := hp.w
  have hw8 := hp.w8
  obtain ⟨Pa, Pb, Po, hlen, hnd, hpres, hsv, ha0, hb0, ho0, hpd, h019⟩ := regs_facts n hM.hn
  have hn9 := hM.n9
  have hn4 := hM.n4
  have hown := own_eq hn9
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hn4
  have hfit := hp.fit
  have ho := hp.o
  have ha := hp.a
  have hb := hp.b
  simp only [entry, entryRest, zextCode, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨g1, g2, g3, K₁, V₁⟩ => ?_
  rw [WP.block_append_iff, saveCode_eq]
  refine WP.mono (saves_ok (saved n) 0 (s := s₁) (by omega)) fun s₂ ⟨K₂, L₂, _, V₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ptrs_ok s₂ ha0 hb0 ho0 hpd) fun s₃ ⟨go, ga, gb, K₃, V₃⟩ => ?_
  have x0₃ : s₃.gpr .x0 = s.gpr .x0 := by
    rw [K₃.gpr _ (h019 .x0 (by simp)).2.2.2, K₂.gpr, K₁.gpr _ (h019 .x0 (by simp)).2.2.1]
  have hs₃ : Scr s₃ (s.gpr .x0) W := ⟨x0₃, by rw [K₃.wr, K₂.wr, K₁.wr, hp.wr]; simp, hfit, by omega⟩
  have hW := setConst_ok hs₃ (n := n) (o := moAt n) (x := m) (by omega) hmo8 hM.m_lt
  refine WP.mono (WP.block_novec (fun i hi => hM.novec i (List.mem_append_right _ hi)) hW)
    fun s₄ ⟨⟨e₄, k₄, O₄⟩, V₄⟩ => ?_
  have pg : ∀ r, r ∉ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2] → r ≠ .x1 → s₄.gpr r = s₃.gpr r :=
    fun r _ h1 => k₄.gpr r (by simpa using h1)
  have hs₄ : Scr s₄ (s.gpr .x0) W := hs₃.of_keepRegs k₄ (by decide)
  have mem₄ : Outside (s.gpr .x0) (moAt n) (8 * n) s.mem s₄.mem := by
    rw [← K₁.mem, ← K₂.mem, ← K₃.mem]; exact O₄
  -- The registers of `s₃` kept by the constant's stores (all but `x1`).
  have k1 : ∀ r, r ≠ .x1 → s₄.gpr r = s₃.gpr r := fun r h1 => k₄.gpr r (by simpa using h1)
  have rne : ∀ r ∈ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2], r ≠ .x1 := by
    intro r hr e; subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h
    · exact ha0 (by simp [← h])
    · exact hb0 (by simp [← h])
    · exact ho0 (by simp [← h])
  have off0 : ∀ x : Reg, s₂.gpr x = s₁.gpr x := fun x => by rw [K₂.gpr]
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := by rw [off0, K₁.gpr _ (h019 .x0 (by simp)).2.2.1]
  have hP : ∀ (d e : Nat), d + 8 ≤ 8 * n → e + 8 * n ≤ own n →
      InRegions (s₄.rd ++ s₄.wr) (off (s.gpr .x0) e + BitVec.ofNat 64 d) 8 := by
    intro d e hd he
    show InRegions _ (off (off (s.gpr .x0) e) d) 8
    rw [off_off]
    have := hs₄.ld (d := e + d) (by have := hd; have := he; omega)
    rwa [hs₄.x0] at this
  refine ⟨hs₄, ⟨by simp only [mod]; omega, by simp only [mod]; omega, by simp only [mod]; omega,
    .inr (by simp only [mod]; omega), e₄, ?_, hM.red⟩, ⟨?_, fun d hd => hP d _ hd ha, by omega⟩,
    ⟨?_, fun d hd => hP d _ hd hb, by omega⟩, ⟨?_, fun d hd => ?_, by omega, ?_⟩,
    fun i hi => ?_, fun r h1 hpr => ?_, mem₄, ?_, ?_, ?_, fun d hd => ?_⟩
  · rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv
  · rw [k1 _ (rne _ (by simp)), ga, x0₂, off0, g2]
  · rw [k1 _ (rne _ (by simp)), gb, x0₂, off0, g3]
  · rw [k1 _ (rne _ (by simp)), go, x0₂, off0, g1]
  · show InRegions _ (off (off (s.gpr .x0) (arg s .x1)) d) 8
    rw [off_off]
    have := hs₄.st (d := arg s .x1 + d) (by omega)
    rwa [hs₄.x0] at this
  · have := hp.fit; simp only [off, Nat.add_comm]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := arg s .x1) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [V₄, V₃]
    have := L₂ i hi
    rw [Nat.zero_add] at this
    rw [this, K₁.gpr]
    have hp' := hsv _ (List.getElem_mem hi)
    intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> rw [h] at hp' <;> exact absurd hp' (by decide)
  · rw [k1 r (fun h => h1 (by simp [h])), K₃.gpr r hpr, K₂.gpr, K₁.gpr r h1]
  · rw [k₄.rd, K₃.rd, K₂.rd, K₁.rd]
  · rw [k₄.wr, K₃.wr, K₂.wr, K₁.wr]
  · rw [k₄.sp, K₃.sp, K₂.sp, K₁.sp]
  · rw [V₄, V₃, V₂ d hd, V₁]

theorem mulFn_wp (n m : Nat) {s : State} {Q : State → Prop} : WP isa (mulFn n m) s Q ↔
    WP isa (.block (entry n m ++ (mulR (mod n m) (ptrs n).1 (ptrs n).2.1 (ptrs n).2.2 0 0 0 ++
      restoreCode n))) s Q := by
  rw [mulFn, WP.seq_iff, entry, List.append_assoc]
  exact WP.block_append_iff.symm

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn_ok {n m W : Nat} (hM : ModOk n m) {s : State} (hp : Pre n W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) n < m) :
    WP isa (mulFn n m) s fun s' => abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) n * wordsVal s.mem (s.gpr .x0) (arg s .x3) n % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 8, d ≠ (slot i).1) → s'.v d = s.v d := by
  obtain ⟨Pa, Pb, Po, hlen, hnd, hpres, hsv, ha0, hb0, ho0, hpd, h019⟩ := regs_facts n hM.hn
  have hn9 := hM.n9
  have hn4 := hM.n4
  have hown := own_eq hn9
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hn4
  have hfit := hp.fit
  have hw := hp.w
  have hw8 := hp.w8
  have ho := hp.o
  have ha := hp.a
  have hb' := hp.b
  rw [mulFn_wp, WP.block_append_iff]
  refine WP.mono (entry_ok hM hp) fun s₁ E => ?_
  -- The numbers the entry left.
  have ev : ∀ d, d + 8 * n ≤ own n → wordsVal s₁.mem (s.gpr .x0) d n = wordsVal s.mem (s.gpr .x0) d n :=
    fun d hd => E.mem.wordsVal (by omega) (by omega)
  rw [WP.block_append_iff]
  have hB : wordsVal s₁.mem (off (s.gpr .x0) (arg s .x3)) 0 n < m := by
    rw [wordsVal_off, Nat.add_zero, ev _ hb']; exact hb
  have hW := mulR_okW E.scr E.mod (by simp only [mod]; omega) ⟨by simp only [mod]; omega, by simp only [mod]; omega⟩
    E.pa E.pb E.po Pa Pb Po (o := 0) (a := 0) (b := 0) (by simp only [mod]; omega)
    (by simp only [mod]; omega) (by simp only [mod]; omega) rfl rfl rfl hB
  refine WP.mono (WP.block_novec (fun i hi => hM.novec i (List.mem_append_left _ hi)) hW)
    fun s₂ ⟨⟨K, V, C⟩, Vv⟩ => ?_
  rw [restoreCode_eq]
  refine WP.mono (restores_ok (saved n) 0 (by omega) hnd) fun s₃ ⟨K₃, V₃, R₃⟩ => ?_
  have e1 : (mod n m).n = n := rfl
  rw [e1] at V C K
  have mem₂ : s₃.mem = s₂.mem := K₃.mem
  -- The registers kept by everything but the saves and restores.
  have keep : ∀ r, r ∉ saved n → r ∉ clob n → r ∉ [Reg.x1, .x2, .x3] →
      r ∉ [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2] → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [K₃.gpr r h1, K.gpr r h2, E.gpr r h3 h4]
  refine ⟨⟨fun r hr => ?_, by rw [K₃.sp, K.sp, E.sp], fun d hd => ?_⟩, fun x hx hx' => ?_, ⟨?_, ?_⟩,
    keep .x0 (h019 .x0 (by simp)).2.1 (h019 .x0 (by simp)).1 (h019 .x0 (by simp)).2.2.1
      (h019 .x0 (by simp)).2.2.2, by rw [K₃.rd, K.rd, E.rd], by rw [K₃.wr, K.wr, E.wr],
    fun d hd => by rw [V₃, Vv, E.v d hd]⟩
  · by_cases hs : r ∈ saved n
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      rw [R₃ i hi, Nat.zero_add, Vv, E.lanes i hi]
    · obtain ⟨c1, c2, c3⟩ := hpres r hr hs
      exact keep r hs c1 c2 c3
  · have hd' : ∀ i < 8, d ≠ (slot i).1 := by
      have : ∀ d ∈ preservedV, ∀ i < 8, d ≠ (slot i).1 := by decide
      exact this d hd
    rw [V₃, Vv, E.v d hd']
  · rw [mem₂]
    have := Outside.of_off K.mem (by have := (s.gpr .x0).isLt; omega)
    rw [this x hx, E.mem x hx']
  · have e := wordsVal_off s₂.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₂, ← e]; exact V
  · have e := wordsVal_off s₂.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₂, ← e, C, wordsVal_off, wordsVal_off, Nat.add_zero, Nat.add_zero, ev _ ha, ev _ hb']

end VG.Proof.Weierstrass.AArch64.Mont
