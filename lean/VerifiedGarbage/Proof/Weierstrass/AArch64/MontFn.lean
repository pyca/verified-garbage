import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontRound
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Montgomery products modulo a curve's `p` or `n`, as functions, on AArch64

`mulFn n m` (`Impl/Weierstrass/AArch64/Mont.lean`), from a state `Pre n m`
(`ws` in `x0` and the offsets in `w1`–`w3`, the working space the only
region, the numbers below the function's own working space), zero-extends the
offsets (`zext_ok`), saves the callee-saved registers it writes in vector
lanes (`saves_ok`) and computes its pointers (`ptrsF_ok`); its body
(`bodyF_ok`) loads `[b]` and the modulus into registers, runs the rounds
(`roundsG_ok`), reduces the result against the modulus in registers
(`csubM_ok`) and stores it; then it restores the registers (`mulFn_ok`). The
function keeps the callee-saved registers, `x30`, `sp` and the low halves of
`v8`–`v15` (`abiPreserved`), changes the memory only at `[o]` (`Kept`), and
leaves `x0 = ws`, `x19` and `x20`.
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- An offset argument: the low 32 bits of its register. -/
abbrev arg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- The function's own working space. -/
abbrev own (n : Nat) : Nat := Spec.Weierstrass.Mont.ownAt n

/-- The registers the body writes. -/
def bodyW (n : Nat) : List Reg := [.x1, .x2, .x3, .x6, .x7, .x23] ++ bRegsF n ++ mPool n ++ acc n ++ dRegs n

/-- The pointer additions. -/
def ptrsCode (n : Nat) : List Instr := [.add .x (roF n) .x0 .x1, .add .x (raF n) .x0 .x2, .add .x .x3 .x0 .x3]

/-- What follows the pointers: `[b]` into registers, the reduction's constant,
`x7` and the accumulator cleared, the rounds, the modulus into registers, the
reduction and the store. -/
def bodyCode (n m : Nat) : List Instr :=
  loadsR .x3 (bRegsF n) 0 ++ (mulConst (mod n m) ++
    ((zero7 :: zeros (acc n)) ++ ((List.range n).flatMap (roundF n m) ++
      (mLoadCode n m ++ (csubM n (lowF n) (win n n n) (mRegs n m) ++
        storesR (roF n) (lowF n) 0)))))

/-- Whether a reduction is a friendly modulus's. -/
def isFriendly : Red → Bool
  | .friendly _ => true
  | .general => false

theorem friendly_of {r : Red} (h : isFriendly r = true) : ∃ ws, r = .friendly ws := by
  cases r with
  | friendly ws => exact ⟨ws, rfl⟩
  | general => exact absurd h (by decide)

/-- What the function needs of the modulus `m` of `n` words: six or nine
words, `m` below `2^(64 n)`, `minv m` its inverse's negation, what the
multiplication needs of it, P-384's sparse `p` (reduced as a general one's
constant says) or a friendly modulus, `x6` free for `[b]` only where the
reduction needs no constant, each word of `m` in the register `mReg` once
`mLoadCode` builds them (in distinct registers), and code that writes no
vector register but the lanes'. -/
structure ModOk (n m : Nat) : Prop where
  hn : n = 6 ∨ n = 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true
  kind : (sparseOk n m = true ∧ (mod n m).red = .general) ∨
    (sparseOk n m = false ∧ ∃ ws, (mod n m).red = .friendly ws)
  x6 : Reg.x6 ∈ bRegsF n → mulConst (mod n m) = []
  loads : ∀ j < n, (mReg n m j, mWord m j) ∈ mLoads n m
  lnd : ((mLoads n m).map Prod.fst).Nodup
  novec : ∀ i ∈ ptrsCode n ++ bodyCode n m, vdstOf i = none

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

theorem ModOk.n9 {n m : Nat} (h : ModOk n m) : n ≤ 9 := by rcases h.hn with h | h <;> omega
theorem ModOk.n4 {n m : Nat} (h : ModOk n m) : 4 ≤ n := by rcases h.hn with h | h <;> omega
theorem ModOk.hn' {n m : Nat} (h : ModOk n m) : n = 4 ∨ n = 6 ∨ n = 9 := .inr h.hn

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-! ## Facts of the registers, for each number of words -/

/-- What the code needs of its registers. -/
structure Regs (n : Nat) : Prop where
  n10 : n < 10
  bsafe : RoundSafe n (bRegsF n)
  macc : ∀ r ∈ mPool n, r ∉ acc n
  ra : raF n ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n
  ro : roF n ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n
  blen : (bRegsF n).length = n
  bnd : (bRegsF n).Nodup
  b3 : Reg.x3 ∉ bRegsF n
  bra : raF n ∉ bRegsF n
  bro : roF n ∉ bRegsF n
  b7 : Reg.x7 ∉ bRegsF n
  md : ∀ r ∈ mPool n, r ∉ dRegs n
  m2 : ∀ r ∈ mPool n, r ≠ .x2 ∧ r ≠ .x7 ∧ r ≠ roF n
  rod : roF n ∉ dRegs n
  r67 : raF n ≠ .x6 ∧ raF n ≠ .x7 ∧ roF n ≠ .x6 ∧ roF n ≠ .x7
  rom : roF n ∉ mPool n
  ra3 : raF n ≠ .x3 ∧ roF n ≠ .x3 ∧ raF n ≠ roF n ∧ raF n ≠ .x0 ∧ roF n ≠ .x0 ∧ raF n ≠ .x1 ∧
    raF n ≠ .x2 ∧ roF n ≠ .x1 ∧ roF n ≠ .x2
  slen : (saved n).length ≤ 10
  snd : (saved n).Nodup
  spres : ∀ r ∈ saved n, r ∈ preserved
  pres : ∀ r ∈ preserved, r ∉ saved n → r ∉ bodyW n ∧ r ≠ roF n ∧ r ≠ raF n
  keep0 : ∀ r ∈ [Reg.x0, .x19, .x20], r ∉ bodyW n ∧ r ∉ saved n ∧ r ≠ roF n ∧ r ≠ raF n
  nro : roF n ∉ bodyW n

theorem regs_ok : ∀ n, (n = 6 ∨ n = 9) → Regs n := by
  intro n hn
  rcases hn with rfl | rfl <;> constructor <;> first | decide | (unfold RoundSafe; decide)

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

/-- The pointers: `ro = x0 + x1`, `ra = x0 + x2`, and `x3 = x0 + x3`. -/
theorem ptrsF_ok (s : State) {ra ro : Reg} (ha : ra ∉ [Reg.x0, .x1, .x2, .x3])
    (ho : ro ∉ [Reg.x0, .x1, .x2, .x3]) (hd : ra ≠ ro) :
    WP isa (.block [.add .x ro .x0 .x1, .add .x ra .x0 .x2, .add .x .x3 .x0 .x3]) s fun s' =>
      s'.gpr ro = s.gpr .x0 + s.gpr .x1 ∧ s'.gpr ra = s.gpr .x0 + s.gpr .x2 ∧
      s'.gpr .x3 = s.gpr .x0 + s.gpr .x3 ∧ Keeps [ra, .x3, ro] s s' ∧ s'.v = s.v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha ho
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    State.read, BitVec.setWidth_eq]
  have e2 : ro ≠ ra := Ne.symm hd
  have := Ne.symm ha.1; have := Ne.symm ha.2.1; have := Ne.symm ha.2.2.1; have := Ne.symm ha.2.2.2
  have := Ne.symm ho.1; have := Ne.symm ho.2.1; have := Ne.symm ho.2.2.1; have := Ne.symm ho.2.2.2
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  all_goals simp only [RegUpd.gpr_write]
  all_goals simp_all

/-! ## The body -/

theorem regsVal_of_loads {s : State} {mem : Mem} {p : Addr} : ∀ (ts : List Reg) (a : Nat),
    (∀ j (r : Reg), ts[j]? = some r → s.gpr r = word mem p (a + 8 * j)) →
    regsVal s ts = wordsVal mem p a ts.length
  | [], _, _ => rfl
  | t :: ts, a, h => by
    have h0 := h 0 t rfl
    rw [Nat.mul_zero, Nat.add_zero] at h0
    have hr := regsVal_of_loads ts (a + 8) fun j r hr => by
      rw [h (j + 1) r (by rw [List.getElem?_cons_succ]; exact hr), show a + 8 * (j + 1) = a + 8 + 8 * j by omega]
    rw [List.length_cons, regsVal, wordsVal, h0, hr]

theorem mLoads_fst {n m : Nat} {p : Reg × BitVec 64} (hp : p ∈ mLoads n m) : p.1 ∈ mPool n :=
  (List.of_mem_zip hp).1

theorem mRegs_sub {n m : Nat} (hM : ModOk n m) : ∀ r ∈ mRegs n m, r ∈ mPool n := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact mLoads_fst (hM.loads j (List.mem_range.mp hj))

theorem mRegs_length (n m : Nat) : (mRegs n m).length = n := by simp [mRegs]

/-- The modulus's words into their registers. -/
theorem mLoad_ok {n m : Nat} (hM : ModOk n m) (s : State) :
    WP isa (.block (mLoadCode n m)) s fun s' => regsVal s' (mRegs n m) = m ∧ Keeps (mPool n) s s' := by
  rw [mLoadCode]
  refine WP.mono (constLoads_ok (mLoads n m) hM.lnd) fun s' ⟨e, k⟩ => ⟨?_, k.mono fun r hr => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr; exact mLoads_fst hp⟩
  rw [mRegs, List.range_eq_range']
  exact regsVal_of_shifts s' (mReg n m) 0 n m hM.m_lt fun k hk => by
    rw [Nat.zero_add]; exact e _ (hM.loads k hk)

/-- The reduction's constant into `x6`. -/
theorem mulConst_ok (M : Mod) (s : State) :
    WP isa (.block (mulConst M)) s fun s' => ConstOk M s' ∧ Keeps [.x6] s s' := by
  cases hr : M.red with
  | general =>
    rw [show mulConst M = const64 .x6 M.minv by simp only [mulConst, hr]]
    refine WP.mono (const64_ok s .x6 M.minv) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
    unfold ConstOk; rw [hr]; exact e
  | friendly ws =>
    cases hg : firstGen ws with
    | none =>
      rw [show mulConst M = [] by simp only [mulConst, hr, hg]]
      refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      unfold ConstOk; rw [hr]; intro v hv; rw [hg] at hv; exact absurd hv (by simp)
    | some v =>
      rw [show mulConst M = const64 .x6 (BitVec.ofNat 64 v) by simp only [mulConst, hr, hg]]
      refine WP.mono (const64_ok s .x6 (BitVec.ofNat 64 v)) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
      unfold ConstOk; rw [hr]; intro v' hv'
      rw [hg, Option.some.injEq] at hv'
      rw [e, hv']

theorem constOk_of_nil {M : Mod} (h : mulConst M = []) (s : State) : ConstOk M s := by
  cases hr : M.red with
  | general => simp only [mulConst, hr, const64] at h; exact absurd h (by simp)
  | friendly ws =>
    cases hg : firstGen ws with
    | none => simp only [ConstOk, hr]; intro v hv; rw [hg] at hv; exact absurd hv (by simp)
    | some v => simp only [mulConst, hr, hg, const64] at h; exact absurd h (by simp)

theorem mem_bodyW_fixed {n : Nat} : ∀ r ∈ [Reg.x1, .x2, .x3, .x6, .x7, .x23], r ∈ bodyW n := by
  intro r hr; simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hr)))

theorem mem_bodyW_b {n : Nat} {r : Reg} (h : r ∈ bRegsF n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem mem_bodyW_m {n : Nat} {r : Reg} (h : r ∈ mPool n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inr h))

theorem mem_bodyW_acc {n : Nat} {r : Reg} (h : r ∈ acc n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inr h)

theorem mem_bodyW_d {n : Nat} {r : Reg} (h : r ∈ dRegs n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inr h

theorem mem_bodyW_round {n : Nat} {r : Reg} (h : r ∈ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n) :
    r ∈ bodyW n := by
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | h
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_acc h

/-- The body: `[po] = [pa] [pb] R⁻¹ mod m`, changing only the registers
`bodyW` and the memory at `[po]`. -/
theorem bodyF_ok {n m : Nat} (hM : ModOk n m) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {pa pb po : Addr} (hpa : Ptr s (raF n) pa (8 * n)) (hpb : Ptr s .x3 pb (8 * n))
    (hpo : PtrW s (roF n) po (8 * n)) (hB : wordsVal s.mem pb 0 n < m) :
    WP isa (.block (bodyCode n m)) s fun s' =>
      (∀ r, r ∉ bodyW n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * n) s.mem s'.mem ∧ wordsVal s'.mem po 0 n < m ∧
      wordsVal s'.mem po 0 n * 2 ^ (64 * n) % m = wordsVal s.mem pa 0 n * wordsVal s.mem pb 0 n % m := by
  have R := regs_ok n hM.hn
  have hn := R.n10
  have hacc := acc_regs_lt _ hn
  have hmX := hM.m_lt
  -- How each step's changes keep a register outside `bodyW`.
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ bodyW n) →
      ∀ r, r ∉ bodyW n → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  have x0W : Reg.x0 ∉ bodyW n := (R.keep0 .x0 (by simp)).1
  rw [bodyCode, WP.block_append_iff]
  -- `[b]` into its registers.
  refine WP.mono (loadsEach_ok (bRegsF n) hpb (a := 0) (by rw [R.blen]; omega) rfl R.bnd R.b3)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hB₁ : regsVal s₁ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [regsVal_of_loads _ 0 e₁, R.blen]
  have w₁ := kw k₁ fun q hq => mem_bodyW_b hq
  -- The reduction's constant.
  rw [WP.block_append_iff]
  have hC : WP isa (.block (mulConst (mod n m))) s₁ fun s₃ => ConstOk (mod n m) s₃ ∧
      Keeps (if mulConst (mod n m) = [] then [] else [.x6]) s₁ s₃ := by
    by_cases hc : mulConst (mod n m) = []
    · rw [hc]
      simp only [↓reduceIte]
      exact WP.block_nil ⟨constOk_of_nil hc s₁, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · exact WP.mono (mulConst_ok _ s₁) fun s₃ ⟨c, k⟩ => ⟨c, by simp only [hc, ↓reduceIte]; exact k⟩
  refine WP.mono hC fun s₃ ⟨c₃, k₃⟩ => ?_
  have w₃ := kw k₃ fun q hq => by
    split at hq
    · exact absurd hq List.not_mem_nil
    · exact mem_bodyW_fixed q (by simp at hq; simp [hq])
  have g₃ : ∀ r, r ≠ .x6 → s₃.gpr r = s₁.gpr r := fun r hr => k₃.gpr r (by
    split
    · exact List.not_mem_nil
    · simp only [List.mem_singleton]; exact hr)
  have hB₃ : regsVal s₃ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [← hB₁]
    refine regsVal_congr fun r hr => k₃.gpr r ?_
    split
    · exact List.not_mem_nil
    · rename_i hc
      simp only [List.mem_singleton]
      rintro rfl
      exact hc (hM.x6 hr)
  -- `x7` and the accumulator cleared.
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₃) fun s₄ ⟨z₄, k₄⟩ => ?_
  have w₄ := kw k₄ fun q hq => mem_bodyW_fixed q (by simp at hq; simp [hq])
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok s₄ (acc n)) fun s₅ ⟨z₅, k₅⟩ => ?_
  have w₅ := kw k₅ fun q hq => mem_bodyW_acc hq
  have c₅ : ConstOk (mod n m) s₅ := c₃.keep (by
    rw [k₅.gpr _ (fun h => by have := hacc _ h; simp at this), k₄.gpr _ (by decide)])
  have z₇ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (fun h => by have := hacc _ h; simp at this), z₄]
  have hB₅ : regsVal s₅ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [← hB₃, regsVal_congr fun r hr => k₅.gpr r (R.bsafe.acc hr),
      regsVal_congr fun r hr => k₄.gpr r (by simp only [List.mem_singleton]; rintro rfl; exact R.b7 hr)]
  have h0 : regsVal s₅ (wins n 0) = 0 := regsVal_zero fun r hr => z₅ r (wins_sub_acc hn 0 r hr)
  -- The pointers so far.
  have kp : ∀ r, r ∉ bodyW n → s₅.gpr r = s.gpr r := fun r hr => by
    rw [w₅ r hr, w₄ r hr, w₃ r hr, w₁ r hr]
  have nro : roF n ∉ bodyW n := R.nro
  have ra₅ : s₅.gpr (raF n) = s.gpr (raF n) := by
    have hra := R.ra
    simp only [List.mem_cons, not_or] at hra
    rw [k₅.gpr _ hra.2.2.2.2, k₄.gpr _ (by simp [R.r67.2.1]), g₃ _ R.r67.1, k₁.gpr _ R.bra]
  have hmem₅ : s₅.mem = s.mem := by rw [k₅.mem, k₄.mem, k₃.mem, k₁.mem]
  have hrd₅ : s₅.rd = s.rd := by rw [k₅.rd, k₄.rd, k₃.rd, k₁.rd]
  have hwr₅ : s₅.wr = s.wr := by rw [k₅.wr, k₄.wr, k₃.wr, k₁.wr]
  have hs₅ : Scr s₅ base size := ⟨(kp _ x0W).trans hs.x0, hwr₅ ▸ hs.wr, hs.nowrap, hs.enc⟩
  have hpa₅ : Ptr s₅ (raF n) pa (8 * n) :=
    ⟨ra₅.trans hpa.reg, by rw [hrd₅, hwr₅]; exact hpa.ld, hpa.enc⟩
  -- The rounds.
  rw [WP.block_append_iff]
  have hinv : (m * (mod n m).minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv
  have hsp : sparseOk n m = true → (mod n m).n = 6 ∧ m = p384 ∧ (mod n m).red = .general := fun h => by
    obtain ⟨h6, hp⟩ := sparseOk_eq h
    rcases hM.kind with ⟨_, hg⟩ | ⟨hf, _⟩
    · exact ⟨h6, hp, hg⟩
    · rw [h] at hf; exact absurd hf (by decide)
  have hfr : sparseOk n m = false → ∃ ws, (mod n m).red = .friendly ws := fun h => by
    rcases hM.kind with ⟨ht, _⟩ | ⟨_, hw⟩
    · rw [h] at ht; exact absurd ht (by decide)
    · exact hw
  have hR := roundsG_ok (M := mod n m) (size := size) (sp := sparseOk n m) hn R.ra R.bsafe R.blen hsp hfr
    (pa := pa) (sa := 8 * n) (Nat.le_refl _) hmX hinv hM.red n (Nat.le_refl _) hs₅ hpa₅ z₇ c₅
    (by rw [hB₅]; exact hB) h0
  rw [show (List.range n).flatMap (roundF n m) =
      (List.range n).flatMap (roundG (mod n m) (raF n) (bRegsF n) (sparseOk n m)) from rfl]
  refine WP.mono hR fun s₆ ⟨⟨U, eU⟩, hT, k₆⟩ => ?_
  replace hT : regsVal s₆ (wins n n) < 2 * m := hT
  replace eU : 2 ^ (64 * n) * regsVal s₆ (wins n n) =
      wordsVal s₅.mem pa 0 n * regsVal s₅ (bRegsF n) + U * m := eU
  have w₆ := kw k₆ fun q hq => mem_bodyW_round hq
  rw [hmem₅, hB₅] at eU
  -- The modulus into its registers.
  rw [WP.block_append_iff]
  refine WP.mono (mLoad_ok hM s₆) fun s₇ ⟨e₇, k₇⟩ => ?_
  have g₇ : ∀ r, r ∉ mPool n → s₇.gpr r = s₆.gpr r := fun r hr => k₇.gpr r hr
  have hz₇ : s₇.gpr .x7 = 0 := by
    rw [g₇ _ (fun h => (R.m2 _ h).2.1 rfl), k₆.gpr _ (fun h => by
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · have := hacc _ h; simp at this), z₇]
  -- The result reduced.
  have hsplit := wins_split n n
  have hlowlen : (lowF n).length = n := by simp [lowF]
  have hlow_acc : ∀ r ∈ lowF n, r ∈ acc n := fun r hr =>
    wins_sub_acc hn n r (by rw [hsplit]; exact List.mem_append_left _ hr)
  have hT₇ : ∀ r ∈ wins n n, s₇.gpr r = s₆.gpr r := fun r hr =>
    g₇ r fun h => R.macc _ h (wins_sub_acc hn n r hr)
  have hV : regsVal s₇ (lowF n) + 2 ^ (64 * n) * (s₇.gpr (win n n n)).toNat = regsVal s₆ (wins n n) := by
    have hw' := regsVal_congr (rs := wins n n) hT₇
    rw [← hw', hsplit, regsVal_append, show ((List.range n).map (win n n)).length = n by simp]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [← hw', hsplit, regsVal_append, show ((List.range n).map (win n n)).length = n by simp] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₇.gpr (win n n (n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * n) * 2 ^ 64 ≤ 2 ^ (64 * n) * ((s₇.gpr (win n n n)).toNat +
          2 ^ 64 * (s₇.gpr (win n n (n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega)
      have : m < 2 ^ (64 * n) := hmX
      have : 2 ^ (64 * n) * 2 ^ 64 ≥ 2 * 2 ^ (64 * n) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (csubM_ok hlowlen (mRegs_length n m) (by rcases hM.hn with rfl | rfl <;> decide) hn
    (fresh_low n hn) (fun r hr => R.md r (mRegs_sub hM r hr)) hz₇ e₇ hmX (by rw [hV]; exact hT))
    fun s₈ ⟨e₈, k₈⟩ => ?_
  have w₈ := kw k₈ fun q hq => by
    simp only [List.mem_cons, List.mem_append] at hq
    rcases hq with (rfl | h) | h
    · exact mem_bodyW_fixed _ (by simp)
    · exact mem_bodyW_acc (hlow_acc _ h)
    · exact mem_bodyW_d h
  -- The store.
  have kr : ∀ r, r ∉ bodyW n → s₈.gpr r = s.gpr r :=
    fun r hr => by rw [w₈ r hr, g₇ r (fun h => hr (mem_bodyW_m h)), w₆ r hr, kp r hr]
  have hmem₈ : s₈.mem = s.mem := by rw [k₈.mem, k₇.mem, k₆.mem, hmem₅]
  have hpo₈ : PtrW s₈ (roF n) po (8 * n) :=
    ⟨(kr _ nro).trans hpo.reg, by rw [k₈.wr, k₇.wr, k₆.wr, hwr₅]; exact hpo.st,
      hpo.enc, hpo.nowrap⟩
  refine WP.mono (storesR_ok _ hpo₈ (o := 0) (by rw [hlowlen]; omega) rfl (fresh_low' n hn).1)
    fun s₉ ⟨e₉, k₉, O₉⟩ => ?_
  rw [hlowlen] at e₉ O₉
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₉.gpr r (by simp), kr r hr]
  · rw [k₉.rd, k₈.rd, k₇.rd, k₆.rd, hrd₅]
  · rw [k₉.wr, k₈.wr, k₇.wr, k₆.wr, hwr₅]
  · rw [k₉.sp, k₈.sp, k₇.sp, k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp]
  · intro x hx; rw [O₉ x hx, hmem₈]
  · rw [e₉, e₈, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₉, e₈, hV, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

/-! ## The function -/

theorem moAt_facts {n : Nat} (h : n ≤ 9) (h4 : 4 ≤ n) :
    own n ≤ moAt n ∧ moAt n + 16 * n = 4096 ∧ moAt n % 8 = 0 := by
  simp only [own, moAt, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega

theorem mulFn_wp (n m : Nat) {s : State} {Q : State → Prop} : WP isa (mulFn n m) s Q ↔
    WP isa (.block (zextCode ++ (saveCode n ++ (ptrsCode n ++ (bodyCode n m ++ restoreCode n))))) s Q := by
  rw [mulFn, WP.seq_iff, ← WP.block_append_iff]
  simp only [entryRest, exitCode, bodyCode, ptrsCode, List.append_assoc, List.cons_append, List.nil_append]

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn_ok {n m W : Nat} (hM : ModOk n m) {s : State} (hp : Pre n W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) n < m) :
    WP isa (mulFn n m) s fun s' => abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) n * wordsVal s.mem (s.gpr .x0) (arg s .x3) n % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  have R := regs_ok n hM.hn
  have hn9 := hM.n9
  have hown := own_eq hn9
  have hfit := hp.fit
  have hw := hp.w
  have hw8 := hp.w8
  have ho := hp.o
  have ha := hp.a
  have hb' := hp.b
  have k0 := R.keep0 .x0 (by simp)
  have hn4 := hM.n4
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hM.n4
  rw [mulFn_wp, WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨g1, g2, g3, K₁, V₁⟩ => ?_
  rw [WP.block_append_iff, saveCode_eq]
  refine WP.mono (saves_ok (saved n) 0 (s := s₁) (by have := R.slen; omega)) fun s₂ ⟨K₂, L₂, _, V₂⟩ => ?_
  rw [WP.block_append_iff, ptrsCode]
  obtain ⟨r3a, r3o, rao, ra0, ro0, ra1, ra2, ro1, ro2⟩ := R.ra3
  refine WP.mono (ptrsF_ok s₂ (ra := raF n) (ro := roF n) (by simp [ra0, ra1, ra2, r3a]) (by simp [ro0, ro1, ro2, r3o])
    rao) fun s₃ ⟨go, ga, gb, K₃, V₃⟩ => ?_
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := by rw [K₂.gpr, K₁.gpr _ (by decide)]
  have x0₃ : s₃.gpr .x0 = s.gpr .x0 := by
    rw [K₃.gpr _ (by simp [Ne.symm ra0, Ne.symm ro0]), x0₂]
  have hs₃ : Scr s₃ (s.gpr .x0) W := ⟨x0₃, by rw [K₃.wr, K₂.wr, K₁.wr, hp.wr]; simp, hfit, by omega⟩
  have off0 : ∀ x : Reg, s₂.gpr x = s₁.gpr x := fun x => by rw [K₂.gpr]
  have hP : ∀ (d e : Nat), d + 8 ≤ 8 * n → e + 8 * n ≤ own n →
      InRegions (s₃.rd ++ s₃.wr) (off (s.gpr .x0) e + BitVec.ofNat 64 d) 8 := by
    intro d e hd he
    show InRegions _ (off (off (s.gpr .x0) e) d) 8
    rw [off_off]
    have := hs₃.ld (d := e + d) (by have := hd; have := he; omega)
    rwa [hs₃.x0] at this
  have hpa : Ptr s₃ (raF n) (off (s.gpr .x0) (arg s .x2)) (8 * n) :=
    ⟨by rw [ga, x0₂, off0, g2], fun d hd => hP d _ hd ha, by omega⟩
  have hpb : Ptr s₃ .x3 (off (s.gpr .x0) (arg s .x3)) (8 * n) :=
    ⟨by rw [gb, x0₂, off0, g3], fun d hd => hP d _ hd hb', by omega⟩
  have hpo : PtrW s₃ (roF n) (off (s.gpr .x0) (arg s .x1)) (8 * n) := by
    refine ⟨by rw [go, x0₂, off0, g1], fun d hd => ?_, by omega, ?_⟩
    · show InRegions _ (off (off (s.gpr .x0) (arg s .x1)) d) 8
      rw [off_off]
      have := hs₃.st (d := arg s .x1 + d) (by omega)
      rwa [hs₃.x0] at this
    · have := hp.fit; simp only [off, Nat.add_comm]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := arg s .x1) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega
  have hmem₃ : s₃.mem = s.mem := by rw [K₃.mem, K₂.mem, K₁.mem]
  have hB : wordsVal s₃.mem (off (s.gpr .x0) (arg s .x3)) 0 n < m := by
    rw [wordsVal_off, Nat.add_zero, hmem₃]; exact hb
  rw [WP.block_append_iff]
  refine WP.mono (WP.block_novec (fun i hi => hM.novec i (List.mem_append_right _ hi))
    (bodyF_ok hM hs₃ hpa hpb hpo hB)) fun s₄ ⟨⟨G₄, rd₄, wr₄, sp₄, O₄, V, C⟩, Vv⟩ => ?_
  rw [restoreCode_eq]
  refine WP.mono (restores_ok (saved n) 0 (by have := R.slen; omega) R.snd) fun s₅ ⟨K₅, V₅, R₅⟩ => ?_
  have mem₅ : s₅.mem = s₄.mem := K₅.mem
  -- The registers kept by everything but the saves and restores.
  have keep : ∀ r, r ∉ saved n → r ∉ bodyW n → r ∉ [Reg.x1, .x2, .x3] → r ≠ roF n → r ≠ raF n →
      s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [K₅.gpr r h1, G₄ r h2, K₃.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h5, fun e => h3 (by simp [e]), h4⟩), off0, K₁.gpr r h3]
  have ev : ∀ d, wordsVal s₃.mem (off (s.gpr .x0) d) 0 n = wordsVal s.mem (s.gpr .x0) d n := fun d => by
    rw [wordsVal_off, Nat.add_zero, hmem₃]
  refine ⟨⟨fun r hr => ?_, by rw [K₅.sp, sp₄, K₃.sp, K₂.sp, K₁.sp], fun d hd => ?_⟩, fun x hx _ => ?_, ⟨?_, ?_⟩,
    keep .x0 k0.2.1 k0.1 (by decide) (Ne.symm ro0) (Ne.symm ra0), by rw [K₅.rd, rd₄, K₃.rd, K₂.rd, K₁.rd],
    by rw [K₅.wr, wr₄, K₃.wr, K₂.wr, K₁.wr], fun d hd => by rw [V₅, Vv, V₃, V₂ d hd, V₁]⟩
  · by_cases hs : r ∈ saved n
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      have l := L₂ i hi
      rw [Nat.zero_add] at l
      rw [R₅ i hi, Nat.zero_add, Vv, V₃, l, K₁.gpr]
      have hp' := R.spres _ (List.getElem_mem hi)
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] at hp' <;> exact absurd hp' (by decide)
    · obtain ⟨c1, c2, c3⟩ := R.pres r hr hs
      exact keep r hs c1 (by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> exact absurd hr (by decide)) c2 c3
  · have hd' : ∀ i < 10, d ≠ (slot i).1 := by
      have : ∀ d ∈ preservedV, ∀ i < 10, d ≠ (slot i).1 := by decide
      exact this d hd
    rw [V₅, Vv, V₃, V₂ d hd', V₁]
  · rw [mem₅]
    have := Outside.of_off O₄ (by have := (s.gpr .x0).isLt; omega)
    rw [this x hx, hmem₃]
  · have e := wordsVal_off s₄.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₅, ← e]; exact V
  · have e := wordsVal_off s₄.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₅, ← e, C, ev, ev]

end VG.Proof.Weierstrass.AArch64.Mont
