import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.CallLay

/-! # Constant-time table selection for the x86 comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-- The words the selection stores: those of entry `a` of the table at `X`
if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word {mem mem' : Mem} {base X : Addr} {n a H o : Nat}
    (h : ∀ c < n, mem'.readW (off base (o + 16 * c)) 128 = accVal mem X n a H c) :
    ∀ i < 2 * n, word mem' base (o + 8 * i) =
      if 1 ≤ a ∧ a ≤ H then word mem X (16 * n * (a - 1) + 8 * i) else 0 := by
  intro i hi
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 2 ∧ i = 2 * c + q := ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  have e := readW_extract mem' (off base (o + 16 * c)) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add, show o + 16 * c + 8 * q = o + 8 * (2 * c + q) by omega] at e
  rw [Mont.word, off, ← e, h c (by omega), accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (16 * n * (a - 1) + 16 * c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
    rw [show 16 * n * (a - 1) + 16 * c + 8 * q = 16 * n * (a - 1) + 8 * (2 * c + q) by omega]
  · simp

/-- Numbers with the same words. -/
theorem wordsVal_congr₂ {m m' : Mem} {b b' : Addr} : ∀ (o o' k : Nat),
    (∀ i < k, word m' b' (o' + 8 * i) = word m b (o + 8 * i)) → wordsVal m' b' o' k = wordsVal m b o k
  | _, _, 0, _ => rfl
  | o, o', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_congr₂ (o + 8) (o' + 8) k fun i hi => by
      rw [show o + 8 + 8 * i = o + 8 * (i + 1) by omega, show o' + 8 + 8 * i = o' + 8 * (i + 1) by omega]
      exact h (i + 1) (by omega)]

theorem Unch.split {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 2 * k)] m m') :
    Unch base [(o, k), (o + k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  dsimp only at h1 h2 ⊢; omega

/-- What the selection leaves: in `E`, entry `a`'s `x` and `y` (of the table
at `X`) and `R` if `a ≥ 1`, else `(0, R, 0)`. -/
structure SelPost (K : TCombCfg) (base : Addr) (s : State) (a : Nat) (X : Addr) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1)) K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then K.one else 0
  keep : Keeps [.eax, .ecx, .edx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

/-- The words of `v < 2^(64 k)`, word by word, are `v`. -/
theorem wordsVal_wordOf {m : Mem} {b : Addr} {o k v : Nat} (hv : v < 2 ^ (64 * k))
    (h : ∀ i < k, word m b (o + 8 * i) = wordOf v i) : wordsVal m b o k = v :=
  wordsVal_of_shifts m b o k v hv h

/-- Zero words. -/
theorem wordsVal_zeros {m : Mem} {b : Addr} {o k : Nat} (h : ∀ i < k, word m b (o + 8 * i) = 0) :
    wordsVal m b o k = 0 :=
  wordsVal_of_shifts m b o k 0 (Nat.two_pow_pos _) fun i hi => by rw [h i hi, Nat.zero_shiftRight]; rfl

/-- Load the retained public table pointer and add the window offset. -/
theorem selSetup_ok (K : TCombCfg) {s : State} {base : Addr} {size j : Nat} {T : BitVec 32}
    (hs : Scr s base size) (hptr : K.ptr + 4 ≤ size)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) (hT : s.mem.readW (off base K.ptr) 32 = T)
    (htb : K.tblBytes < 2 ^ 32) :
    WP isa (.block K.selSetup) s fun t => t.gpr .edx = T + BitVec.ofNat 32 (j * K.tblBytes) ∧
      CKeeps [.eax, .ecx, .edx] s t := by
  have hea : (s.gpr .edi + BitVec.ofNat 32 K.ptr).setWidth 64 = off base K.ptr :=
    hs.ea (d := K.ptr) (by omega)
  have hread := hs.read hptr
  apply WP.of_runBlock
  simp only [TCombCfg.selSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execMul, State.load32, State.ea, sc, at_, hb, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags, hea, hread, hT,
    Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt htb, Nat.mod_mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- The retained table pointer addresses every entry; the scalar magnitude
only controls masks. The selected point is neutral when its magnitude is zero. -/
theorem select_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 6) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 32)
    (hptr : K.ptr + 4 ≤ size) (hexy : K.E.y = K.E.x + 8 * K.M.n)
    (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x)
    (hzero : K.zero + 8 * K.M.n ≤ size)
    (h0xy : K.zero + 8 * K.M.n ≤ K.E.x ∨ K.E.x + 16 * K.M.n ≤ K.zero)
    (h0z : K.zero + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.M.n)) (h0 : wordsVal s.mem base K.zero K.M.n = 0)
    {j a : Nat} {T : BitVec 32} (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (h8 : s.gpr .ebx = BitVec.ofNat 32 a) (ha : a ≤ K.H)
    (hT : s.mem.readW (off base K.ptr) 32 = T)
    (hreg : InRegions (s.rd ++ s.wr) ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64) K.tblBytes)
    (hX : ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64).toNat + K.tblBytes ≤ 2 ^ 32) :
    WP isa (.block K.select) s
      (SelPost K base s a ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64)) := by
  have hnw := hs.nowrap
  have htbe : K.tblBytes = 16 * K.M.n * K.H := rfl
  rw [TCombCfg.select, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (selSetup_ok K hs hptr hb hT htb) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  have h8₁ : s₁.gpr .ebx = BitVec.ofNat 32 a := by rw [k₁.1 _ (by decide), h8]
  have hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64 +
        BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16 := by
    intro e he c hc
    rw [k₁.2.2.1, k₁.2.2.2]
    refine VG.CallLay.inRegions_sub hreg ?_ (by omega)
    have := Nat.mul_le_mul_left (16 * K.M.n) (show e + 1 ≤ K.H by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  refine WP.mono (selPass_ok K hs₁ hn.2 hH (by omega) h8₁ (congrArg (BitVec.setWidth 64) x₁)
    hr hX (by omega)) fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have h8₂ : s₂.gpr .ebx = BitVec.ofNat 32 a := by rw [k₂.1 _ (by decide), h8₁]
  have h0₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [O₂.wordsVal h0xy (by omega), k₁.2.1, h0]
  refine WP.mono (selOne_ok K hs₂ (by omega) h8₂ hy hz hzero (by omega) (by omega) h0z hone h0₂)
    fun t ⟨ey, ez, k₃, U₃⟩ => ?_
  have W := accVal_word a₂
  rw [k₁.2.1] at W
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    U₃.word (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left h1]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_left ⟨h1, ha⟩]
    · rw [ite_eq_right h1]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_right (by omega)]
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left h1, ey, ite_eq_right (by omega)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega,
          W _ (by omega), ite_eq_left ⟨h1, ha⟩]
        rw [show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) =
          16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
    · rw [ite_eq_right h1, ey, ite_eq_left (by omega)]
  · rw [ez]; split <;> split <;> omega
  · exact (k₁.keeps.trans (k₂.mono (by decide))).trans k₃
  · have U₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.x + 8 * K.M.n, 8 * K.M.n)] s.mem s₂.mem := by
      rw [← k₁.2.1]
      exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega]; exact O₂.unch)
    rw [← hexy] at U₂
    exact (U₂.trans U₃).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.X86
