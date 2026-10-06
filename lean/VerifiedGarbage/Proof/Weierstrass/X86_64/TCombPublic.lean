import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect

/-! Direct table lookup when the comb scalar is public. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem publicAddress_ok (K : TCombCfg) (s : State) {j a : Nat} {T : Addr}
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (hT : s.syms K.tsym = T) (hH : K.H < 2 ^ 31) (hn : K.M.n ≤ 14) (ha : a ≤ K.H) :
    WP isa (.block K.publicAddress) s fun t =>
      t.gpr .rdx = T + BitVec.ofNat 64 (j * K.tblBytes + 16 * K.M.n * (a - 1)) ∧
      Keeps [.rax, .rcx, .rdx] s t ∧ t.xmm = s.xmm ∧ t.syms = s.syms := by
  have hn' : 16 * K.M.n < 2 ^ 31 := by omega
  subst hT
  crun [TCombCfg.publicAddress, hb, h8, imm32_eq hH, imm32_eq hn', RegUpd.cf_setReg, RegUpd.cf_setFlags]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]
    rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show K.H < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 16 * K.M.n < 2 ^ 64 by omega)]
    simp only [TCombCfg.tblBytes]
    simp only [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl,
      show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    have sat : ((2 ^ 64 - 1 + a) % 2 ^ 64 +
        (BitVec.setWidth 64 (BitVec.ofBool (decide (a < 1)))).toNat) % 2 ^ 64 = a - 1 := by
      by_cases h : a = 0
      · subst a; decide
      · have h' : ¬ a < 1 := by omega
        simp only [decide_eq_false h']
        change ((2 ^ 64 - 1 + a) % 2 ^ 64 + 0) % 2 ^ 64 = a - 1
        omega
    rw [sat]
    have he : (j * K.H + (a - 1)) * (16 * K.M.n) =
        j * (16 * K.M.n * K.H) + 16 * K.M.n * (a - 1) := by grind
    rw [← he]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]

/-- Read one coordinate pair and mask a zero digit. -/
theorem publicLoadStep_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {c : Nat} (hc : c < 14)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * c)) 16) :
    WP isa (.block [.movdquLoad (selAcc c) (tblAt (16 * c)),
      .xop (.bin .pand (selAcc c) .xmm15)]) s fun t =>
      t.xmm (selAcc c) = s.mem.readW (X + BitVec.ofNat 64 (16 * c)) 128 &&& s.xmm .xmm15 ∧
      XKeep [] (· = selAcc c) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_tblAt, hx, State.load128, hr,
    ite_true, Option.map_some, XOp.exec, XBinOp.eval, RegUpd.xmm_setXmm_self,
    RegUpd.xmm_setXmm_of_ne _ _ (Ne.symm (selAcc_ne c hc).2), Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]

/-- Load all pairs before writing any scratch memory. -/
theorem publicLoadSteps_ok {n : Nat} (hn : n ≤ 14) {X : Addr} :
    ∀ k ≤ n, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * c)) 16) →
    WP isa (.block ((List.range k).flatMap fun c =>
      [.movdquLoad (selAcc c) (tblAt (16 * c)), .xop (.bin .pand (selAcc c) .xmm15)])) s fun t =>
      (∀ c < 14, t.xmm (selAcc c) = if c < k then
        s.mem.readW (X + BitVec.ofNat 64 (16 * c)) 128 &&& s.xmm .xmm15 else s.xmm (selAcc c)) ∧
      XKeep [] (fun r => ∃ c < n, r = selAcc c) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun _ _ => by simp, XKeep.refl _ _ _⟩
  | k + 1, hk, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (publicLoadSteps_ok hn k (by omega) s hx hr) fun s₁ ⟨a₁,k₁⟩ => ?_
    have h15 : s₁.xmm .xmm15 = s.xmm .xmm15 := k₁.xmm _ (by
      rintro ⟨c,hc,h⟩; exact (selAcc_ne c (by omega)).2 h.symm)
    refine WP.mono (publicLoadStep_ok s₁ ((k₁.gpr _ List.not_mem_nil).trans hx) (c := k) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega))) fun t ⟨a₂,k₂⟩ => ⟨fun c hc => ?_, ?_⟩
    · by_cases hck : c = k
      · subst hck
        rw [a₂, h15, k₁.mem, ite_eq_left (Nat.lt_succ_self _)]
      · rw [k₂.xmm _ (fun h => hck (selAcc_inj c hc k (by omega) h)), a₁ c hc]
        by_cases hlt : c < k
        · simp only [hlt, show c < k + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < k + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => ⟨k, by omega, h⟩)

theorem publicLoad_ok (K : TCombCfg) {s : State} {base X : Addr} {size : Nat}
    (hs : Scr s base size) (hn : K.M.n ≤ 14) (hx : s.gpr .rdx = X)
    (hr : ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * c)) 16)
    (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block K.publicLoad) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 =
        s.mem.readW (X + BitVec.ofNat 64 (16 * c)) 128 &&& s.xmm .xmm15) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [] s t := by
  rw [TCombCfg.publicLoad, WP.block_append_iff]
  refine WP.mono (publicLoadSteps_ok hn K.M.n (Nat.le_refl _) s hx hr) fun s₁ ⟨a₁,k₁⟩ => ?_
  refine WP.mono (storeAcc_ok (o := K.E.x) K.M.n s₁ (hs.of_keepRegs
    ⟨k₁.gpr,k₁.rd,k₁.wr⟩ (by decide)) hE) fun t ⟨a₂,O₂,g₂,r₂,w₂,_⟩ => ?_
  exact ⟨fun c hc => by rw [a₂ c hc, a₁ c (by omega), ite_eq_left hc],
    by rw [← k₁.mem]; exact O₂,
    ⟨fun r hr => by rw [g₂, k₁.gpr r hr], by rw [r₂,k₁.rd], by rw [w₂,k₁.wr]⟩⟩

theorem publicMask_ok {s : State} {a : Nat} (ha : a < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block TCombCfg.publicMask) s fun t =>
      t.xmm .xmm15 = bmask128 (!(decide (a = 0))) ∧ Keeps [.rcx] s t := by
  rw [TCombCfg.publicMask, WP.block_append_iff]
  refine WP.mono (eqMask_ok s (v := 0) (by decide) ha h8) fun s₁ ⟨m₁,k₁,_⟩ => ?_
  rw [show ([.alu .xor .rcx (.imm (-1)), .xop (.movq .xmm15 .rcx),
    .xop (.bin .punpcklqdq .xmm15 .xmm15)] : List Instr) =
    [.alu .xor .rcx (.imm (-1))] ++
      [.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)] from rfl,
    WP.block_append_iff]
  refine WP.mono (notMask_ok s₁ m₁) fun s₂ ⟨m₂,k₂,_⟩ => ?_
  refine WP.mono (dupMask_ok s₂ m₂) fun t ⟨m₃,k₃⟩ => ?_
  exact ⟨m₃, (k₁.trans k₂).trans ⟨fun r _ => k₃.gpr r List.not_mem_nil,k₃.mem,k₃.rd,k₃.wr⟩⟩

/-- The direct lookup produces the same coordinate pairs as the full scan. -/
theorem publicPrefix_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hn : K.M.n ≤ 14) (hH : K.H < 2 ^ 31)
    {j a : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ K.H) (hT : s.syms K.tsym = T)
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) K.tblBytes)
    (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block (K.publicAddress ++ TCombCfg.publicMask ++ K.publicLoad)) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 =
        accVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n) (16 * ·) a K.H c) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [.rax,.rcx,.rdx] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (publicAddress_ok K s hb h8 hT hH hn ha) fun s₁ ⟨x₁,k₁,_,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (publicMask_ok (by omega) ((k₁.1 _ (by decide)).trans h8)) fun s₂ ⟨m₂,k₂⟩ => ?_
  have hx₂ := (k₂.1 .rdx (by decide)).trans x₁
  have h0 : 0 < K.H := Nat.two_pow_pos _
  have ha' : a - 1 < K.H := by omega
  have htb : K.tblBytes ≤ 224 * 2 ^ 31 :=
    Nat.mul_le_mul (show 16 * K.M.n ≤ 224 by omega) (Nat.le_of_lt hH)
  have hr : ∀ c < K.M.n, InRegions (s₂.rd ++ s₂.wr)
      (T + BitVec.ofNat 64 (j * K.tblBytes + 16 * K.M.n * (a - 1)) + BitVec.ofNat 64 (16 * c)) 16 := by
    intro c hc
    rw [k₂.2.2.1,k₂.2.2.2,k₁.2.2.1,k₁.2.2.2,
      BitVec.ofNat_add, BitVec.add_assoc, Offset.add_add, ← BitVec.add_assoc]
    refine VG.CallLay.inRegions_sub hreg ?_ (by omega)
    have := Nat.mul_le_mul_left (16 * K.M.n) (show a - 1 + 1 ≤ K.H by omega)
    simp only [Nat.mul_add, Nat.mul_one] at this
    change _ ≤ 16 * K.M.n * K.H
    omega
  refine WP.mono (publicLoad_ok K ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)) hn hx₂ hr hE)
    fun t ⟨v₃,O₃,k₃⟩ => ?_
  refine ⟨fun c hc => ?_, ?_, ((Keeps.regs k₁).trans ((Keeps.regs k₂).mono (by decide))).trans
    (k₃.mono (by decide))⟩
  · rw [v₃ c hc,m₂,k₂.2.1,k₁.2.1]
    by_cases hz : a = 0
    · subst a; simp [bmask128,accVal]
    · have h1 : 1 ≤ a := by omega
      simp only [hz, decide_false, Bool.not_false, bmask128, ite_true, BitVec.and_allOnes,
        accVal, h1, ha, and_self]
      rw [BitVec.ofNat_add, BitVec.add_assoc, Offset.add_add, BitVec.add_assoc]
  · rw [← k₁.2.1, ← k₂.2.1]; exact O₃

theorem selectPublic_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 14) (hH : K.H < 2 ^ 31)
    (hexy : K.E.y = K.E.x + 8 * K.M.n) (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    {j a : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (ha : a ≤ K.H) (hT : s.syms K.tsym = T)
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) K.tblBytes) :
    WP isa (.block K.selectPublic) s (SelPost K base s a (T + BitVec.ofNat 64 (j * K.tblBytes))) := by
  have hnw := hs.nowrap
  rw [TCombCfg.selectPublic, WP.block_append_iff]
  refine WP.mono (publicPrefix_ok K hs hn.2 hH hb h8 ha hT hreg (by omega))
    fun s₂ ⟨a₂,O₂,k₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  have h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [k₂.gpr _ (by decide), h8]
  refine WP.mono (selOne_ok K hs₂ (by omega) h8₂ hy hz (by omega)) fun t ⟨ey, ez, k₃, U₃, _⟩ => ?_
  have W := accVal_word a₂
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    U₃.word (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · have hyw : ∀ i < K.M.n, word s₂.mem base (K.E.y + 8 * i) =
        if 1 ≤ a ∧ a ≤ K.H then word s.mem (T + BitVec.ofNat 64 (j * K.tblBytes))
          (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else 0 := fun i hi => by
      rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega, W _ (by omega),
        show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) = 16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩),
          decide_eq_false (show ¬ a = 0 by omega), bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          decide_eq_true (show a = 0 by omega), bv_and_or_true, bv_or_zero]
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ez i hi, decide_eq_false (show ¬ a = 0 by omega), Bool.not_false, bv_and_true]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [ez i hi, decide_eq_true (show a = 0 by omega), Bool.not_true, bv_and_false]
  · exact k₂.trans (k₃.mono (by decide))
  · have U₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.x + 8 * K.M.n, 8 * K.M.n)] s.mem s₂.mem := by
      exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega]; exact O₂.unch)
    rw [← hexy] at U₂
    exact (U₂.trans U₃).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h <;> simp [h]

theorem selectChoice_ok (publicLookup : Bool) (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 31)
    (hexy : K.E.y = K.E.x + 8 * K.M.n) (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    {j a : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (ha : a ≤ K.H) (hT : s.syms K.tsym = T)
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) K.tblBytes) :
    WP isa (.block (if publicLookup then K.selectPublic else K.select)) s (SelPost K base s a (T + BitVec.ofNat 64 (j * K.tblBytes))) := by
  cases publicLookup
  · exact select_ok K hs hn hH htb hexy hy hz hxz hone hb h8 ha hT hreg
  · exact selectPublic_ok K hs hn hH hexy hy hz hxz hone hb h8 ha hT hreg

end VG.Proof.Weierstrass.X86_64
