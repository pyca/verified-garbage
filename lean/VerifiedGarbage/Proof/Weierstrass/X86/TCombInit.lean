import VerifiedGarbage.Proof.Weierstrass.X86.TCombLoop
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

theorem tcombW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)], K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ptr hL w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.ptr_bits; dsimp only; omega

/-- Zero stored to the `m` words at `o`, from `rax = 0`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .eax = 0)
    {o : Nat} : ∀ m, o + 4 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => .store (sc (o + 4 * i)) .eax)) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (4 * m) s.mem s'.mem ∧
        ∀ d < 4 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega)⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz m (by omega)) fun s₁ ⟨k₁, O₁, z₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have hrax : s₁.gpr .eax = 0 := (k₁.gpr _ (by simp)).trans hz
    simp only [List.map_cons, List.map_nil]
    refine wp_storeS (hs₁.ea (d := o + 4 * m) (by omega)) (hs₁.write (d := o + 4 * m) (n := 4) (by omega))
      fun s₂ u₂ => WP.block_nil ?_
    have Ow : Outside base (o + 4 * m) 4 s₁.mem s₂.mem := by
      rw [u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨k₁.trans (u₂.keeps _), fun x hx => (Ow x (by omega)).trans (O₁ x (by omega)),
      fun d hd => ?_⟩
    by_cases hd' : d < 4 * m
    · rw [Ow _ (by rw [ofs_off0 base (by omega)]; omega)]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 4 * m) = BitVec.ofNat 64 (d - 4 * m) := by
        simp only [off]; rw [show o + d = o + 4 * m + (d - 4 * m) by omega, Offset.add_ofNat_add_sub]
      rw [u₂.mem, hrax]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 4 * m < 2 ^ 64 by omega), show d - 4 * m < 32 / 8 by omega,
        ↓reduceIte]
      simp

theorem zeroEax_ok (s : State) :
    WP isa (.block [.mov .eax (.imm 0)]) s fun t => t.gpr .eax = 0 ∧ CKeeps [.eax] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

theorem movEsi_ok (s : State) {j : Nat} (_hj : j < 2^31) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 j))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 j ∧ CKeeps [.esi] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

/-- `[k]G` into `A`, for `k < 2^kbytes` whose bits are the table at `K.bits`;
only `powClob` and `tcombW` change. -/
theorem tcombInit_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.initCore) s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ size := fun x hx =>
    hL.comb.lay.le x (combWs_slots _ x hx)
  have b64 : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have axy := hL.comb.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have axz := hL.comb.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have ayz := hL.comb.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  dsimp only [TCombCfg.toComb] at axy axz ayz
  have hsl : ∀ x ∈ combWs K.toComb, K.bits + K.kbytes + 4 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ (combWs_slots _ x hx))
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hJ31 : K.J < 2 ^ 31 := by omega
  have e : K.initCore = setConst K.M.n K.A.x K.start.1 ++ (setConst K.M.n K.A.y K.start.2 ++
      (setConst K.M.n K.A.z K.one ++ ([.mov .eax (.imm 0)] ++ ((List.range K.zw).map
        (fun i => .store (sc (K.bits + K.kbytes + 4 * i)) .eax) ++
          [.mov .esi (.imm (BitVec.ofNat 32 K.J))])))) := by
    unfold TCombCfg.initCore
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  have hlt : ∀ {x}, x < C.p → x < 2 ^ (64 * K.M.n) := fun h => Nat.lt_trans h hpn
  refine WP.mono (setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) (le _ (by tcomb_mem))
    (hlt hV.start_lt.1)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) (le _ (by tcomb_mem))
    (hlt hV.start_lt.2)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) (le _ (by tcomb_mem))
    (hlt hV.one_lt)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroEax_ok s₃) fun s₄ ⟨z₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zstores_ok hs₄ z₄ K.zw hL.bits) fun s₅ ⟨k₅, O₅, z₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by simp)
  refine WP.mono (movEsi_ok s₅ hJ31) fun s₆ ⟨b₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  have U₃ : Unch base (combWx K) s.mem s₃.mem :=
    (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [combWx, combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hw ⊢
      grind
  have U₆ : Unch base (combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)]) s.mem s₆.mem := by
    rw [m₆]
    refine (U₃.trans (show Unch base [(K.bits + K.kbytes, 4 * K.zw)] s₃.mem s₅.mem by
      rw [← k₄.2.1]; exact O₅.unch)).mono fun _ hw => hw
  have U₆full : Unch base (tcombW K) s.mem s₆.mem := U₆
  have hmo := tcombW_mo hL hM
  -- `A`, apart from the cleared words.
  have hA5 : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [m₆, O₅.wordsVal (by have := hsl x hxs; omega) (b64 x hxs), k₄.2.1]
  have vx : wordsVal s₆.mem base K.A.x K.M.n = K.start.1 := by
    rw [hA5 _ (by simp), O₃.wordsVal axz (b64 _ (by tcomb_mem)), O₂.wordsVal axy (b64 _ (by tcomb_mem)), e₁]
  have vy : wordsVal s₆.mem base K.A.y K.M.n = K.start.2 := by
    rw [hA5 _ (by simp), O₃.wordsVal ayz (b64 _ (by tcomb_mem)), e₂]
  have vz : wordsVal s₆.mem base K.A.z K.M.n = K.one := by rw [hA5 _ (by simp), e₃]
  have I₆ : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s₆ K.J := by
    refine ⟨hs₅.of_keeps k₆.keeps (by decide), b₆, ?_, U₆full, hM.unch U₆full hmo (by omega), ?_, ?_, fun t ht => ?_, ?_,
      by rw [unch_read32 U₆ (by have := hL.ptr_le; omega) (tcombW_ptr hL)]; exact hF.tsym⟩
    · have c : ∀ r ∈ [Reg.eax], r ∈ powClob := by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
      exact ((((k₁.mono c).trans (k₂.mono c)).trans (k₃.mono c)).trans ((CKeeps.regs k₄).mono c)).trans
        ((k₅.mono fun r hr => absurd hr List.not_mem_nil).trans ((CKeeps.regs k₆).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..))
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hV.start_lt.1
      · rw [vy]; exact hV.start_lt.2
      · rw [vz]; exact hV.one_lt
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, hV.one, combEW_top]
      exact hV.start
    · by_cases htk : t < K.kbytes
      · rw [U₆full.byte (fun w hw => by
          rcases List.mem_append.mp hw with hw | hw
          · exact combW_bits hL ht w hw
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl
            dsimp only; omega)
          (by omega_using [hbz, hzw, ht, hn])]
        exact hF.bits t htk
      · have := z₅ (t - K.kbytes) (by omega)
        rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega] at this
        rw [m₆, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
          (Nat.pow_le_pow_right (by decide) (by omega)))]
        rfl
    · exact TblMem.of_unch hF.tbl (by rw [k₆.2.2.1, k₆.2.2.2, k₅.rd, k₅.wr, k₄.2.2.1, k₄.2.2.2, k₃.rd,
        k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]) U₆full (tcombW_size hL hM) hF.out
  exact I₆

/-- `[k]G` from initialization and the complete-addition loop. -/
theorem tcombCore_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.seq (.block K.initCore) (.loop K.step .ne)) s fun s' => KeepRegs powClob s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  refine WP.seq (WP.mono (tcombInit_ok hL hV hpn hs hM hF) fun s' I => ?_)
  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (fun j s' h1 h2 hi => tstep_ok hL hC hM3 hG hV hpn hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I


end VG.Proof.Weierstrass.X86
