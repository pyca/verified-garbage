import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect

/-!
# The comb's sign: the exchange in `xmm`, and the negation in one correction

`swapFieldX` exchanges two slots under the mask `rcx` sixteen bytes at a time,
so one mask applies to half a field element at once (`swapFieldX_ok`, which is
`cswap_ok`'s statement), and `negField` negates a slot as `2p - [x]`, which
needs one correction whatever the four words are (`negField_ok`).
-/

-- The symbolic execution's `simp only` sets include register inequalities that
-- close conjuncts of the postcondition rather than rewrite the state.
set_option linter.unusedSimpArgs false

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519 (toFe)
open VG.Proof.X25519.X86_64 (off fe val4 Outside Scr Keeps F Op clob)
open VG.Impl.X25519.X86_64 (sc)

/-! ## Sixteen bytes as two words -/

/-- A read of `8 n` bits is the read of `n` bytes. -/
private theorem readW_eq_read (m : Mem) (a : Addr) (n : Nat) : m.readW a (8 * n) = m.read a n := by
  show (m.read a (8 * n / 8)).setWidth (8 * n) = m.read a n
  rw [show 8 * n / 8 = n by omega]
  exact BitVec.setWidth_eq _

/-- Byte `j` of the `n` bytes at `a`. -/
private theorem byte_readW (m : Mem) (a : Addr) {n j : Nat} (hj : j < n) :
    (m.readW a (8 * n)).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [readW_eq_read]
  exact VG.Mem.extractLsb'_read m a hj

/-- The low word of the 16 bytes at `a`. -/
theorem read128_lo (m : Mem) (a : Addr) : (m.readW a 128).setWidth 64 = m.readW a 64 := by
  symm
  show (m.read a 8).setWidth 64 = _
  rw [VG.Mem.read_eq_of_bytes (n := 8) (v := (m.readW a 128).setWidth 64) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · rw [← byte_readW m a (n := 16) (show j < 16 by omega)]
    ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
    rw [decide_eq_true (by omega : 8 * j + i < 64), Bool.true_and]

/-- The high word of the 16 bytes at `a`. -/
theorem read128_hi (m : Mem) (a : Addr) :
    (m.readW a 128).extractLsb' 64 64 = m.readW (a + BitVec.ofNat 64 8) 64 := by
  symm
  show (m.read (a + BitVec.ofNat 64 8) 8).setWidth 64 = _
  rw [VG.Mem.read_eq_of_bytes (n := 8) (v := (m.readW a 128).extractLsb' 64 64) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · rw [Offset.add_add, ← byte_readW m a (n := 16) (show 8 + j < 16 by omega)]
    ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
    rw [decide_eq_true (by omega : 8 * j + i < 64), Bool.true_and]
    congr 1
    omega

/-- Two slots hold the same field element if their halves hold the same bytes. -/
theorem fe_of_read128 {m m' : Mem} {base : Addr} {d d' : Nat}
    (h₀ : m'.readW (off base d) 128 = m.readW (off base d') 128)
    (h₁ : m'.readW (off base (d + 16)) 128 = m.readW (off base (d' + 16)) 128) :
    fe m' base d = fe m base d' := by
  have lo : ∀ (mm : Mem) (e : Nat), VG.Proof.X25519.X86_64.word mm base e =
      (mm.readW (off base e) 128).setWidth 64 := fun mm e => (read128_lo mm (off base e)).symm
  have hi : ∀ (mm : Mem) (e : Nat), VG.Proof.X25519.X86_64.word mm base (e + 8) =
      (mm.readW (off base e) 128).extractLsb' 64 64 := fun mm e => by
    show mm.readW (off base (e + 8)) 64 = _
    rw [read128_hi, off, off, Offset.add_add]
  have e24 : ∀ (mm : Mem) (e : Nat), VG.Proof.X25519.X86_64.word mm base (e + 24) =
      (mm.readW (off base (e + 16)) 128).extractLsb' 64 64 := fun mm e => by
    rw [show e + 24 = e + 16 + 8 by omega, hi mm (e + 16)]
  have e0 : VG.Proof.X25519.X86_64.word m' base d = VG.Proof.X25519.X86_64.word m base d' := by
    rw [lo m' d, lo m d', h₀]
  have e1 : VG.Proof.X25519.X86_64.word m' base (d + 8) =
      VG.Proof.X25519.X86_64.word m base (d' + 8) := by rw [hi m' d, hi m d', h₀]
  have e2 : VG.Proof.X25519.X86_64.word m' base (d + 16) =
      VG.Proof.X25519.X86_64.word m base (d' + 16) := by rw [lo m' (d + 16), lo m (d' + 16), h₁]
  have e3 : VG.Proof.X25519.X86_64.word m' base (d + 24) =
      VG.Proof.X25519.X86_64.word m base (d' + 24) := by rw [e24 m' d, e24 m d', h₁]
  simp only [fe, e0, e1, e2, e3]

/-! ## The exchange of two neighbouring slots -/

/-- `mask` and `cmask` are the same mask. -/
private theorem mask_eq_cmask (sw : Bool) : VG.Proof.X25519.X86_64.mask sw = cmask sw := by
  cases sw <;> rfl

/-- `x ⊕ ((x ⊕ y) ∧ m)` is `y` under an all-ones mask and `x` under a zero one. -/
private theorem sel_xor (x y : BitVec 128) (sw : Bool) :
    x ^^^ ((x ^^^ y) &&& cmask128 sw) = if sw then y else x := by
  cases sw
  · rw [show cmask128 false = 0 from rfl, show (if false then y else x) = x from rfl]
    ext i hi
    simp
  · rw [show cmask128 true = BitVec.allOnes 128 from rfl, BitVec.and_allOnes,
      show (if true then y else x) = y from rfl]
    ext i hi
    cases hb : x[i] <;> simp [hb]

/-- `y ⊕ ((x ⊕ y) ∧ m)` is `x` under an all-ones mask and `y` under a zero one. -/
private theorem sel_xor' (x y : BitVec 128) (sw : Bool) :
    y ^^^ ((x ^^^ y) &&& cmask128 sw) = if sw then x else y := by
  rw [BitVec.xor_comm x y]; exact sel_xor y x sw

/-- A 16-byte write read back. -/
private theorem readW_writeW_self128 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW a 128 = v := Mem.readW_writeW_self m a 16 v (by omega)

/-- The 16 bytes at `base + d` are readable. -/
private theorem rd128 {s : State} {base : Addr} (hs : Scratch s base) {d : Nat}
    (hd : d + 16 ≤ 8192) : InRegions (s.rd ++ s.wr) (off base d) 16 :=
  ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by have := hs.nowrap; omega)⟩

/-- The 16 bytes at `base + d` are writable. -/
private theorem wr128 {s : State} {base : Addr} (hs : Scratch s base) {d : Nat}
    (hd : d + 16 ≤ 8192) : InRegions s.wr (off base d) 16 :=
  ⟨_, hs.wr, Offset.contains_base _ hd (by have := hs.nowrap; omega)⟩

/-- `setXmm` keeps the symbols. -/
private theorem syms_setXmm (s : State) (r : XReg) (v : BitVec 128) :
    (s.setXmm r v).syms = s.syms := rfl

/-- The exchange's loads and masking: `xmm0` and `xmm1` hold the 16 bytes at
`d` and at `e`, exchanged if the mask in `xmm15` is all ones. -/
theorem swapPieceXPre_ok {s : State} {base : Addr} (hs : Scratch s base) {d e : Nat}
    (hd : d + 16 ≤ 8192) (he : e + 16 ≤ 8192) {sw : Bool} (hx : s.xmm .xmm15 = cmask128 sw) :
    WP isa (.block [.movdquLoad .xmm0 (sc d), .movdquLoad .xmm1 (sc e),
      .xop (.bin .movdqa .xmm2 .xmm0), .xop (.bin .pxor .xmm2 .xmm1),
      .xop (.bin .pand .xmm2 .xmm15), .xop (.bin .pxor .xmm0 .xmm2),
      .xop (.bin .pxor .xmm1 .xmm2)]) s fun t =>
      t.xmm .xmm0 = (if sw then s.mem.readW (off base e) 128
        else s.mem.readW (off base d) 128) ∧
      t.xmm .xmm1 = (if sw then s.mem.readW (off base d) 128
        else s.mem.readW (off base e) 128) ∧
      t.xmm .xmm15 = s.xmm .xmm15 ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have rdd := rd128 hs hd
  have rde := rd128 hs he
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, XBinOp.eval,
    State.load128, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, rdd, rde, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.xmm_setXmm_self, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, syms_setXmm,
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm0 = XReg.xmm1 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm0 = XReg.xmm2 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm1 = XReg.xmm0 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm15 = XReg.xmm0 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm15 = XReg.xmm1 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm15 = XReg.xmm2 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm1 = XReg.xmm2 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm2 = XReg.xmm0 by decide),
    RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm15 = XReg.xmm2 by decide)]
  rw [hx]
  refine ⟨sel_xor _ _ _, sel_xor' _ _ _, ?_⟩
  and_intros <;> trivial


/-- A 16-byte store. -/
theorem st128_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d + 16 ≤ 8192)
    (r : XReg) :
    WP isa (.block [.movdquStore (sc d) r]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.xmm r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm ∧ t.syms = s.syms := by
  have hw := wr128 hs hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hw, ite_true, Option.some.injEq, exists_eq_left']
  and_intros <;> trivial

/-- `swapPieceX`: the 16 bytes at `d` and at `e` exchanged under the mask in
`xmm15`. -/
theorem swapPieceX_ok {s : State} {base : Addr} (hs : Scratch s base) {d e : Nat}
    (hd : d + 16 ≤ 8192) (he : e + 16 ≤ 8192) (hde : d + 16 ≤ e) {sw : Bool}
    (hx : s.xmm .xmm15 = cmask128 sw) :
    WP isa (.block (swapPieceX d e)) s fun t =>
      t.mem.readW (off base d) 128 = (if sw then s.mem.readW (off base e) 128
        else s.mem.readW (off base d) 128) ∧
      t.mem.readW (off base e) 128 = (if sw then s.mem.readW (off base d) 128
        else s.mem.readW (off base e) 128) ∧
      Outside base d (e + 16 - d) s.mem t.mem ∧
      (∀ k, k + 16 ≤ 8192 → (k + 16 ≤ d ∨ (d + 16 ≤ k ∧ k + 16 ≤ e) ∨ e + 16 ≤ k) →
        t.mem.readW (off base k) 128 = s.mem.readW (off base k) 128) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm .xmm15 = s.xmm .xmm15 ∧
      t.syms = s.syms := by
  have hn := hs.nowrap
  have hsep : Mem.Sep (off base d) (128 / 8) (off base e) (128 / 8) :=
    Offset.sep base (Or.inl (by omega)) (by omega) (by omega)
  rw [show swapPieceX d e = [.movdquLoad .xmm0 (sc d), .movdquLoad .xmm1 (sc e),
      .xop (.bin .movdqa .xmm2 .xmm0), .xop (.bin .pxor .xmm2 .xmm1),
      .xop (.bin .pand .xmm2 .xmm15), .xop (.bin .pxor .xmm0 .xmm2),
      .xop (.bin .pxor .xmm1 .xmm2)] ++
      ([.movdquStore (sc d) .xmm0] ++ [.movdquStore (sc e) .xmm1]) from rfl,
    WP.block_append_iff]
  refine WP.mono (swapPieceXPre_ok hs hd he hx) fun u ⟨u0, u1, ux, ug, um, urd, uwr, usy⟩ => ?_
  have hsu : Scratch u base := ⟨by rw [ug]; exact hs.rdi, uwr ▸ hs.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (st128_ok hsu hd .xmm0) fun v ⟨vm, vg, vrd, vwr, vx, vsy⟩ => ?_
  have hsv : Scratch v base := ⟨by rw [vg]; exact hsu.rdi, vwr ▸ hsu.wr, hn⟩
  refine WP.mono (st128_ok hsv he .xmm1) fun t ⟨tm, tg, trd, twr, tx, tsy⟩ => ?_
  have hm : t.mem = (s.mem.writeW (off base d) (u.xmm .xmm0)).writeW (off base e) (u.xmm .xmm1) := by
    rw [tm, vm, um, vx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, Mem.readW_writeW_sep hsep (by omega), readW_writeW_self128, u0]
  · rw [hm, readW_writeW_self128, u1]
  · rw [hm]
    exact ((writeW128_outside s.mem base _ (by omega)).mono (Nat.le_refl _) (by omega)).trans
      ((writeW128_outside _ base _ (by omega)).mono (by omega) (by omega))
  · intro k hk hsep'
    rw [hm, Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by omega),
      Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by omega)]
  · rw [tg, vg, ug]
  · rw [trd, vrd, urd]
  · rw [twr, vwr, uwr]
  · rw [tx, vx]; exact ux
  · rw [tsy, vsy, usy]

/-- `swapFieldX`: the slots `a` and `b = a + 1` exchanged under the mask `rcx`,
as `swapFieldWide_ok` has it for `cswap`. -/
theorem swapFieldX_ok {s : State} {base : Addr} (hs : Scratch s base) (a b : Slot)
    (hab : b.val = a.val + 1) (ha : offset a + 64 ≤ 768) {sw : Bool}
    (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (swapFieldX (offset a))) s fun t =>
      Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have hb : offset b = offset a + 32 := by simp only [offset, hab]; omega
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  rw [swapFieldX, List.append_assoc, WP.block_append_iff]
  refine WP.mono (combDupMask_ok s (b := sw) (by rw [hm, mask_eq_cmask])) fun u ⟨ux, uk⟩ => ?_
  have hsu : Scratch u base := ⟨(uk.gpr _ List.not_mem_nil).trans hs.rdi, uk.wr ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (swapPieceX_ok hsu (sw := sw) (d := offset a) (e := offset a + 32)
    (by omega) (by omega) (by omega) ux) fun v ⟨v0, v1, vO, vE, vg, vrd, vwr, vx, vsy⟩ => ?_
  rw [uk.mem] at v0 v1 vE
  have hsv : Scratch v base := ⟨by rw [vg]; exact hsu.rdi, vwr ▸ hsu.wr, hs.nowrap⟩
  refine WP.mono (swapPieceX_ok hsv (sw := sw) (d := offset a + 16) (e := offset a + 48)
    (by omega) (by omega) (by omega) (by rw [vx]; exact ux)) fun t ⟨t0, t1, tO, tE, tg, trd, twr, _, tsy⟩ => ?_
  -- the four halves of the two slots, and the memory outside them
  have hv64 : Outside base (offset a) 64 s.mem v.mem :=
    fun x hx => (vO x (by omega)).trans (congrFun uk.mem x)
  have ht64 : Outside base (offset a) 64 v.mem t.mem := fun x hx => tO x (by omega)
  have hmem : Outside base (offset a) 64 s.mem t.mem := hv64.trans ht64
  have keep : Keep base s t := by
    refine ⟨fun r hr => ?_, ?_, ?_, fun x hx => hmem x (by
      have := a.isLt; simp only [offset] at *; omega)⟩
    · rw [tg, vg, uk.gpr r (by simp)]
    · rw [trd, vrd, uk.rd]
    · rw [twr, vwr, uk.wr]
  refine ⟨keep, ?_, ?_⟩
  · rw [tg, vg, uk.gpr _ (by simp)]
  · -- the four halves, and the slots elsewhere
    have ha0 : t.mem.readW (off base (offset a)) 128 =
        (if sw then s.mem.readW (off base (offset a + 32)) 128
        else s.mem.readW (off base (offset a)) 128) := by
      rw [tE (offset a) (by omega) (by omega), v0]
    have ha1 : t.mem.readW (off base (offset a + 16)) 128 =
        (if sw then s.mem.readW (off base (offset a + 48)) 128
        else s.mem.readW (off base (offset a + 16)) 128) := by
      rw [t0, vE (offset a + 48) (by omega) (by omega), vE (offset a + 16) (by omega) (by omega)]
    have hb0 : t.mem.readW (off base (offset a + 32)) 128 =
        (if sw then s.mem.readW (off base (offset a)) 128
        else s.mem.readW (off base (offset a + 32)) 128) := by
      rw [tE (offset a + 32) (by omega) (by omega), v1]
    have hb1 : t.mem.readW (off base (offset a + 48)) 128 =
        (if sw then s.mem.readW (off base (offset a + 16)) 128
        else s.mem.readW (off base (offset a + 48)) 128) := by
      rw [t1, vE (offset a + 16) (by omega) (by omega), vE (offset a + 48) (by omega) (by omega)]
    funext i
    have hswa : swapEnv a b sw (env s.mem base) a =
        (if sw then env s.mem base b else env s.mem base a) := by simp [swapEnv, hne]
    have hswb : swapEnv a b sw (env s.mem base) b =
        (if sw then env s.mem base a else env s.mem base b) := by simp [swapEnv, hne]
    have hswo : ∀ j : Slot, j ≠ a → j ≠ b → swapEnv a b sw (env s.mem base) j =
        env s.mem base j := fun j hja hjb => by simp [swapEnv, hja, hjb]
    by_cases hia : i = a
    · subst hia
      rw [hswa]
      cases sw
      · simp only [Bool.false_eq_true, ↓reduceIte] at ha0 ha1 ⊢
        exact congrArg toFe (fe_of_read128 ha0 ha1)
      · simp only [↓reduceIte] at ha0 ha1 ⊢
        simp only [env, hb]
        exact congrArg toFe (fe_of_read128 ha0 ha1)
    · by_cases hib : i = b
      · subst hib
        rw [hswb]
        cases sw
        · simp only [Bool.false_eq_true, ↓reduceIte] at hb0 hb1 ⊢
          simp only [env, hb]
          exact congrArg toFe (fe_of_read128 hb0 hb1)
        · simp only [↓reduceIte] at hb0 hb1 ⊢
          simp only [env, hb]
          exact congrArg toFe (fe_of_read128 hb0 hb1)
      · rw [hswo i hia hib]
        refine congrArg toFe (hmem.fe ?_ (by simp only [offset]; have := i.isLt; omega))
        have := i.isLt; have := a.isLt; have := b.isLt
        simp only [offset] at *
        rcases Nat.lt_trichotomy i.val a.val with h | h | h
        · left; omega
        · exact absurd (Fin.ext h) hia
        · rcases Nat.lt_trichotomy i.val b.val with h' | h' | h'
          · omega
          · exact absurd (Fin.ext h') hib
          · right; omega

/-! ## The negation in one correction -/

open VG.Spec.X25519 (P) in
/-- The constant `2p` in four words. -/
private theorem val4_twoP : val4 (BitVec.ofNat 64 (2 ^ 64 - 38)) (BitVec.allOnes 64)
    (BitVec.allOnes 64) (BitVec.allOnes 64) = 2 * P := by
  simp only [VG.Proof.X25519.X86_64.val4, BitVec.toNat_ofNat, BitVec.toNat_allOnes, P]
  norm_num

open VG.Spec.X25519 (P) in
/-- `negWords`: `r8`–`r11` is `2p - [x]`, which is `-[x]` modulo `p`, for any
four words at `x`. -/
theorem negWords_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat}
    (hx : VG.Proof.X25519.X86_64.Slot x) :
    WP isa (.block (negWords x)) s fun t =>
      (val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) + fe s.mem base x) % P = 0 ∧
      Keeps [.rax, .r8, .r9, .r10, .r11] s t := by
  have hw8 := VG.Proof.X25519.X86_64.ld_sc hs (d := x) (by omega)
  have hw9 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 8) (by omega)
  have hw10 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 16) (by omega)
  have hw11 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 24) (by omega)
  rw [negWords, WP.block_append_iff]
  refine WP.mono (show WP isa (.block
      [.movImm64 .r8 (BitVec.ofNat 64 (2 ^ 64 - 38)), .alu .sub .r8 (.mem (sc x)),
        .movImm64 .r9 (BitVec.allOnes 64), .alu .sbb .r9 (.mem (sc (x + 8))),
        .movImm64 .r10 (BitVec.allOnes 64), .alu .sbb .r10 (.mem (sc (x + 16))),
        .movImm64 .r11 (BitVec.allOnes 64), .alu .sbb .r11 (.mem (sc (x + 24))),
        .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun t =>
      ∃ β : Nat, β ≤ 1 ∧
        val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) + fe s.mem base x =
          2 * P + 2 ^ 256 * β ∧
        (t.gpr .rax).toNat = 38 * β ∧
        Keeps [.rax, .r8, .r9, .r10, .r11] s t from ?_)
    fun u ⟨β, hβ, he, hr, hk⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
      VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hw8, hw9, hw10, hw11,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
      RegUpd.cf_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_true, ite_false,
      reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨_, Bool.toNat_le _, ?_, VG.Proof.X25519.X86_64.mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
    · have e := VG.Proof.X25519.X86_64.chain_sub (BitVec.ofNat 64 (2 ^ 64 - 38))
        (BitVec.allOnes 64) (BitVec.allOnes 64) (BitVec.allOnes 64)
        (VG.Proof.X25519.X86_64.word s.mem base x)
        (VG.Proof.X25519.X86_64.word s.mem base (x + 8))
        (VG.Proof.X25519.X86_64.word s.mem base (x + 16))
        (VG.Proof.X25519.X86_64.word s.mem base (x + 24))
      rw [val4_twoP] at e
      exact e
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2, ite_false]
  · have hsu := hs.of_keeps hk (by decide)
    refine WP.mono (VG.Proof.X25519.X86_64.borrow38_ok u) fun t ⟨c, hc, he2, _, hk2⟩ => ?_
    refine ⟨?_, hk.trans (hk2.mono (by simp))⟩
    have b8 := (t.gpr .r8).isLt
    have b9 := (t.gpr .r9).isLt
    have b10 := (t.gpr .r10).isLt
    have b11 := (t.gpr .r11).isLt
    have c8 := (u.gpr .r8).isLt
    have c9 := (u.gpr .r9).isLt
    have c10 := (u.gpr .r10).isLt
    have c11 := (u.gpr .r11).isLt
    have hfe : fe s.mem base x < 2 ^ 256 := by
      have := (VG.Proof.X25519.X86_64.word s.mem base x).isLt
      have := (VG.Proof.X25519.X86_64.word s.mem base (x + 8)).isLt
      have := (VG.Proof.X25519.X86_64.word s.mem base (x + 16)).isLt
      have := (VG.Proof.X25519.X86_64.word s.mem base (x + 24)).isLt
      simp only [VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.val4]
      omega
    simp only [VG.Proof.X25519.X86_64.val4] at he he2 ⊢
    rw [hr] at he2
    -- `c = 0`: the difference stays above `38 β`
    have hc0 : c = 0 := by simp only [P] at he; omega
    subst hc0
    simp only [P] at he ⊢
    omega

/-- The selection: `r8`–`r11` keep the negation if the mask `rcx` is all ones,
and are the words at `x` otherwise (`cmove`, since `test` sets `ZF` exactly
for a zero mask). -/
theorem negSel_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat}
    (hx : VG.Proof.X25519.X86_64.Slot x) {sw : Bool}
    (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block [.alu .test .rcx (.reg .rcx), .cmov .e .r8 (.mem (sc x)),
      .cmov .e .r9 (.mem (sc (x + 8))), .cmov .e .r10 (.mem (sc (x + 16))),
      .cmov .e .r11 (.mem (sc (x + 24)))]) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        (if sw then val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
        else fe s.mem base x) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have hw8 := VG.Proof.X25519.X86_64.ld_sc hs (d := x) (by omega)
  have hw9 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 8) (by omega)
  have hw10 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 16) (by omega)
  have hw11 := VG.Proof.X25519.X86_64.ld_sc hs (d := x + 24) (by omega)
  have hz : ∀ b : Bool, (VG.Proof.X25519.X86_64.mask b &&& VG.Proof.X25519.X86_64.mask b == 0) =
      !b := by decide
  cases sw
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval,
      State.load64, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hm, hz, hw8, hw9, hw10, hw11,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, Bool.not_false, Bool.not_true, ite_true,
      ite_false, Bool.false_eq_true, reduceCtorEq, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval,
      State.load64, VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hm, hz, hw8, hw9, hw10, hw11,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, Bool.not_false, Bool.not_true, ite_true,
      ite_false, Bool.false_eq_true, reduceCtorEq, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

open VG.Spec.X25519 (P) in
/-- `negField`: the field element at `x` negated if the mask `rcx` is all
ones, and unchanged otherwise. -/
theorem negField_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat}
    (hx : VG.Proof.X25519.X86_64.Slot x) {sw : Bool}
    (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (negField x)) s fun t =>
      Op base x s t ∧ t.gpr .rcx = s.gpr .rcx ∧
      F t.mem base x = (if sw then -(F s.mem base x) else F s.mem base x) := by
  rw [negField, List.append_assoc, WP.block_append_iff]
  refine WP.mono (negWords_ok hs hx) fun u ⟨hu, hk⟩ => ?_
  have hsu := hs.of_keeps hk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (negSel_ok hsu hx (sw := sw) (by rw [hk.1 .rcx (by decide), hm]))
    fun v ⟨hv, hk2⟩ => ?_
  have hsv := hsu.of_keeps hk2 (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.store4_ok hsv hx) fun t ⟨tm, tg, trd, twr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h2 : r ∉ [Reg.r8, Reg.r9, Reg.r10, Reg.r11] := by
      simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]
    have h1 : r ∉ [Reg.rax, Reg.r8, Reg.r9, Reg.r10, Reg.r11] := by
      simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]
    rw [tg, hk2.1 r h2, hk.1 r h1]
  · rw [trd, hk2.2.2.1, hk.2.2.1]
  · rw [twr, hk2.2.2.2, hk.2.2.2]
  · rw [tm, hk2.2.1, hk.2.1]
    exact VG.Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _
  · rw [tg, hk2.1 .rcx (by decide), hk.1 .rcx (by decide)]
  · rw [show F t.mem base x = VG.Proof.X25519.toFe
      (val4 (v.gpr .r8) (v.gpr .r9) (v.gpr .r10) (v.gpr .r11)) from by
      rw [F, tm, VG.Proof.X25519.X86_64.fe_st4 _ _ (by omega)], hv, hk.2.1]
    cases sw
    · simp only [Bool.false_eq_true, ↓reduceIte, F]
    · simp only [↓reduceIte, F]
      have h0 : VG.Proof.X25519.toFe (val4 (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)) =
          VG.Proof.X25519.toFe 0 - VG.Proof.X25519.toFe (fe s.mem base x) :=
        VG.Proof.X25519.toFe_sub (by simp only [hu, Nat.zero_mod])
      rw [h0, VG.Proof.X25519.toFe_zero, zero_sub]

/-- `negField_ok` for the whole scratch (the comb's regions), by running it on
the first 4096 bytes, as `swapFieldWide_ok` does for `cswap`. -/
theorem negFieldWide_ok {s : State} {base : Addr} (hs : Scratch s base) {x : Nat}
    (hx : VG.Proof.X25519.X86_64.Slot x) {sw : Bool}
    (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask sw) :
    WP isa (.block (negField x)) s fun t =>
      Op base x s t ∧ t.gpr .rcx = s.gpr .rcx ∧
      F t.mem base x = (if sw then -(F s.mem base x) else F s.mem base x) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hop, hc, hv⟩ := negField_ok hn hx hm
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hop.gpr, rfl, rfl, hop.mem⟩, hc, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd,
    State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
