import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Step

/-!
# The `zmm` comb: a step of the loop

Step `j` adds the entry of table `j` for the odd digit `d_{2j+1}` to half 0
(`A`) and for the even digit `d_{2j}` to half 1 (`B`): after the 26 steps,
`A = [G + Σ d_{2j+1} 1024^j]B` and `B = [G + Σ d_{2j} 1024^j]B`.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM carry)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vnegBody vadd)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr mq)
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-! ## The sum -/

/-- An entry of the selection, negated for a negative digit, added to a point. -/
theorem entry_rep {P : Spec.Ed25519.Point} {v : ℤ} (hP : Rep P (v • baseAff)) (S i : Nat) {j : Nat}
    (hj : j < 26) :
    Rep (vAddPt P (negIf (decide (nib S i < 16)) (selEntry j (mag (nib S i)))))
      ((sdig S i * 1024 ^ j + v) • baseAff) := by
  have hmag : mag (nib S i) < 17 := by unfold mag nib; split <;> omega
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok j (mag (nib S i)) hj hmag
  have hcc : selEntry j (mag (nib S i)) = cache q₀ := by
    rw [← hq₀, selEntry, ← combCached_T j (mag (nib S i))]; rfl
  let q := if nib S i < 16 then negPoint q₀ else q₀
  have hneg : negIf (decide (nib S i < 16)) (cache q₀) = cache q := by
    by_cases hlt : nib S i < 16
    · simp only [hlt, decide_true, negIf, ↓reduceIte, q]
      exact VG.Proof.Ed25519.X86_64.negCached_cache q₀
    · simp only [hlt, decide_false, negIf, Bool.false_eq_true, ↓reduceIte, q]
  have hrq : Rep q ((sdig S i * 1024 ^ j) • baseAff) := by
    by_cases hlt : nib S i < 16
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S i * 1024 ^ j = -(((mag (nib S i) * 1024 ^ j : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : nib S i ≤ 16)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S i * 1024 ^ j = (((mag (nib S i) * 1024 ^ j : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 16 ≤ nib S i)]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  rw [hcc, hneg, vAddPt_cache, add_smul, add_comm]
  exact pointAdd_rep hP hrq


/-! ## The invariant -/

/-- The offsets the loop writes: the rows of the window, the sign's mask, `SGA` and `SGB`. -/
def ZChg (q : Nat) : Prop := InZ q ∨ DigOff q

/-- What the loop needs of the state `s₀` it starts from. -/
structure ZLoopPre (s₀ : State) (b T : Addr) (S : Nat) : Prop where
  scratch : Scratch s₀ b
  zok : ZOK b s₀
  hconsts : ∀ h < 2, EConsts (Zmm.half b h s₀).mem b
  consts : EConsts s₀.mem b
  k2 : ∀ h < 2, VG.Proof.X25519.X86_64.F s₀.mem b (ZK2 + 32 * h) = 2
  bits : ∀ q < 256, s₀.mem (off b (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  tbl : CombTbl s₀ T
  far : TblFar b T

/-- What the loop keeps of `s₀`: the registers but `rbx`, `rsi` and `clob` (`r11` kept), the
regions, the statics, and the memory but at `ZChg`. -/
structure ZFrame (s₀ : State) (b : Addr) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ clob → s.gpr r = s₀.gpr r
  r11 : s.gpr .r11 = s₀.gpr .r11
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : ∀ a, ¬ ZChg (ofs b a) → s.mem a = s₀.mem a
  syms : s.syms = s₀.syms

theorem ZFrame.refl (s₀ : State) (b : Addr) : ZFrame s₀ b s₀ :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

theorem ZFrame.scratch {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s)
    (hr : s.gpr .rdi = b) : Scratch s b :=
  ⟨hr, by rw [h.wr]; exact hp.scratch.wr, hp.scratch.nowrap⟩

theorem ZFrame.byte {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) {d : Nat}
    (hd : ¬ ZChg d) (hd' : d < 2 ^ 64) : s.mem (b + BitVec.ofNat 64 d) = s₀.mem (b + BitVec.ofNat 64 d) :=
  h.mem _ (by simp only [ofs]; rw [off_ofNat _ hd']; exact hd)

theorem ZFrame.readW {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) {d w : Nat}
    (hd : ∀ i < w / 8, ¬ ZChg (d + i)) (hd' : d + w / 8 < 2 ^ 64) :
    s.mem.readW (b + BitVec.ofNat 64 d) w = s₀.mem.readW (b + BitVec.ofNat 64 d) w :=
  Mem.readW_congr fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]; exact h.byte (hd i hi) (by omega)

theorem ZFrame.zok {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s)
    (hr : s.gpr .rdi = b) : ZOK b s :=
  ⟨hr, by rw [h.wr]; exact hp.scratch.wr, hp.scratch.nowrap, fun sel hs i hi => by
    have hm : ∀ sel ∈ blendSels, ZMASK ≤ maskRow sel ∧ maskRow sel + 64 ≤ 6016 := by decide
    have := hm sel hs
    rw [h.readW (fun q hq => by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK at *; omega) (by omega)]
    exact hp.zok.masks sel hs i hi⟩

theorem ZFrame.k2 {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) :
    ∀ h' < 2, ∀ k < 4, s.mem.readW (b + BitVec.ofNat 64 (ZK2 + 32 * h' + 8 * k)) 64 =
      s₀.mem.readW (b + BitVec.ofNat 64 (ZK2 + 32 * h' + 8 * k)) 64 :=
  fun h' hh k hk => h.readW (fun q hq => by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZK2 ZB at *; omega)
    (by unfold ZK2; omega)

theorem ZFrame.bits {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    ∀ q < 256, s.mem (off b (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun q hq => by
  rw [h.mem _ (by rw [bits_far hq]; unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega)]
  exact hp.bits q hq

theorem ZFrame.keep {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) : PowersKeep b 56 7368 s₀ s :=
  ⟨fun r h1 h2 h3 => h.gpr r h1 h2 h3, h.rd, h.wr, fun p _ hp => h.mem p (by
    unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega)⟩

theorem ZFrame.tbl {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    CombTbl s T :=
  hp.tbl.keep hp.far h.keep h.syms

theorem ZFrame.consts {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    EConsts s.mem b :=
  hp.consts.of_mq fun d h1 h2 => h.readW (fun q hq => by
    unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega) (by omega)

/-- The loop's invariant after `j` steps, with the points `[vA]B` and `[vB]B` in the halves. -/
structure ZInv (s₀ : State) (b : Addr) (j : Nat) (vA vB : ℤ) (s : State) : Prop where
  bound : j ≤ 26
  rdi : s.gpr .rdi = b
  counter : s.gpr .rbx = BitVec.ofNat 64 j
  frame : ZFrame s₀ b s
  hconsts : ∀ h < 2, EConsts (Zmm.half b h s).mem b
  small : ∀ h < 2, Small (Zmm.half b h s)
  valA : Rep (lanePt (Zmm.half b 0 s)) (vA • baseAff)
  valB : Rep (lanePt (Zmm.half b 1 s)) (vB • baseAff)

/-! ## Small blocks -/

theorem movRdx_ok (s : State) {j : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r9)]) s fun t => t.gpr .rdx = BitVec.ofNat 64 j ∧ Keeps [.rdx] s t ∧
      (∀ r i, t.zlane r i = s.zlane r i) ∧ t.syms = s.syms := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, h9, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem rbxNext26_ok (s : State) (n : Nat) (hn : n < 26) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 26)) ∧ Keeps [.rbx] s t ∧
      (∀ r i, t.zlane r i = s.zlane r i) ∧ t.syms = s.syms := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (26 : BitVec 32).signExtend 64 == 0) = decide (n + 1 = 26) := by
    rw [show (26 : BitVec 32).signExtend 64 = BitVec.ofNat 64 26 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem tzs_append (t : Nat) (a c : List Instr) : tzs t (a ++ c) = tzs t a ++ tzs t c :=
  List.flatMap_append

/-- The window's constants, as half `h` sees them, kept by what writes only at `DigOff`. -/
theorem hconsts_dig {m m' : Mem} {b : Addr} (hk : MemOff b DigOff m m') {h : Nat} (hh : h < 2)
    (hc : EConsts (hmem b h m) b) : EConsts (hmem b h m') b :=
  hc.of_mq fun d h1 h2 => Mem.readW_congr fun i hi => by
    simp only [hmem]
    rw [Offset.add_ofNat_add_ofNat, off_ofNat _ (by omega)]
    split
    · rename_i hw
      unfold InWin at hw
      refine hk _ ?_
      simp only [ofs]
      rw [off_ofNat _ (by unfold zoff ZB; omega)]
      unfold DigOff zoff ZB SGA SGB combSignMask
      omega
    · refine hk _ ?_
      simp only [ofs]
      rw [off_ofNat _ (by omega)]
      unfold DigOff SGA SGB combSignMask
      omega

/-! ## A step -/

theorem combStep_block : ([.mov .rdx (.reg .r9)] : List Instr) ++ zselect ++ tzs 15 esplit ++ zsign ++
    tzs 12 vnegBody ++ tzs 15 (carry (5 + ·)) ++ tzs 15 vadd ++
    ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)] : List Instr) =
    ([.mov .rdx (.reg .r9)] : List Instr) ++ (zselect ++ ((tzs 15 esplit ++ zsign ++
      (tzs 12 vnegBody ++ tzs 15 (carry (5 + ·) ++ vadd))) ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)] : List Instr))) := by
  simp only [tzs_append, List.append_assoc]

/-- A step of the loop: the entries of table `j` for the digits `d_{2j+1}` and `d_{2j}` added
to the halves. -/
theorem zstep_ok {s₀ z : State} {b T : Addr} {S j : Nat} {vA vB : ℤ} (hp : ZLoopPre s₀ b T S)
    (hS : S < 2 ^ 256) (h : ZInv s₀ b j vA vB z) (hj : j < 26) :
    WP isa combStep z fun t => t.zf = some (decide (j + 1 = 26)) ∧
      ZInv s₀ b (j + 1) (sdig S (2 * j + 1) * 1024 ^ j + vA) (sdig S (2 * j) * 1024 ^ j + vB) t := by
  have hsz := h.frame.scratch hp h.rdi
  rw [Zmm.combStep]
  refine WP.seq (WP.mono_syms (zscal zdigits_scal (zdigits_ok hsz hj hS h.counter (h.frame.bits hp)))
    fun z₁ ⟨⟨r8₁, r10₁, r9₁, rbx₁, sa₁, sb₁, g₁, rd₁, wr₁, m₁⟩, zl₁⟩ sy₁ => ?_)
  rw [combStep_block, WP.block_append_iff]
  have hs₁ : Scratch z₁ b :=
    ⟨by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsz.rdi,
      by rw [wr₁]; exact hsz.wr, hsz.nowrap⟩
  refine WP.mono (movRdx_ok z₁ r9₁) fun z₂ ⟨d₂, k₂, zl₂, sy₂⟩ => ?_
  have hs₂ : Scratch z₂ b := hs₁.of_keeps k₂ (by decide)
  have f₂ : ZFrame s₀ b z₂ := by
    refine ⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · rw [k₂.1 r (by intro e; simp at e; exact h3 (e ▸ by decide)), g₁ r (fun e => h3 (e ▸ by decide))
        (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))
        (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))]
      exact h.frame.gpr r h1 h2 h3
    · rw [k₂.1 _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.frame.r11
    · rw [k₂.2.2.1, rd₁]; exact h.frame.rd
    · rw [k₂.2.2.2, wr₁]; exact h.frame.wr
    · rw [k₂.2.1, m₁ a (fun e => ha (Or.inr e))]; exact h.frame.mem a ha
    · rw [sy₂, sy₁]; exact h.frame.syms
  have hmA : mag (nib S (2 * j + 1)) ≤ 16 := by unfold mag nib; split <;> omega
  have hmB : mag (nib S (2 * j)) ≤ 16 := by unfold mag nib; split <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (zselect_ok hs₂ (f₂.tbl hp) hj hmA hmB d₂ (by rw [k₂.1 _ (by decide)]; exact r8₁)
    (by rw [k₂.1 _ (by decide)]; exact r10₁)) fun z₃ ⟨sel₃, k14₃, k₃⟩ => ?_
  have hs₃ : Scratch z₃ b := ⟨by rw [k₃.gpr _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hsz.nowrap⟩
  have mem₃ : z₃.mem = z₁.mem := by rw [k₃.mem, k₂.2.1]
  -- the halves' points and constants, kept since `z`
  have zl : ∀ r, ¬ (zselRegs r ∨ r = xr 9) → ∀ i < 4, z₃.zlane r i = z.zlane r i := fun r hr i hi => by
    rw [k₃.zl r hr i hi, zl₂, zl₁]
  have hreg : ∀ q < 9, ¬ (zselRegs (xr q) ∨ xr q = xr 9) := by decide
  have l0 : ∀ h' < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h' z₃) 0 l i = lanes (Zmm.half b h' z) 0 l i :=
    fun h' hh l hl i hi => by
      simp only [lanes, Nat.zero_add]
      rw [qw_half b z₃ _ hl, qw_half b z _ hl]
      simp only [zq]
      rw [zl _ (hreg i (by omega)) _ (by omega)]
  have p₃ : ∀ h' < 2, lanePt (Zmm.half b h' z₃) = lanePt (Zmm.half b h' z) := fun h' hh => by
    simp only [lanePt]
    rw [fe5_congr (l0 h' hh 0 (by decide)), fe5_congr (l0 h' hh 1 (by decide)),
      fe5_congr (l0 h' hh 2 (by decide)), fe5_congr (l0 h' hh 3 (by decide))]
  have sm₃ : ∀ h' < 2, Small (Zmm.half b h' z₃) := fun h' hh l hl i hi => by
    rw [l0 h' hh l hl i hi]; exact h.small h' hh l hl i hi
  have hk₃ : ∀ h' < 2, EConsts (Zmm.half b h' z₃).mem b := fun h' hh => by
    show EConsts (hmem b h' z₃.mem) b
    rw [mem₃]
    exact hconsts_dig m₁ hh (h.hconsts h' hh)
  rw [WP.block_append_iff]
  refine WP.mono_syms (zentry_ok (m := hmag (mag (nib S (2 * j + 1))) (mag (nib S (2 * j))))
    (n := hmag (nib S (2 * j + 1)) (nib S (2 * j))) hs₃
    ⟨hs₃.rdi, hs₃.wr, hsz.nowrap, by rw [k₃.mem]; exact (f₂.zok hp hs₂.rdi).masks⟩
    hk₃ sm₃ (fun h' hh => by simp only [hmag]; split <;> omega) sel₃
    (fun h' hh => by
      rw [k14₃ h' hh 0 (by decide), k14₃ h' hh 1 (by decide), k14₃ h' hh 2 (by decide), k14₃ h' hh 3 (by decide),
        f₂.k2 h' hh 0 (by decide), f₂.k2 h' hh 1 (by decide), f₂.k2 h' hh 2 (by decide),
        f₂.k2 h' hh 3 (by decide), ← hp.k2 h' hh]
      rfl)
    (by rw [mem₃]; exact sa₁) (by rw [mem₃]; exact sb₁)) fun z₄ ⟨o₄, g₄, rd₄, wr₄, m₄, p₄, sm₄, e₄⟩ sy₄ => ?_
  have rbx₄ : z₄.gpr .rbx = BitVec.ofNat 64 j := by
    rw [g₄ _ (by decide), k₃.gpr _ (by decide), k₂.1 _ (by decide)]; exact rbx₁
  refine WP.mono (rbxNext26_ok z₄ j hj rbx₄) fun t ⟨rb, zf, kt, zlt, syt⟩ => ⟨zf, ?_⟩
  have lt : ∀ h' < 2, ∀ r l i, l < 4 → lanes (Zmm.half b h' t) r l i = lanes (Zmm.half b h' z₄) r l i :=
    fun h' hh r l i hl => by
      simp only [lanes]; rw [qw_half b t _ hl, qw_half b z₄ _ hl]; simp only [zq]; rw [zlt]
  have pt : ∀ h' < 2, lanePt (Zmm.half b h' t) = lanePt (Zmm.half b h' z₄) := fun h' hh => by
    simp only [lanePt]
    rw [fe5_congr fun i _ => lt h' hh 0 0 i (by decide), fe5_congr fun i _ => lt h' hh 0 1 i (by decide),
      fe5_congr fun i _ => lt h' hh 0 2 i (by decide), fe5_congr fun i _ => lt h' hh 0 3 i (by decide)]
  have gz : ∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = z₂.gpr r := fun r h0 h1 h2 h3 => by
    rw [kt.1 r (by simp [h0]), g₄ r h2, k₃.gpr r (by simp [h1, h2, h3])]
  refine ⟨by omega, by rw [gz _ (by decide) (by decide) (by decide) (by decide)]; exact hs₂.rdi, rb, ?_,
    fun h' hh => ?_, fun h' hh l hl i hi => ?_, ?_, ?_⟩
  · refine ⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · rw [gz r h1 (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))]
      exact f₂.gpr r h1 h2 h3
    · rw [gz _ (by decide) (by decide) (by decide) (by decide)]; exact f₂.r11
    · rw [kt.2.2.1, rd₄, k₃.rd]; exact f₂.rd
    · rw [kt.2.2.2, wr₄, k₃.wr]; exact f₂.wr
    · rw [kt.2.1, m₄ a (fun e => ha (Or.inl e)), k₃.mem]; exact f₂.mem a ha
    · rw [syt, sy₄, k₃.syms]; exact f₂.syms
  · show EConsts (hmem b h' t.mem) b
    rw [kt.2.1]; exact e₄ h' hh
  · rw [lt h' hh 0 l i hl]; exact sm₄ h' hh l hl i hi
  · rw [pt 0 (by decide), p₄ 0 (by decide), p₃ 0 (by decide)]
    simp only [hmag, ite_true]
    exact entry_rep h.valA S (2 * j + 1) hj
  · rw [pt 1 (by decide), p₄ 1 (by decide), p₃ 1 (by decide)]
    simp only [hmag, show (1 : Nat) ≠ 0 by decide, ite_false]
    exact entry_rep h.valB S (2 * j) hj

end VG.Proof.Ed25519.X86_64.Zmm
