import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop

/-!
# The blocks after the pipeline's

`tail_ok`: once the pipeline has encrypted and hashed the blocks before
`g + 16` (`TailReady`), with `t = nb - g - 16 < 8` blocks left,
`StitchAvx8.tailT` and `finish` meet `EPost`. With blocks left, `ksTail`
encrypts the eight counters the pipeline prepared, of the blocks from
`g + 16` on, and stores their keystream at `scratch + 832` (`ksTail_ok`);
`tailSetup` advances the counter by `t` and points `rax` at the powers
`H'ᵗ` … `H'` (`tailSetup_ok`); `StitchZH`'s loop encrypts the `t` blocks
and adds their products with their powers (`StitchZH.remLoop_ok`), which
`tailEnd` reduces into `Y`, for powers whose products add up to `GHASH`
(`TailLaw`, which `Ok.lean` proves of the powers the setup stores).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs aesFixed ksTail tailSetup tailEnd tailT finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32 blockAt ghashFrom)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_rev)
open VG.Proof.Aes.X86_64.AesNi (ea_at aesWith_eq)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)

/-- What the products of the last `r` blocks with the powers of the
pipeline add up to: `GHASH` over the `r` blocks (`Ok.lean` proves it of the
powers the setup stores, `H'⁸⁻ᵏ` at `128 + 16 k`). -/
def TailLaw (s₀ : State) (P : Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 7 → ∀ (X : Nat → Block) (y : Block),
    reduceB (StitchZH.accR X (fun j => P (8 - r + j)) y r) = ghashFrom (hk s₀) y ((List.range r).map X)

/-- Where `ksTail` stores the keystream of block `i`. -/
abbrev ksAddr (s₀ : State) (i : Nat) : Addr := pp s₀ + BitVec.ofNat 64 (832 + 16 * i)
abbrev ksR (s₀ : State) : Region := ⟨pp s₀ + BitVec.ofNat 64 832, 128⟩

/-! ## The keystream -/

theorem ksStores_ok (s : State) (p : Addr) (hr11 : s.gpr .r11 = p)
    (hin : ∀ i < 8, InRegions s.wr (p + BitVec.ofNat 64 (832 + 16 * i)) 16)
    (hwrap : p.toNat + 1024 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).map fun i =>
      .vmovdquStore .l128 (at_ .r11 (832 + 16 * i)) (aregs.getD i .xmm3))) s fun t =>
      (∀ i < n, t.mem.readW (p + BitVec.ofNat 64 (832 + 16 * i)) 128 = s.lane (aregs.getD i .xmm3) 0) ∧
      Frame [⟨p + BitVec.ofNat 64 832, 128⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ (∀ r l, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Frame.refl _ _, rfl, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ksStores_ok s p hr11 hin hwrap n (by omega)) fun t ⟨v, f, g, l, rd, wr⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    have ea : t.ea (at_ .r11 (832 + 16 * n)) = p + BitVec.ofNat 64 (832 + 16 * n) := by
      rw [ea_at, BitVec.ofInt_natCast, g, hr11]
    have hw : InRegions t.wr (p + BitVec.ofNat 64 (832 + 16 * n)) 16 := by rw [wr]; exact hin n (by omega)
    rw [WP.block_cons_iff]
    refine ⟨t.setMem (t.mem.writeW (p + BitVec.ofNat 64 (832 + 16 * n)) (t.xmm (aregs.getD n .xmm3))),
      by simp only [isa, exec, State.store128_eq, ea, hw, ite_true], WP.block_nil ⟨fun i hi => ?_, ?_,
        by rw [State.setMem_gpr, g], fun r l' => by rw [State.setMem_lane, l], by rw [State.setMem_rd, rd],
        by rw [State.setMem_wr, wr]⟩⟩
    · simp only [State.setMem_mem]
      by_cases hin' : i = n
      · subst hin'
        rw [Mem.readW_writeW_self _ _ 16 _ (by decide), ← l]
        rfl
      · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
        exact v i (by omega)
    · simp only [State.setMem_mem]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains p (by omega) (by omega) (by omega))

/-- A write of the keystream keeps what the working space holds below it. -/
theorem ks_read {s₀ : State} {m m' : Mem} (hf : Frame [ksR s₀] m m') (d n : Nat) (hd : d + n ≤ 832) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) = m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, n⟩)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint (pp s₀) (.inl hd) (by omega) (by decide)
  · omega

theorem Env.ksFrame {s₀ u v : State} {P : Nat → Block} (h : Env s₀ P u) (hf : Frame [ksR s₀] u.mem v.mem)
    (hg : v.gpr = u.gpr) (hrd : v.rd = u.rd) (hwr : v.wr = u.wr) : Env s₀ P v := by
  refine ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rcx,
    by rw [hg]; exact h.r11, by rw [hg]; exact h.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [hg]; exact h.other r h1 h2 h3 h4 h5 h6,
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by decide)⟩),
    fun k hk => (ks_read hf (128 + 16 * k) 16 (by omega)).trans (h.powers k hk),
    (ks_read hf 768 16 (by decide)).trans h.mask, (ks_read hf 784 16 (by decide)).trans h.poly,
    (ks_read hf 800 8 (by decide)).trans h.rounds, (ks_read hf 808 8 (by decide)).trans h.data,
    by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

theorem ksTail_ok {s₀ s : State} {P : Nat → Block} {c : Nat} (hp : SPre s₀) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) :
    WP isa (ksTail (nr s₀)) s fun t => Env s₀ P t ∧
      (∀ i < 8, blockAt t.mem (ksAddr s₀ i) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      Frame [ksR s₀] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.lane .xmm2 0 = s.lane .xmm2 0 ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hpos : 0 < nr s₀ := by rcases hp.rounds with h | h | h <;> omega
  have hwp := hp.wrap_p
  refine WP.seq (WP.mono (loadCounters_ok s (fun i hi => by
    rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
    exact in_rdwr (in_sub hp.p_in (by omega))) 8 (by decide)) fun t ⟨ht, hf⟩ => ?_)
  let Q : Nat → State → Prop := fun _ u => Env s₀ P u ∧ YFrame (.xmm1 :: aregs) t u
  have hEt : Env s₀ P t := hE.yframe hf
  refine WP.seq (WP.mono (aesFixed_ok (nr s₀) hpos aregs (by decide) (by decide) (fun _ => []) Q
    (fun _ _ h => h.1.keys hp) (fun _ _ _ _ h => WP.block_nil ⟨h, fun _ _ _ _ => rfl⟩)
    (fun _ _ _ h hf' => ⟨h.1.yframe hf', h.2.trans hf'⟩) (fun u h => by
      simp only [ea_at, BitVec.ofInt_natCast, BitVec.add_zero, h.1.r10, h.1.rdi])
    t ⟨hEt, YFrame.refl _ _⟩) fun u ⟨hu, hQ⟩ => ?_)
  have hct : ∀ i < 8, XBinOp.eval .pshufb (u.lane (aregs.getD i .xmm3) 0) revMask =
      ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀)) := by
    intro i hi
    apply Eq.symm
    apply aesWith_eq
    rw [hu _ (aregs_member i hi) 0 (by decide), ht i hi, ea_at, BitVec.ofInt_natCast, hE.r11]
    exact congrArg (fun x => Spec.Aes.cipher (nr s₀) (sch s₀)
      (VG.Proof.Aes.X86_64.AesNi.st x)) (hT.read i hi)
  refine WP.mono (ksStores_ok u (pp s₀) hQ.1.r11 (fun i hi => by
    rw [hQ.1.wr]; exact in_sub hp.p_in (by omega)) (by omega) 8 (by decide))
    fun v ⟨hv, hvF, hvG, hvL, hvR, hvW⟩ => ?_
  have hm : u.mem = s.mem := by rw [hQ.2.mem, hf.mem]
  have hFv : Frame [ksR s₀] s.mem v.mem := hm ▸ hvF
  refine ⟨?_, fun i hi => ?_, hFv, ?_, ?_, ?_, ?_⟩
  · exact hQ.1.ksFrame hvF hvG hvR hvW
  · rw [blockAt_eq, hv i hi]; exact hct i hi
  · rw [hvG, hQ.2.gpr, hf.gpr]
  · rw [hvL, hQ.2.lane _ (by decide) 0 (by decide), hf.lane _ (by decide) 0 (by decide)]
  · rw [hvR, hQ.2.rd, hf.rd]
  · rw [hvW, hQ.2.wr, hf.wr]

/-! ## Before the loop -/

theorem tailSetup_ok (s : State) {t : Nat} (ht : t < 8) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + t))
    (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 768) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 784) 16) :
    WP isa (.block tailSetup) s fun u =>
      u.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      u.gpr .rax = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) ∧
      u.gpr .rdx = s.gpr .rdx + 256 ∧ u.gpr .r11 = s.gpr .r11 + 64 ∧
      (u.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32 + BitVec.ofNat 32 t ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .rdx → q ≠ .r11 → q ≠ .r8 → u.gpr q = s.gpr q) ∧
      u.lane .xmm0 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 ∧
      u.lane .xmm1 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 784) 128 ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → u.lane r 0 = s.lane r 0) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have s9 : s.gpr .r9 - 16 = BitVec.ofNat 64 t := by
    rw [h9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1; omega
  have sh : BitVec.ofNat 64 t <<< 4 = BitVec.ofNat 64 (16 * t) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
    omega
  have hax : s.gpr .r11 + 256 - BitVec.ofNat 64 (16 * t) = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, Offset.ofNat_sub_ofNat (by omega)]
  have hin0' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin0
  have hin1' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((784 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin1
  have w32 : (BitVec.ofNat 64 t).setWidth 32 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [tailSetup, runBlock_cons, runStep_some, runBlock_nil, exec, isa, execAlu, execAlu32, execShift,
    show 1 ≤ 4 ∧ 4 ≤ 63 from by decide, and_self, readSrc, readSrc32,
    State.setReg32, State.load128, ea_at, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags,
    mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
    gpr_setV, mem_setV, rd_setV, wr_setV, e16, e64, e256, State.lane, xmm_setV,
    xmm_setReg, xmm_arithFlags, xmm_setFlags,
    setWidth_setWidth_32, w32, hax, reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', s9, sh,
    hin0', hin1']
  exact ⟨rfl, trivial, trivial, trivial, trivial, fun q h1 h2 h3 h4 h5 => by simp only [h1, h2, h3, h4, h5, ↓reduceIte],
    by rw [BitVec.ofInt_natCast], by rw [BitVec.ofInt_natCast],
    fun r h0 h1 => by simp only [h0, h1, ↓reduceIte], trivial⟩


/-! ## After the loop -/

theorem tailEnd_ok (s : State) {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (h1 : s.lane .xmm1 0 = poly) :
    WP isa (.block (tailEnd nr)) s fun u =>
      u.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧ u.gpr .r11 = s.gpr .r11 - 64 ∧
      u.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr) ∧
      (∀ q, q ≠ .r11 → q ≠ .r10 → u.gpr q = s.gpr q) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have enr : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * nr)) = BitVec.ofNat 64 (16 * nr) := by
    rcases hnr with rfl | rfl | rfl <;> decide
  rw [tailEnd, List.append_assoc, WP.block_append_iff]
  have hA : WP isa (.block [.alu .sub .r11 (.imm 64)]) s fun s₁ =>
      s₁.gpr .r11 = s.gpr .r11 - 64 ∧ (∀ q, q ≠ .r11 → s₁.gpr q = s.gpr q) ∧
      (∀ r l, s₁.lane r l = s.lane r l) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, e64, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩
  refine WP.mono hA fun s₁ ⟨a11, ag, al, am, ard, awr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₁ (by rw [al]; exact h1)) fun s₂ ⟨y₂, f₂⟩ => ?_
  have hC : WP isa (.block [.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 (16 * nr)))]) s₂
      fun u => u.gpr .r10 = s₂.gpr .rdi + BitVec.ofNat 64 (16 * nr) ∧ (∀ q, q ≠ .r10 → u.gpr q = s₂.gpr q) ∧
        (∀ r l, u.lane r l = s₂.lane r l) ∧ u.mem = s₂.mem ∧ u.rd = s₂.rd ∧ u.wr = s₂.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, enr, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ↓reduceIte, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩
  refine WP.mono hC fun u ⟨c10, cg, cl, cm, crd, cwr⟩ => ?_
  have hp₁ : prod (s₁.proj 0) = prod (s.proj 0) := by simp only [prod, State.proj_xmm, al]
  refine ⟨by rw [cl, y₂, hp₁], by rw [cg _ (by decide), f₂.gpr, a11], ?_, fun q h11 h10 => ?_,
    by rw [cm, f₂.mem, am], by rw [crd, f₂.rd, ard], by rw [cwr, f₂.wr, awr]⟩
  · rw [c10, f₂.gpr, ag _ (by decide)]
  · rw [cg q h10, f₂.gpr, ag q h11]

/-- `cmp r9, 16`. -/
theorem cmp16z_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.zf = some (s.gpr .r9 - 16 == 0) ∧ YFrame [] s s' := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩⟩

/-- Writes to a region of the data keep `Env`. -/
theorem Env.dataWrite {s₀ s t : State} {P : Nat → Block} (hp : SPre s₀) (h : Env s₀ P s) {R : Region}
    (hR : Region.Sub R (dR s₀)) (hf : Frame [R] s.mem t.mem)
    (hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Env s₀ P t := by
  have rdP : ∀ d w, d + w / 8 ≤ 1024 → w / 8 < 2 ^ 64 →
      t.mem.readW (pp s₀ + BitVec.ofNat 64 d) w = s.mem.readW (pp s₀ + BitVec.ofNat 64 d) w :=
    fun d w hd hn => hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, w / 8⟩) (Region.contains_self _ _)
      (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst r
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ hd)).sub_right hR) hn
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rcx,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r11,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [hg r h1 h2 h3 h4]; exact h.other r h1 h2 h3 h4 h5 h6,
    h.frame.trans (hf.sub fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst r
      exact ⟨dR s₀, by simp, hR⟩),
    fun k hk => (rdP _ 128 (by omega) (by decide)).trans (h.powers k hk),
    (rdP 768 128 (by decide) (by decide)).trans h.mask, (rdP 784 128 (by decide) (by decide)).trans h.poly,
    (rdP 800 64 (by decide) (by decide)).trans h.rounds, (rdP 808 64 (by decide) (by decide)).trans h.data,
    hr.trans h.rd, hw.trans h.wr⟩

/-! ## The blocks after the pipeline's -/

theorem tail_ok {s₀ s : State} {P : Nat → Block} {g : Nat} (hp : SPre s₀) (hlaw : TailLaw s₀ P)
    (h : TailReady s₀ P g s) :
    WP isa (.seq (tailT (nr s₀)) (.block finish)) s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hlt := h.lt
  obtain ⟨t, ht⟩ : ∃ t, t = nb s₀ - (g + 16) := ⟨_, rfl⟩
  have ht8 : t < 8 := by omega
  have hnb : nb s₀ = g + 16 + t := by omega
  have h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + t) := by rw [h.remaining]; congr 1; omega
  have hz : (BitVec.ofNat 64 (16 + t) - 16 == 0) = decide (t = 0) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]
    omega
  rw [tailT]
  refine WP.seq (WP.seq (WP.mono (cmp16z_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_))
  have hE₁ : Env s₀ P s₁ := h.env.yframe f₁
  refine WP.ite (decide (t = 0)) (by simp only [eval, z₁, h9, hz]) (fun he => ?_) (fun he => ?_)
  · -- No blocks left.
    have t0 : t = 0 := by simpa using he
    subst t0
    refine WP.block_nil (finish_complete hp false hE₁ ?_ ?_ ?_)
    · rw [f₁.mem, hnb]; exact h.data
    · rw [f₁.gpr, hnb]; exact h.counter
    · rw [f₁.lane .xmm2 (by simp) 0 (by decide), h.hash, hnb]
  -- `t` blocks left.
  have t1 : 1 ≤ t := by
    have : t ≠ 0 := by simpa using he
    omega
  refine WP.seq (WP.mono (ksTail_ok hp hE₁ (f₁.mem ▸ h.templates))
    fun s₂ ⟨hE₂, hks, hF₂, hg₂, hy₂, hrd₂, hwr₂⟩ => ?_)
  have g₂ : ∀ q, s₂.gpr q = s.gpr q := fun q => by rw [hg₂, f₁.gpr]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tailSetup_ok s₂ ht8 (by rw [g₂]; exact h9)
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide))))
    fun s₃ ⟨a10, aax, adx, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₃) fun s₄ ⟨p₄, f₄⟩ => ?_
  have hA : bAddr s₀ g + 256 = bAddr s₀ (g + 16) := bAddr_add s₀ g 16
  let E : StitchZH.REnv := ⟨t, .rdx, bAddr s₀ (g + 16), bAddr s₀ (g + 16), pp s₀ + BitVec.ofNat 64 64,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * t), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, ard, hE₂.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, awr, hE₂.wr]
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, am]
  have rdx₄ : s₄.gpr .rdx = bAddr s₀ (g + 16) := by rw [f₄.gpr, adx, g₂, h.cursor, hA]
  have hEok : E.Ok :=
    { r1 := t1, r15 := show t ≤ 15 by omega, gS := rdx₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [f₄.gpr, a11, hE₂.r11]; rfl
      gW := by show s₄.gpr .rax = _; rw [f₄.gpr, aax, hE₂.r11]
      src9 := show Reg.rdx ≠ Reg.r9 by decide, src10 := show Reg.rdx ≠ Reg.r10 by decide
      inS := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (bAddr s₀ (g + 16) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, bAddr_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j < t) => by
        show InRegions s₄.wr (bAddr s₀ (g + 16) + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hp.d_in (by omega)
      inW := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dS := fun j (hj : j < t) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (g + 16) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (g + 16), 16 * i⟩
        exact Offset.disjoint_base _ (by omega) (by omega)
      dK := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (g + 16), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (g + 16), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₄ : StitchZH.RInv E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [f₄.gpr]; exact a10
      r9 := by
        show s₄.gpr .r9 = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂, h9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by
        rw [f₄.lane _ (by decide) 0 (by decide), a0, hE₂.r11]
        exact hE₂.mask
      m1 := by
        rw [f₄.lane _ (by decide) 0 (by decide), a1, hE₂.r11]
        exact hE₂.poly }
  refine WP.seq (WP.mono (StitchZH.remLoop_ok hEok hI₄) fun s₅ hI₅ => ?_)
  refine WP.mono (tailEnd_ok s₅ hp.rounds hI₅.m1) fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the tail leaves.
  have g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' => by
    rw [g₆ q h11 h10, hI₅.gpr q h9' h10]
  have hR : Region.Sub ⟨bAddr s₀ (g + 16), 16 * t⟩ (dR s₀) := Offset.sub_base _ (by omega)
  have hF : Frame [⟨bAddr s₀ (g + 16), 16 * t⟩] s₂.mem s₆.mem := by
    rw [m₆, ← m₄]; exact hI₅.frame
  have hE₆ : Env s₀ P s₆ := hE₂.dataWrite hp hR hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 - 64 = _
        rw [f₄.gpr, a11, BitVec.add_sub_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE₂.rdi, hE₂.r10]
      · rw [g₆₄ q h11 h10 h4, f₄.gpr, ag q h10 h1 h2 h11 h3])
    (by rw [rd₆, hI₅.rd]; exact f₄.rd.trans ard) (by rw [wr₆, hI₅.wr]; exact f₄.wr.trans awr)
  have hD₂ : DataInv s₀ (g + 16) s₂.mem := (f₁.mem ▸ h.data).frame hF₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact hp.d_p.sub_right (Offset.sub_base (pp s₀) (d := 832) (n := 128) (k := 1024) (by decide)))
  have hX : ∀ j < t, E.X j = ctb s₀ (g + 16 + j) := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ (g + 16) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [m₄, bAddr_add, Offset.add_add, hD₂ _ (by omega), ite_eq_right (by omega),
      show 64 + (768 + 16 * j) = 832 + 16 * j by omega, hks j (by omega)]
  have hT : ∀ j < t, E.T j = P (8 - t + j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * t + 16 * j = 128 + 16 * (8 - t + j) by omega]
    exact hE₂.powers _ (by omega)
  refine finish_complete hp false hE₆ (fun k hk => ?_) ?_ ?_
  · by_cases hkg : k < g + 16
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (dp s₀) (.inl (by omega)) (by omega) (by omega)),
        hD₂ k (by omega), ite_eq_left hkg, ite_eq_left hk]
    · obtain ⟨j, rfl⟩ : ∃ j, k = g + 16 + j := ⟨k - (g + 16), by omega⟩
      have ct := hI₅.ct j (show j < t by omega)
      rw [show E.aD j = bAddr s₀ (g + 16 + j) from bAddr_add s₀ (g + 16) j, ← m₆] at ct
      rw [ct, hX j (by omega), ite_eq_left hk]
  · rw [g₆₄ _ (by decide) (by decide) (by decide), f₄.gpr, a8, g₂, h.counter, hnb, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, show g + 16 + 8 + t = g + 16 + t + 8 by omega]
  · rw [y₆, hI₅.prod, StitchZH.accR_congr _ t hX hT, hlaw t t1 (by omega)]
    have hy : E.y = hashPrefix s₀ false (g + 16) := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), al _ (by decide) (by decide), hy₂,
        f₁.lane _ (by simp) 0 (by decide), h.hash]
    rw [hy, hnb]
    simp only [hashPrefix, List.range_add, List.map_append, List.map_map, ghashFrom, List.foldl_append]
    rfl


end VG.Proof.Gcm.X86_64.StitchAvx8
