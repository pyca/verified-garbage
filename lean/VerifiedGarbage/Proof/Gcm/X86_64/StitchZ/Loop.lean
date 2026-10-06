import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec

/-!
# Interleaved counter mode and GHASH with AVX-512: the loops

`EInv s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the
first `e - 1` hashed into `Y` (lane 0 of `zmm2`, the other lanes 0), the
powers `P` in the working space; `rdx` points to group `e - 1`, the next to
hash. `body_ok`: a body encrypts group `e` (`batch_ok`) while it hashes group
`e - 1` between its rounds (`gq_ok`), which it does not write (`QG.data`).
`DInv` and `dbody_ok` are the same for decryption, which hashes each group
during its own rounds, before its blocks are overwritten. The setup is
`Stitch`'s, and then the four lanes (`setupZ_ok`); the stores at the end are
`Stitch`'s. `final_ok` and `dfinal_ok` are the stores after the loops, for
any powers whose products add up to `GHASH` (`FinOk`), without the field;
`StitchZ/Loop48.lean` puts the loops of three groups in front of these.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16 blockAt_writeW_sep' blocks_ctr32)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (batch body gq ghLoad ord setupZ first lastG dbody fin)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## Helpers -/

/-- `vpshufb x, x', ymm0` (`VEX.128`) and a 16-byte store of `x` to `[b]`. -/
theorem store16Z_ok (x x' : XReg) (b : Reg) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr b) 16) :
    WP isa (.block [.vop (.vbin .vpshufb .l128 x x' .xmm0), .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ b 0) x])
      s fun s' => s'.mem = s.mem.writeW (s.gpr b) (XBinOp.eval .pshufb (s.lane x' 0) revMask) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ x → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hin' : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  simp only [State.lane] at h0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.setV, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, VBinOp.sse, State.lane, ite_true, hin', h0, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  simp [State.zlane, State.lane, hr]

/-! ## The GHASH state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {j c g : Nat}
    (hc : c + 16 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 16))
    {t t' : State} (h : QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] t.mem t'.mem) : QG s₀ lo a X P yl j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 4, prod (t'.zproj l) = prod (t.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, hlane .xmm8 (by decide) (by decide) l hl,
      hlane .xmm9 (by decide) (by decide) l hl, hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        fun l h1 h4 => by rw [hlane _ (by decide) (by decide) l h4]; exact h2.2 l h1 h4⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The end of an encryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 32`. -/
theorem nextE_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 32)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a decryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 16`. -/
theorem nextD_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 16)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The powers in the working space are kept by the data written. -/
theorem keepP {s₀ : State} (hp : SPre s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {k l : Nat} (hk : k < 4) (hl : l < 4) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  have hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  have hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batch_ok hp gq gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

/-! ## The setup -/

theorem State.zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (l : Nat) :
    (s.setV .l256 d lo hi).zlane r l =
      if r = d then (if l = 0 then lo else if l = 1 then hi else 0) else s.zlane r l := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega : l = 0 ∨ l = 1 ∨ 2 ≤ l) with rfl | rfl | hl
    · simp
    · simp
    · simp [show ¬ l < 2 by omega, show l ≠ 0 by omega, show l ≠ 1 by omega]
  · simp [h]

theorem paddd_two_two : XBinOp.eval .paddd VG.Proof.Aes.X86_64.Vaes.two VG.Proof.Aes.X86_64.Vaes.two = four := by
  decide

theorem lane0_zlane (t : State) (r : XReg) : t.lane r 0 = t.zlane r 0 := rfl
theorem lane1_zlane (t : State) (r : XReg) : t.lane r 1 = t.zlane r 1 := rfl

theorem shuf44_0 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 0 = a 0 := rfl
theorem shuf44_1 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 1 = a 1 := rfl
theorem shuf44_2 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 2 = b 0 := rfl
theorem shuf44_3 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 3 = b 1 := rfl

structure Ready (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The four lanes, from the two of `Stitch.setup`: the powers of the `k`-th
load are the `2k`-th and `2k + 1`-th of `Stitch`'s. -/
theorem setupZ_ok {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Stitch.Ready s₀ P s) :
    WP isa (.block setupZ) s (Ready s₀ fun k l => P (2 * k + l / 2) (l % 2)) := by
  refine WP.mono (WP.zframe (is := setupZ) (rs := [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm1, .xmm2]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l (cb s₀)) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun s' ⟨⟨c14, m0, i15, p1, y0, y1⟩, f⟩ => ?_
  · have c0 : s.xmm .xmm14 = Nat.repeat inc32 0 (cb s₀) := by
      have h := hR.a.ctr 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 (cb s₀) := by
      have h := hR.a.ctr 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.a.inc 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.a.inc 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have m0 : s.xmm .xmm0 = revMask := by
      have h := hR.a.msk 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have m1 : s.ymmHi .xmm0 = revMask := by
      have h := hR.a.msk 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have p0 : s.xmm .xmm1 = poly := by
      have h := hR.m1 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have p1 : s.ymmHi .xmm1 = poly := by
      have h := hR.m1 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    rw [setupZ]
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, ?_, fun l hl1 hl4 => ?_⟩⟩
    all_goals simp only [VOp.exec]
    all_goals try rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    all_goals try omega
    all_goals simp (disch := decide) only [lane0_zlane, lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4, State.zlane_setV256,
      State.zlane_setV128, shuf44_0, shuf44_1, shuf44_2, shuf44_3, reduceCtorEq,
      ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
    all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
      show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
    all_goals first
      | exact c0 | exact c1 | exact m0 | exact m1 | exact p0 | exact p1
      | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [i0]; exact paddd_two_two) | (rw [i1]; exact paddd_two_two)
  · have hA := hR.a
    refine ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.zero_add], m0, i15, by rw [f.gpr]; exact hA.rdi,
      by rw [f.gpr]; exact hA.rsi, by rw [f.gpr]; exact hA.r10, by rw [f.mem]; exact hA.frame,
      fun k hk => by rw [f.mem]; exact hA.blocks k hk, by rw [f.rd]; exact hA.rd, by rw [f.wr]; exact hA.wr⟩,
      by rw [f.gpr]; exact hR.rdx, by rw [f.gpr]; exact hR.rax, fun r h1 h2 h3 => by rw [f.gpr]; exact hR.gpr r h1 h2 h3,
      fun k hk l hl => ?_, fun l hl => ?_, by rw [y0]; exact hR.y, y1⟩
    · rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega]
      exact hR.pw _ (by omega) _ (by omega)
    · exact p1 l hl

/-- The first group, with nothing between its rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [hg₁]; exact hR.gpr r h1 h2 h4,
    fun k hk l hl => by rw [keepP hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (by decide)]; simp

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega)]; rfl

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of a group. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {yl : Nat → Block} :
    ∀ n, n ≤ 4 → ∀ s, GEnv s₀ 0 a X P s → (∀ l < 4, s.zlane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ord i))) s fun s' => GEnv s₀ 0 a X P s' ∧
        (0 < n → ∀ l < 4, prod (s'.zproj l) = accN X P yl l n) ∧ (∀ l < 4, s'.zlane .xmm2 l = yl l) ∧
        ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun h => absurd h (by decide), hy, ZFrame.refl _ _⟩
  | n + 1, hn, s, hE, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ghRun_ok n (by omega) s hE hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (ghStep (by omega) (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨hE', fun _ => p', y', f₁.trans f'⟩

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 4, ∀ l < 4, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  have f₂ : ZFrame [.xmm8, .xmm9, .xmm10] s₁ s₁ := ZFrame.refl _ _
  have hE₂ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  refine WP.mono (ghRun_ok (yl := yl) 4 (Nat.le_refl _) s₁ hE₂
    (fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.zlane _ (by decide) l hl, f₂.zlane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ (by decide) 0 (by decide), p₃ (by decide) 1 (by decide), p₃ (by decide) 2 (by decide),
    p₃ (by decide) 3 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), f₄.zlane _ (by decide) 0 (by decide), f₃.zlane _ (by decide) 0 (by decide),
      f₂.zlane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hI.a.msk 0 (by decide)
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₅.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  have hdata := blocks_ctr32 hb
  refine ⟨hdata, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₅.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₅.mem (dp s₀) (nb s₀))
    rw [show blocksAt s₅.mem (dp s₀) (nb s₀) = (List.range (16 * e)).map (ctb s₀) from by
        rw [← he]; simp only [blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-! ## Decryption -/

structure DInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- Which blocks of the group the GHASH loads to come still read: all until
they are done, after round 4. -/
abbrev loD (j : Nat) : Nat := if j < 5 then 0 else 16

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInv s₀ P e s) :
    WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  have hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * e + 64 * k) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  -- The group is hashed after rounds 1–4, before its blocks are decrypted, and reduced after round 5.
  refine WP.seq (WP.mono (batch_ok hp gq gRegs gRegs_ok (QG s₀ loD a X P yl)
    (gq_ok (fun j => by simp only [loD]; split <;> split <;> omega) (fun j hj1 hj4 => by
      simp only [loD, show j < 5 by omega, ite_true]; exact Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi _ => by have : 16 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega) hA₁ (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : DInv s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  have hm0₁ : s₁.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide), State.zlane_lt2 _ _ (by decide)]; exact hm0
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₁ hm0₁
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have e2 : s₁.lane .xmm2 0 = s.zlane .xmm2 0 := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide)]
  rw [g₁, hrcx, m₁, e2] at m₂
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₂.mem (yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

end VG.Proof.Gcm.X86_64.StitchZ
