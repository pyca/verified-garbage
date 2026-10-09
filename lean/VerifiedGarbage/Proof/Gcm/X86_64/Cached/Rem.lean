import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction

/-!
# The blocks after the last group

`rem_ok`: once the loops stop with `r = nb mod 16` blocks after the groups
encrypted, the last group still to hash (`EInv`), `StitchZH.rem` stores the
counter after all the blocks (`remSetup_ok`), computes the keystream of the
`r` blocks while it hashes the last group (`ksSel_ok`), encrypts the `r`
blocks and adds their products with their powers (`remLoop_ok`), and reduces
them into `Y`, for powers whose products add up to `GHASH` (`RemOk`, which
`StitchZ/Ok.lean` proves of the powers the setup stores).
-/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (ksSel ksBatch rem remWith remSetup remBody remNext)
open VG.Proof.Gcm.X86_64.StitchZ (EInv AInv GEnv QG gq_ok gRegs gRegs_ok FinOk)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- What the products of the last `r` blocks with the powers of a group add
up to: `GHASH` over the `r` blocks (`StitchZ/Ok.lean` proves it of the powers
the setup stores, `H'¹⁶⁻ᵐ` at `16 m`). -/
def RemOk (H : Block) (P : Nat → Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    reduceB (accR X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y r) =
      ghashFrom H y ((List.range r).map X)

/-- `cmp r10, n`. -/
theorem cmp10_ok (s : State) (i : BitVec 32) (n : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r10 (.imm i)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r10).toNat < (BitVec.ofNat 64 n).toNat)) ∧ s'.gpr = s.gpr ∧
        (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The keystream of the `r` blocks after the last group, `4 ⌈r / 4⌉` blocks
of it, while the last group is hashed between the rounds. -/
theorem ksSel_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (gq j)) s fun s' => Q (j + 1) s' ∧ ZFrame gRegs s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r l, s'.zlane r l = s.zlane r l) → Frame [ksR s₀] s.mem s'.mem → Q 10 s')
    {c : Nat} {s : State} (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (h11 : s.gpr .r11 = pp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) (hQ : Q 1 s) :
    WP isa ksSel s fun s' => Q 10 s' ∧
      (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → x ∉ gRegs → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      Frame [ksR s₀] s.mem s'.mem := by
  -- A batch of `4 k ≥ r` blocks, from a state the comparisons leave as `s` was.
  have br : ∀ k, r ≤ 4 * k → k ≤ 4 → ∀ t : State, t.gpr = s.gpr → (∀ x l, t.zlane x l = s.zlane x l) →
      t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (ksBatch k gq) t fun s' => Q 10 s' ∧
        (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
          ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → x ∉ gRegs → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        Frame [ksR s₀] s.mem s'.mem := by
    intro k hrk hk4 t hg' hl hm hrd' hwr' hh
    have hQt : Q 1 t := hq 1 s t hQ ⟨hg', hm, hrd', hwr', fun x _ l _ => hl x l⟩
    refine WP.mono (ksBatch_ok hp hk4 gq gRegs gRegs_ok Q hg hq hqx
      (fun l hl' => by rw [hl]; exact hctr l hl') (fun l hl' => by rw [hl]; exact hmsk l hl')
      (fun l hl' => by rw [hl]; exact hinc l hl') (by rw [hg']; exact hrdi) (by rw [hg']; exact hrsi)
      (by rw [hg']; exact h11) (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr) (by rw [hm]; exact hfr)
      (hCache.keep hh (Keys.mk (by rw [hg', hm]; exact (hCache.base).sched) hCache.base.le
        (by rw [hrd', hwr', hg']; exact hCache.base.keys))) gq_keeps hQt)
      fun s' ⟨q', ks', g', rd', wr', l', f', _⟩ => ⟨q', fun i hi => ks' i (by omega), by rw [g', hg'],
        by rw [rd', hrd'], by rw [wr', hwr'], fun x h1 h2 h3 h4 l hl' => by rw [l' x h1 h2 h3 h4 l hl', hl],
        by rw [← hm]; exact f'⟩
  have c65 : BitVec.signExtend 64 (65 : BitVec 32) = BitVec.ofNat 64 65 := by decide
  have c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  have c193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  have t16 : (s.gpr .r10).toNat = 16 * r := by
    rw [h10, VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by omega)]
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s 65 65 c65)) fun s₁ ⟨⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 65).toNat = 65 from rfl] at cf₁
  refine WP.ite (decide (16 * r < 65)) (by simp only [eval, cf₁]) (fun h => ?_) (fun h => ?_)
  · exact br 1 (by simp at h; omega) (by decide) s₁ g₁ l₁ m₁ rd₁ wr₁ hh₁
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₁ 129 129 c129))
    fun s₂ ⟨⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
  rw [g₁, t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₂
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, cf₂]) (fun h' => ?_) (fun h' => ?_)
  · exact br 2 (by simp at h'; omega) (by decide) s₂ (by rw [g₂, g₁]) (fun x l => by rw [l₂, l₁])
      (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (hh₁.trans hh₂)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₂ 193 193 c193))
    fun s₃ ⟨⟨cf₃, g₃, l₃, m₃, rd₃, wr₃⟩, hh₃⟩ => ?_)
  rw [g₂, g₁, t16, show (BitVec.ofNat 64 193).toNat = 193 from rfl] at cf₃
  refine WP.ite (decide (16 * r < 193)) (by simp only [eval, cf₃]) (fun h'' => ?_) (fun h'' => ?_)
  · exact br 3 (by simp at h''; omega) (by decide) s₃ (by rw [g₃, g₂, g₁]) (fun x l => by rw [l₃, l₂, l₁])
      (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) ((hh₁.trans hh₂).trans hh₃)
  · exact br 4 (by omega) (by decide) s₃ (by rw [g₃, g₂, g₁]) (fun x l => by rw [l₃, l₂, l₁])
      (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) ((hh₁.trans hh₂).trans hh₃)

/-- The GHASH state of the last group, kept by the keystream stored. -/
theorem QG.ksR {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {j g : Nat}
    (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    {t t' : State} (h : QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r l, t'.zlane r l = t.zlane r l)
    (hf : Frame [ksR s₀] t.mem t'.mem) : QG s₀ lo a X P yl j t' := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 4, prod (t'.zproj l) = prod (t.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, hlane]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l), 16⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane]; exact h2.1, fun l h1 h4 => by rw [hlane]; exact h2.2 l h1 h4⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl, fun l hl => by rw [hlane]; exact h2.2 l hl⟩

/-- Before the loop: `rdx` at the blocks, `r10 = 0`, and the products cleared. -/
theorem remPre_ok (s : State) :
    WP isa (.block ([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] ++ [] ++ Impl.Gcm.X86_64.StitchAvx.zero)) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
        (∀ q, q ≠ .rdx → q ≠ .r10 → s'.gpr q = s.gpr q) ∧ prod (s'.proj 0) = Prod.zero ∧
        (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → s'.lane x 0 = s.lane x 0) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  rw [List.append_nil, WP.block_append_iff]
  have hA : WP isa (.block [.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)]) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .rdx + 256 ∧ s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .rdx → q ≠ .r10 → s₁.gpr q = s.gpr q) ∧ (∀ x l, s₁.lane x l = s.lane x l) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, arithFlags,
      State.setFlags, State.setReg32, isa, State.setReg, e256, reduceCtorEq, ↓reduceIte, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, rfl, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
      trivial⟩
  refine WP.mono hA fun s₁ ⟨d₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₁) fun s' ⟨p', f'⟩ =>
    ⟨by rw [f'.gpr, d₁], by rw [f'.gpr, z₁], fun q h1 h2 => by rw [f'.gpr, g₁ q h1 h2], p',
      fun x h8 h9 h10 => by rw [f'.lane x (by simp [h8, h9, h10]) 0 (by decide), l₁], by rw [f'.mem, m₁],
      by rw [f'.rd, rd₁], by rw [f'.wr, wr₁]⟩

theorem rem_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOk (hk s₀) P) {e : Nat} {s : State} (hI : EInv s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hne : nb s₀ ≠ 16 * e) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa rem s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  -- The `r` blocks after the `16 e` encrypted.
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega
  have hr15 : r ≤ 15 := by omega
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9]; congr 1; omega
  have hrax : s.gpr .rax = cp s₀ := hI.rax
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show rem = .seq (.block remSetup) (.seq ksSel
      (.seq (.block ([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] ++ [] ++ Impl.Gcm.X86_64.StitchAvx.zero))
        (.seq (.loop (.block (remBody .rdx ++ remNext)) .ne)
          (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ storeY))))) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetup_ok s hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, hI.a.wr]; exact in_sub_int hp.c_in (by omega))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0] at m₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → s₁.gpr q = s.gpr q := g₁
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache.keep hh₁ (keys_of hp hrdi₁ (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁)
  -- The last group, hashed while the keystream is computed.
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [gk₁ _ (by decide) (by decide)]
      r11 := by rw [gk₁ _ (by decide) (by decide), hr11]
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega), m₁,
          show cp s₀ = (cR s₀).base from rfl,
          blockAt_writeW_sep' (hp.d_c.sub_left (Offset.sub_base _ (by omega))) rfl,
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega))).sep
          (Region.contains_self _ _) cw) (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  have hQ₁ : QG s₀ (fun _ => 0) a X P yl 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [z₁ _ (by decide) l hl]⟩⟩
  refine WP.seq (WP.mono (ksSel_ok hp hr1 hr15 (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.ksR hp (g := e - 1) (by omega) ha h hg hrd hwr hl hf)
    (c := 16 * e) a10₁ (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.inc l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rsi) (by rw [gk₁ _ (by decide) (by decide)]; exact hr11)
    (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁ hCache₁ hQ₁)
    fun s₂ ⟨q₂, ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  obtain ⟨_, h1₂, y₂⟩ := q₂
  rw [ite_t (by decide)] at y₂
  -- `Y` after the groups.
  have hY₂ : s₂.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) := by
    rw [← State.zlane_lt2 _ _ (by decide), y₂.1, hf X yl hI.y1,
      show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, VG.Proof.Gcm.X86_64.Stitch.ghash_append16, ← hI.y]
  -- `rdx` at the `r` blocks, `r10 = 0`, the products cleared.
  refine WP.seq (WP.mono (remPre_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [d₃, g₂, gk₁ _ (by decide) (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (show a.toNat + 256 < 2 ^ 64 by omega), BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (16 * e) < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    show a.toNat + 256 = _
    omega
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀)
    (pp s₀ + BitVec.ofNat 64 (256 - 16 * r)) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁, hI.a.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, hI.a.wr]
  have gk₃ : ∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .rax → s₃.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₃ q h1 h2, g₂, gk₁ q h2 h3]
  have hE : E.Ok :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA,
      gP := by show s₃.gpr .r11 = _; rw [gk₃ _ (by decide) (by decide) (by decide), hr11]
      gW := by show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂, ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega)
      inW := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega) (by omega)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (768 + 16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * r⟩
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₃ : RInv E 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      r9 := by
        show s₃.gpr .r9 = _
        rw [gk₃ _ (by decide) (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₃
      y := rfl
      m0 := by
        rw [l₃ _ (by decide) (by decide) (by decide), ← State.zlane_lt2 _ _ (by decide),
          l₂ _ (by decide) (by decide) (by decide) (by decide) 0 (by decide), z₁ _ (by decide) 0 (by decide)]
        exact hI.a.msk 0 (by decide)
      m1 := by
        rw [l₃ _ (by decide) (by decide) (by decide), ← State.zlane_lt2 _ _ (by decide)]
        exact h1₂ 0 (by decide) }
  refine WP.seq (WP.mono (remLoop_ok hE hI₃) fun s₄ hI₄ => ?_)
  -- The products reduced into `Y`, and `Y` stored.
  rw [WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  have hrcx : s₅.gpr .rcx = yp s₀ := by
    rw [f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₅
    (by rw [f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0)
    (by rw [hrcx, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, f₅.mem] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega
  -- What the stages keep of the memory before them.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → Region.Disjoint ⟨p, 16⟩ (ksR s₀) →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (ksR s₀) := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  -- The blocks.
  have hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega⟩
      have hj : j < r := by omega
      have ct := hI₄.ct j hj
      have eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct]
      show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
        blockAt s₃.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) = _
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk, m₃, ks₂ j hj]
      simp only [hke, ite_false]
  have hX : ∀ j < r, E.X j = ctb s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega
    show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk, m₃, ks₂ j hj]
    simp only [show ¬ 16 * e + j < 16 * e by omega, ite_false]
  have hT : ∀ j < r, E.T j = P ((16 - r + j) / 4) ((16 - r + j) % 4) := fun j hj => by
    show s₃.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 128 = _
    have hm : 16 - r + j < 16 := by omega
    rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega,
      m₃, f₂.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4)), 16⟩)
        (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega))).sep
          (Region.contains_self _ _) cw) (by decide)]
    exact hI.pw _ (by omega) _ (by omega)
  sorry

end VG.Proof.Gcm.X86_64.StitchZH
