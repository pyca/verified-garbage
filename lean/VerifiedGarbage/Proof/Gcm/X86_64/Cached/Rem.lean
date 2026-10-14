module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

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

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (ksSel ksBatch rem remWith remSetup remBody remLoops)
open VG.Proof.Gcm.X86_64.StitchZ (EInv AInv GEnv QG gq_ok gRegs gRegs_ok FinOk)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- What the products of the last `r` blocks with the powers of a group, in
the lanes `laneOf` puts them in, add up to, each lane's reduced: `GHASH` over
the `r` blocks (`StitchZ/OkP.lean` proves it of the powers the setup stores,
`H'¹⁶⁻ᵐ` at `16 m`). -/
def RemOk (H : Block) (P : Nat → Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    (reduceB (laneAcc X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y r 0 r) ^^^
        reduceB (laneAcc X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y r 2 r)) ^^^
      (reduceB (laneAcc X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y r 1 r) ^^^
        reduceB (laneAcc X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y r 3 r)) =
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
of it, while `g` runs between the rounds. -/
theorem ksSelWith_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (g : Nat → List Instr) (G : List XReg) (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r l, s'.zlane r l = s.zlane r l) → Frame [ksR s₀] s.mem s'.mem → Q 10 s')
    {c : Nat} {s : State} (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (h11 : s.gpr .r11 = pp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) (hQ : Q 1 s) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ksSelWith g) s fun s' => Q 10 s' ∧
      (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → x ∉ G → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      Frame [ksR s₀] s.mem s'.mem := by
  -- A batch of `4 k ≥ r` blocks, from a state the comparisons leave as `s` was.
  have br : ∀ k, r ≤ 4 * k → k ≤ 4 → ∀ t : State, t.gpr = s.gpr → (∀ x l, t.zlane x l = s.zlane x l) →
      t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (ksBatch k g) t fun s' => Q 10 s' ∧
        (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
          ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → x ∉ G → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        Frame [ksR s₀] s.mem s'.mem := by
    intro k hrk hk4 t hg' hl hm hrd' hwr' hh
    have hQt : Q 1 t := hq 1 s t hQ ⟨hg', hm, hrd', hwr', fun x _ l _ => hl x l⟩
    refine WP.mono (ksBatch_ok hp hk4 g G hG Q hg hq hqx
      (fun l hl' => by rw [hl]; exact hctr l hl') (fun l hl' => by rw [hl]; exact hmsk l hl')
      (fun l hl' => by rw [hl]; exact hinc l hl') (by rw [hg']; exact hrdi) (by rw [hg']; exact hrsi)
      (by rw [hg']; exact h11) (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr) (by rw [hm]; exact hfr)
      (hCache.keep hh (Keys.mk (by rw [hg', hm]; exact (hCache.base).sched) hCache.base.le
        (by rw [hrd', hwr', hg']; exact hCache.base.keys))) hgh hQt)
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
      Frame [ksR s₀] s.mem s'.mem :=
  ksSelWith_ok hp hr1 hr15 gq gRegs gRegs_ok gq_keeps Q hg hq hqx h10 hctr hmsk hinc hrdi hrsi h11 hrd hwr hfr
    hCache hQ

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

/-- Before the loops: `rdx` at the blocks, `r10 = 0`, and the products cleared. -/
theorem remPre_ok (s : State) :
    WP isa (.block (([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] : List Instr) ++ ([] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero)) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
        (∀ q, q ≠ .rdx → q ≠ .r10 → s'.gpr q = s.gpr q) ∧
        (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
        (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  rw [List.append_nil, WP.block_append_iff]
  have hA : WP isa (.block [.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)]) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .rdx + 256 ∧ s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .rdx → q ≠ .r10 → s₁.gpr q = s.gpr q) ∧ (∀ x l, s₁.zlane x l = s.zlane x l) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, arithFlags,
      State.setFlags, State.setReg32, isa, State.setReg, e256, reduceCtorEq, ↓reduceIte, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, rfl, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
      trivial⟩
  refine WP.mono hA fun s₁ ⟨d₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (zeroZ_ok s₁) fun s' ⟨zz, f', g', m', rd', wr'⟩ =>
    ⟨by rw [g', d₁], by rw [g', z₁], fun q h1 h2 => by rw [g', g₁ q h1 h2], zz,
      fun x h8 h9 h10 l hl => by rw [f' x h8 h9 h10 l hl, l₁], by rw [m', m₁], by rw [rd', rd₁], by rw [wr', wr₁]⟩


end VG.Proof.Gcm.X86_64.StitchZH
