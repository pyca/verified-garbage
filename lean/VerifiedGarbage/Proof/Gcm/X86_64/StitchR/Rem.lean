module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPair
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGD
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Gcm.X86_64.StitchR.Ks`, which only this module used -/

section

/-!
# The keystream of the blocks after the last group, eight at a time

`ks_ok`: `StitchR.ks j` encrypts the next eight counters, in both lanes of
`ymm3`–`ymm6` (`Vaes.ctrs_ok`, `Vaes.aesG_ok`), and stores their keystream to
`scratch + 32 j`, as `Stitch.batch_ok` does without the data.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb ciph sch addr_eq aregs_ok in_sub_int storesK_ok)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq st)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt inc32)

theorem ks_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (j : Nat) (hj : 32 * j + 128 ≤ 1024) {c : Nat} {s : State}
    (hctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 2, s.lane .xmm0 l = revMask) (hinc : ∀ l < 2, s.lane .xmm15 l = two)
    (hK : Keys (nr s₀) (sch s₀) s) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀))
    (h11 : s.gpr .r11 = pp s₀) (hwr : s.wr = s₀.wr) :
    WP isa (Impl.Gcm.X86_64.StitchR.ks j) s fun s' =>
      (∀ i < 8, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (32 * j + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 (c + 8 + l) (cb s₀)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (32 * j), 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwp := hp.wrap_p
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hctr hmsk hinc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys hK f₁
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds (fun _ => []) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial) s₁ hK₁
    trivial (by rw [f₁.gpr, hrsi]; simp) (by rw [f₁.gpr, hr10])) fun s₂ ⟨e₂, _, f₂⟩ => ?_)
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have h11₂ : s₂.gpr .r11 = pp s₀ := by rw [f₂.gpr, f₁.gpr, h11]
  have hwr₂ : s₂.wr = s₀.wr := by rw [f₂.wr, f₁.wr, hwr]
  refine WP.mono (storesK_ok .r11 aregs j s₂ (fun k hk => by
      rw [hwr₂, h11₂]; exact in_sub_int hp.p_in (by simp [aregs] at hk; omega_using [hj, hk]))
    (by rw [h11₂]; simp [aregs]; omega_using [hj, hwp])) fun s₃ ⟨sv, fr, g₃, rd₃, wr₃, l₃⟩ => ?_
  rw [h11₂, show 32 * aregs.length = 128 from rfl] at fr
  rw [h11₂] at sv
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at fr
  refine ⟨fun i hi => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr], by rw [rd₃, f₂.rd, f₁.rd],
    by rw [wr₃, f₂.wr, f₁.wr], fun x h13' h14 hr l hl => ?_, fr⟩
  · have hk : i / 2 < aregs.length := by simp [aregs]; omega_using [hi]
    have := sv (i / 2) hk (i % 2) (by omega_using [])
    rw [show 32 * (j + i / 2) + 16 * (i % 2) = 32 * j + 16 * i by omega_using []] at this
    rw [blockAt_eq, this, ks (i / 2) hk (i % 2) (by omega_using []), show c + 2 * (i / 2) + i % 2 = c + i by omega_using []]
  · rw [l₃, f₂.lane _ (by simp [aregs]) l hl, c₁ l hl]; simp [aregs]
  · rw [l₃, f₂.lane _ (by simp [h13', hr]) l hl, f₁.lane _ (by simp [h14, hr]) l hl]

end VG.Proof.Gcm.X86_64.StitchR

end

end


/-!
# The 256-bit loops: the blocks after the last group

The pieces `remD` and `remE` (`RemE.lean`) share: `ksSel_ok` computes the
keystream of eight or sixteen blocks to `scratch + 256`, `preV_ok` lowers
`r11` by 512, so that the loops' keystream at `r11 + 768` is at
`scratch + 256`, and clears the products, and `add11_ok` restores `r11`.
`RemLaw` is what the products of the last `r` blocks with their powers, reduced,
add up to (`Ok.lean` proves it of the prepared powers). `loopDR_okF` is the
decryption loop of `decR`, for any number of blocks from 16 on.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost DInv AInv Ready FinOk dbody_ok dfinal_ok nb nr kp pp cp yp cb dp dR pR cR
  yR bAddr blk ctb ciph sch hk y₀ addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' store16_ok)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordD dbody)
open VG.Impl.Gcm.X86_64.StitchR (ks ksSel remD decR)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInvD accR accR_congr remSetup_ok zeroZ_ok keys_of cmp10_ok
  add9_ok test99_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- What the products of the last `r` blocks with the powers of a group, in
one lane, reduced, add up to: `GHASH` over the `r` blocks. -/
def RemLaw (H : Block) (P : Nat → Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    reduceB (accR X (fun j => P ((16 - r + j) / 2) ((16 - r + j) % 2)) y r) = ghashFrom H y ((List.range r).map X)

/-- `keyEnd`: `r10` at the last round key. -/
theorem keyEnd_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.keyEnd) s fun s' =>
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ (∀ x l, s'.lane x l = s.lane x l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.StitchR.keyEnd, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by bv_omega, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The keystream of the `r` blocks after the last group, to `scratch + 256`;
of eight blocks, only 128 bytes written, if `r ≤ 8`. -/
theorem ksSel_okF {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15) {c : Nat} {s : State}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 2, s.lane .xmm0 l = revMask) (hinc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two)
    (hK : Keys (nr s₀) (sch s₀) s) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdi : s.gpr .rdi = kp s₀)
    (h11 : s.gpr .r11 = pp s₀) (hwr : s.wr = s₀.wr) :
    WP isa ksSel s fun s' =>
      ((∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (256 + 16 * i)) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem) ∧
      (r ≤ 8 → Frame [⟨pp s₀ + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem) := by
  have c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  have t16 : (s.gpr .r10).toNat = 16 * r := by rw [h10, toNat_ofNat_lt (by omega_arith)]
  rw [show ksSel = .seq (.block [.alu .cmp .r10 (.imm 129)])
      (.ite .b (.seq (.block Impl.Gcm.X86_64.StitchR.keyEnd) (ks 8))
        (.seq (.block Impl.Gcm.X86_64.StitchR.keyEnd) (.seq (ks 8) (ks 12)))) from rfl]
  refine WP.seq (WP.mono (cmp10_ok s 129 129 c129) fun s₁ ⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₁
  have l₁' : ∀ x l, l < 2 → s₁.lane x l = s.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₁]
  -- `keyEnd`, then a batch from `s₂`.
  have pre : WP isa (.block Impl.Gcm.X86_64.StitchR.keyEnd) s₁ fun s₂ =>
      s₂.gpr .r10 = s₂.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀) ∧ (∀ q, q ≠ .r10 → s₂.gpr q = s.gpr q) ∧
      (∀ x l, l < 2 → s₂.lane x l = s.lane x l) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr :=
    WP.mono (keyEnd_ok s₁) fun s₂ ⟨a, g, l, m, rd, wr⟩ =>
      ⟨by rw [a, g _ (by decide), g₁, hrsi], fun q h => by rw [g q h, g₁], fun x l' hl => by rw [l, l₁' x l' hl],
        by rw [m, m₁], by rw [rd, rd₁], by rw [wr, wr₁]⟩
  have hwp := hp.wrap_p
  have kb : ∀ {t : State}, (∀ q, q ≠ .r10 → t.gpr q = s.gpr q) →
      Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem t.mem → t.rd = s.rd → t.wr = s.wr →
      Keys (nr s₀) (sch s₀) t := fun {t} hg hf hrd hwr' => by
    have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega_arith
    refine ⟨?_, hK.le, by rw [hrd, hwr', hg _ (by decide)]; exact hK.keys⟩
    rw [hg _ (by decide), hK.sched, hrdi]
    simp only [Spec.Aes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine (hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r' hr' => ?_)
      (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_arith) hi).symm
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.p_k.symm.sub_left (Region.sub_prefix hn)).sub_right (Offset.sub_base _ (by omega_arith))
  have b8 : ∀ t : State, t.gpr .r10 = t.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀) → (∀ q, q ≠ .r10 → t.gpr q = s.gpr q) →
      (∀ x l, l < 2 → t.lane x l = s.lane x l) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      WP isa (ks 8) t fun s' =>
        (∀ i < 8, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (256 + 16 * i)) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
        (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 (c + 8 + l) (cb s₀)) ∧
        s'.gpr = t.gpr ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧
        (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = t.lane x l) ∧
        Frame [⟨pp s₀ + BitVec.ofNat 64 256, 128⟩] t.mem s'.mem := fun t a g l m rd wr =>
    WP.mono (ks_ok hp 8 (by decide) (c := c) (fun l' hl => by rw [l _ _ hl]; exact hctr l' hl)
      (fun l' hl => by rw [l _ _ hl]; exact hmsk l' hl) (fun l' hl => by rw [l _ _ hl]; exact hinc l' hl)
      (kb g (by rw [m]; exact Frame.refl _ _) rd wr) (by rw [g _ (by decide)]; exact hrsi) a
      (by rw [g _ (by decide)]; exact h11)
      (by rw [wr]; exact hwr)) fun s' ⟨b, c', g', rd', wr', l', f'⟩ => ⟨fun i hi => by
        have := b i hi; rwa [show 32 * 8 + 16 * i = 256 + 16 * i by omega_arith] at this, c', g', rd', wr', l',
        by rwa [show 32 * 8 = 256 from rfl] at f'⟩
  have sub128 : ∀ m m' : Mem, Frame [⟨pp s₀ + BitVec.ofNat 64 256, 128⟩] m m' →
      Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] m m' := fun m m' f => f.sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  refine WP.ite (decide (16 * r < 129)) (by rw [show isa.eval .b s₁ = s₁.cf from rfl, cf₁]) (fun h => ?_) (fun h => ?_)
  · have hr8 : r ≤ 8 := by simp at h; omega_arith
    refine WP.seq (WP.mono pre fun s₂ ⟨a, g, l, m, rd, wr⟩ => ?_)
    refine WP.mono (b8 s₂ a g l m rd wr) fun s' ⟨b, _, g', rd', wr', l', f'⟩ =>
      ⟨⟨fun i hi => b i (by omega_arith), fun q h => by rw [g', g q h], by rw [rd', rd], by rw [wr', wr],
        fun x h13 h14 ha l'' hl => by rw [l' x h13 h14 ha l'' hl, l x l'' hl], by rw [← m]; exact sub128 _ _ f'⟩,
        fun _ => by rw [← m]; exact f'⟩
  · refine WP.seq (WP.mono pre fun s₂ ⟨a, g, l, m, rd, wr⟩ => ?_)
    refine WP.seq (WP.mono (b8 s₂ a g l m rd wr) fun s₃ ⟨b₃, c₃, g₃, rd₃, wr₃, l₃, f₃⟩ => ?_)
    have f₃' : Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s₃.mem := by rw [← m]; exact sub128 _ _ f₃
    refine WP.mono (ks_ok hp 12 (by decide) (c := c + 8) c₃
      (fun l' hl => by rw [l₃ _ (by decide) (by decide) (by decide) l' hl, l _ _ hl]; exact hmsk l' hl)
      (fun l' hl => by rw [l₃ _ (by decide) (by decide) (by decide) l' hl, l _ _ hl]; exact hinc l' hl)
      (kb (fun q h => by rw [g₃, g q h]) f₃' (by rw [rd₃, rd]) (by rw [wr₃, wr]))
      (by rw [g₃, g _ (by decide)]; exact hrsi) (by rw [g₃]; exact a) (by rw [g₃, g _ (by decide)]; exact h11)
      (by rw [wr₃, wr]; exact hwr)) fun s' ⟨b, _, g', rd', wr', l', f'⟩ => ?_
    refine ⟨⟨fun i hi => ?_, fun q h => by rw [g', g₃, g q h], by rw [rd', rd₃, rd], by rw [wr', wr₃, wr],
      fun x h13 h14 ha l'' hl => by rw [l' x h13 h14 ha l'' hl, l₃ x h13 h14 ha l'' hl, l x l'' hl], ?_⟩,
      fun h8 => absurd h8 (by simp at h; omega_arith)⟩
    · by_cases h8 : i < 8
      · rw [blockAt_frame f' fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
        exact b₃ i h8
      · have := b (i - 8) (by omega_arith)
        rwa [show 32 * 12 + 16 * (i - 8) = 256 + 16 * i by omega_arith, show c + 8 + (i - 8) = c + i by omega_arith] at this
    · exact f₃'.trans (f'.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)

/-- The keystream of the `r` blocks after the last group, to `scratch + 256`. -/
theorem ksSel_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15) {c : Nat} {s : State}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 2, s.lane .xmm0 l = revMask) (hinc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two)
    (hK : Keys (nr s₀) (sch s₀) s) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdi : s.gpr .rdi = kp s₀)
    (h11 : s.gpr .r11 = pp s₀) (hwr : s.wr = s₀.wr) :
    WP isa ksSel s fun s' =>
      (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (256 + 16 * i)) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem :=
  WP.mono (ksSel_okF hp hr1 hr15 h10 hctr hmsk hinc hK hrsi hrdi h11 hwr) fun _ h => h.1

/-- Before the loop: `r11` lowered by 512, `r10 = 0`, and the products cleared. -/
theorem preV_ok (s : State) :
    WP isa (.block (([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
      Impl.Gcm.X86_64.StitchAvx.zero)) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 - BitVec.ofNat 64 512 ∧ s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .r11 → q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
      (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e512 : BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 := by decide
  rw [WP.block_append_iff]
  have hA : WP isa (.block [.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)]) s fun s₁ =>
      s₁.gpr .r11 = s.gpr .r11 - BitVec.ofNat 64 512 ∧ s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .r11 → q ≠ .r10 → s₁.gpr q = s.gpr q) ∧ (∀ x l, s₁.zlane x l = s.zlane x l) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, arithFlags,
      State.setFlags, State.setReg32, isa, State.setReg, e512, reduceCtorEq, ↓reduceIte, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, rfl, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
      trivial⟩
  refine WP.mono hA fun s₁ ⟨d₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (zeroZ_ok s₁) fun s' ⟨zz, f', g', m', rd', wr'⟩ =>
    ⟨by rw [g', d₁], by rw [g', z₁], fun q h1 h2 => by rw [g', g₁ q h1 h2], zz,
      fun x h8 h9 h10 l hl => by rw [f' x h8 h9 h10 l hl, l₁], by rw [m', m₁], by rw [rd', rd₁], by rw [wr', wr₁]⟩

/-- `add r11, 512`. -/
theorem add11_ok (s : State) :
    WP isa (.block [.alu .add .r11 (.imm 512)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 + BitVec.ofNat 64 512 ∧ (∀ q, q ≠ .r11 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.lane x l = s.lane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e512 : BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e512, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The decryption loop, for any number of blocks from 16 on: it stops with
fewer than 16 left, having written only the data. -/
theorem loopDR_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordD (hk s₀) P) {s : State}
    (hI : DInv s₀ P 0 s) :
    WP isa (.loop dbody .ae) s fun s' => (∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s') ∧ Frame [dR s₀] s.mem s'.mem := by
  have h16 : 16 ≤ nb s₀ := hp.nb16
  let I : Nat → State → Prop := fun m s' => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s' ∧
    Frame [dR s₀] s.mem s'.mem
  have hstep : ∀ m s', I m s' → WP isa dbody s' (fun s'' =>
      (eval .ae s'' = some false ∧ (∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s'') ∧ Frame [dR s₀] s.mem s''.mem) ∨
      (eval .ae s'' = some true ∧ ∃ m' < m, I m' s'')) := by
    rintro m s' ⟨e, rfl, he, hI, hF⟩
    refine WP.mono (Stitch.dbodyM_okF hp.toM hf he hI.toM) fun s'' ⟨⟨hI', hcf'⟩, hF'⟩ => ?_
    have hF'' : Frame [dR s₀] s.mem s''.mem := hF.trans hF'
    by_cases hlt : nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        ⟨e + 1, hlt, hI'.toDInv⟩, hF''⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega_arith, e + 1, rfl, by omega_arith, hI'.toDInv, hF''⟩
  exact WP.loop (M := isa) I hstep (nb s₀) s ⟨0, by simp, by omega_arith, hI, Frame.refl _ _⟩

end VG.Proof.Gcm.X86_64.StitchR
