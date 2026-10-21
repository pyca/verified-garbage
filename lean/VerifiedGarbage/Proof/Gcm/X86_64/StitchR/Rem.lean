module

import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ks
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPair
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGD
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The 256-bit decryption loop: the blocks after the last group

`remD_ok`: once the decryption loop stops with `r = nb mod 16` blocks left
(`Stitch.DInv`, the groups already hashed and decrypted), `StitchR.remD`
stores the counter after all the blocks (`StitchZH.remSetup_ok`), computes the
keystream of eight or sixteen blocks to `scratch + 256` (`ksSel_ok`), then
hashes each block as read and decrypts it, the first alone if their number is
odd and the rest two at a time (`remMid_ok`, `RemPair.lean`, with `r11`
lowered by 512 so that the loop's keystream at `r11 + 768` is at
`scratch + 256`), adds the products of the two lanes (`foldLanes_ok`),
reduces them into `Y` (`StitchAvx.reduceHash_ok`),
and stores `Y`, for powers whose products add up to `GHASH` (`RemLaw`, which
`Ok.lean` proves of the prepared powers). `decTailR_ok` is `decR` after its
setup.
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

/-- The keystream of the `r` blocks after the last group, to `scratch + 256`. -/
theorem ksSel_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15) {c : Nat} {s : State}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 2, s.lane .xmm0 l = revMask) (hinc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two)
    (hK : Keys (nr s₀) (sch s₀) s) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdi : s.gpr .rdi = kp s₀)
    (h11 : s.gpr .r11 = pp s₀) (hwr : s.wr = s₀.wr) :
    WP isa ksSel s fun s' =>
      (∀ i < r, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (256 + 16 * i)) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem := by
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
      ⟨fun i hi => b i (by omega_arith), fun q h => by rw [g', g q h], by rw [rd', rd], by rw [wr', wr],
        fun x h13 h14 ha l'' hl => by rw [l' x h13 h14 ha l'' hl, l x l'' hl], by rw [← m]; exact sub128 _ _ f'⟩
  · refine WP.seq (WP.mono pre fun s₂ ⟨a, g, l, m, rd, wr⟩ => ?_)
    refine WP.seq (WP.mono (b8 s₂ a g l m rd wr) fun s₃ ⟨b₃, c₃, g₃, rd₃, wr₃, l₃, f₃⟩ => ?_)
    have f₃' : Frame [⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s₃.mem := by rw [← m]; exact sub128 _ _ f₃
    refine WP.mono (ks_ok hp 12 (by decide) (c := c + 8) c₃
      (fun l' hl => by rw [l₃ _ (by decide) (by decide) (by decide) l' hl, l _ _ hl]; exact hmsk l' hl)
      (fun l' hl => by rw [l₃ _ (by decide) (by decide) (by decide) l' hl, l _ _ hl]; exact hinc l' hl)
      (kb (fun q h => by rw [g₃, g q h]) f₃' (by rw [rd₃, rd]) (by rw [wr₃, wr]))
      (by rw [g₃, g _ (by decide)]; exact hrsi) (by rw [g₃]; exact a) (by rw [g₃, g _ (by decide)]; exact h11)
      (by rw [wr₃, wr]; exact hwr)) fun s' ⟨b, _, g', rd', wr', l', f'⟩ => ?_
    refine ⟨fun i hi => ?_, fun q h => by rw [g', g₃, g q h], by rw [rd', rd₃, rd], by rw [wr', wr₃, wr],
      fun x h13 h14 ha l'' hl => by rw [l' x h13 h14 ha l'' hl, l₃ x h13 h14 ha l'' hl, l x l'' hl], ?_⟩
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

theorem remD_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hr : RemLaw (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) remD) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega_arith
  have hr15 : r ≤ 15 := by omega_arith
  refine WP.seq (WP.mono (add9_ok s) fun s' ⟨a9, ga, la, ma, rda, wra⟩ => ?_)
  have la' : ∀ x l, l < 2 → s'.lane x l = s.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, la]
  have hr9 : s'.gpr .r9 = BitVec.ofNat 64 (16 + r) := by
    rw [a9, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    congr 1; omega_arith
  have hrax : s'.gpr .rax = cp s₀ := by rw [ga _ (by decide)]; exact hI.rax
  have hr11 : s'.gpr .r11 = pp s₀ := by
    rw [ga _ (by decide)]; exact hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show remD = .seq (.block Impl.Gcm.X86_64.StitchZH.remSetup) (.seq ksSel
      (.seq (.block ((([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
          Impl.Gcm.X86_64.StitchAvx.zero) ++ ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)])
            (.block (Impl.Gcm.X86_64.StitchZH.remBodyD .rdx ++ Impl.Gcm.X86_64.StitchZH.remNext)))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (Impl.Gcm.X86_64.StitchR.remPairD ++
              Impl.Gcm.X86_64.StitchR.remNextPair)) .ne) (.block Impl.Gcm.X86_64.StitchR.foldLanes)))
            (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr) ++
              storeY)))))) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (remSetup_ok s' hr1 hr15 hr9
    (by rw [la' _ _ (by decide)]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, wra, hI.a.wr]; exact in_sub_int hp.c_in (by omega_arith)))
    fun s₁ ⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0, ma] at m₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → s₁.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₁ q h1 h2, ga q h3]
  have lk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 2, s₁.lane x l = s.lane x l := fun x h l hl => by
    rw [← State.zlane_lt2 _ _ hl, z₁ x h l (by omega_arith), State.zlane_lt2 _ _ hl, la' x l hl]
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, rda]; exact hI.a.rd
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, wra]; exact hI.a.wr
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rdi
  -- The keystream.
  refine WP.seq (WP.mono (ksSel_ok hp hr1 hr15 (c := 16 * e) a10₁
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.inc l hl)
    (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
    (by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rsi) hrdi₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr11) hwr₁)
    fun s₂ ⟨ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  -- `r11` lowered, `r10 = 0`, the products cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preV_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  have gk₃ : ∀ q, q ≠ .r10 → q ≠ .r11 → q ≠ .rax → q ≠ .r9 → s₃.gpr q = s.gpr q := fun q h1 h11 h2 h3 => by
    rw [g₃ q h11 h1, g₂ q h1, gk₁ q h1 h2 h3]
  have lk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 2, s₃.lane x l = s.lane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₃ x h8 h9 h10 l (by omega_arith), State.zlane_lt2 _ _ hl, l₂ x h13 h14 ha l hl,
      lk₁ x h13 l hl]
  have h11₃ : s₃.gpr .r11 = pp s₀ - BitVec.ofNat 64 512 := by
    rw [d₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), hr11]
  have eK : ∀ j, pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j) =
      pp s₀ + BitVec.ofNat 64 (256 + 16 * j) := fun j => by
    rw [show 768 + 16 * j = 512 + (256 + 16 * j) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀ - BitVec.ofNat 64 512)
    (pp s₀ + BitVec.ofNat 64 (256 - 16 * r)) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  have hE : E.Ok :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA, gP := h11₃
      gW := by show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega_arith)
      inW := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [eK]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)) }
  have hI₃ : RInvD E 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := by
        obtain ⟨a, b, c⟩ := p₃ 0 (by decide)
        simp only [prod, State.proj_xmm, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), a, b, c]
        rfl
      y := rfl
      m0 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.a.msk 0 (by decide)
      m1 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.m1 0 (by decide) }
  have hE2 : Ok2 E :=
    { inS := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 32
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j + 2 ≤ r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega)
      inW := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega)) }
  have z1 : ∀ x, s₃.zlane x 1 = 0 → s₃.lane x 1 = 0 := fun x h => by rw [← State.zlane_lt2 _ _ (by decide)]; exact h
  -- The first block alone if `r` is odd, then the pairs and their lanes added.
  refine remMid_ok hE hE2 rfl hI₃ (z1 _ (p₃ 1 (by decide)).1) (z1 _ (p₃ 1 (by decide)).2.1)
    (z1 _ (p₃ 1 (by decide)).2.2)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]; exact hI.y1)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]
        exact hI.a.msk 1 (by decide)) fun s₄ hI₄ => ?_
  -- The products reduced into `Y`, `r11` restored, and `Y` stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add11_ok s₅) fun s₆ ⟨a11, g₆, l₆, m₆, rd₆, wr₆⟩ => ?_
  have hrcx : s₆.gpr .rcx = yp s₀ := by
    rw [g₆ _ (by decide), f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  have m06 : s₆.lane .xmm0 0 = revMask := by
    rw [l₆, f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₆ m06
    (by rw [hrcx, wr₆, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, l₆, y₅] at m₇
  have hm₆ : s₆.mem = s₄.mem := by rw [m₆, f₅.mem]
  have hnb : nb s₀ = 16 * e + r := by omega_arith
  -- What the stages keep of the memory before them.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) →
      Region.Disjoint ⟨p, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  have hS : ∀ j < r, blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) :=
    fun j hj => by
      have hk : 16 * e + j < nb s₀ := by omega_arith
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk]
      simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The blocks.
  have hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      have hj : j < r := by omega_arith
      have ct := hI₄.ct j hj
      have eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct]
      show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
        blockAt s₃.mem (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) = _
      rw [hS j hj, eK, m₃, ks₂ j hj]
  have hH : ∀ j < r, E.H j = blk s₀ (16 * e + j) := fun j hj => hS j hj
  have hT : ∀ j < r, E.T j = P ((16 - r + j) / 2) ((16 - r + j) % 2) := fun j hj => by
    show s₃.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [Offset.add_add, show 256 - 16 * r + 16 * j = 32 * ((16 - r + j) / 2) + 16 * ((16 - r + j) % 2) by omega_arith,
      m₃, f₂.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (32 * ((16 - r + j) / 2) + 16 * ((16 - r + j) % 2)), 16⟩)
        (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))).sep
          (Region.contains_self _ _) cw) (by decide)]
    exact hI.pw _ (by omega_arith) _ (by omega_arith)
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  have hb : ∀ k < nb s₀, blockAt s₇.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hm₆, hb₄ k hk]
  have fA : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  have hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀)) := by
    rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₇.mem (cp s₀) = _
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl, hm₆,
      blockAt_frame hI₄.frame (fA _ hp.d_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), la, State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₇.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₀.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (blk s₀) := rfl
    rw [hbl, m₇, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.prod, accR_congr _ r hH hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₇.mem
    have F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    have F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    have F3 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    rw [m₇, hm₆]
    exact (((F0.trans F1).trans F2).trans F3).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₇.gpr q = _
    by_cases h11 : q = .r11
    · subst h11
      rw [g₇, a11, f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
      show s₃.gpr .r11 + BitVec.ofNat 64 512 = _
      rw [h11₃, BitVec.sub_add_cancel]
    · rw [g₇, g₆ q h11, f₅.gpr, hI₄.gpr q h3 h4]
      show s₃.gpr q = _
      rw [gk₃ q h4 h11 h1 h3]
      exact hI.gpr q h1 h2 h3 h4
  · show s₇.rd = _
    rw [rd₇, rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₇.wr = _
    rw [wr₇, wr₆, f₅.wr, hI₄.wr]; exact hwr₃

/-- The decryption loop, for any number of blocks from 16 on: it stops with
fewer than 16 left. -/
theorem loopDR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordD (hk s₀) P) {s : State}
    (hI : DInv s₀ P 0 s) :
    WP isa (.loop dbody .ae) s fun s' => ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' := by
  have h16 : 16 ≤ nb s₀ := hp.nb16
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (dbody_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true], e + 1, hlt, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega_arith, e + 1, rfl, by omega_arith, hI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀) s ⟨0, by simp, by omega_arith, hI⟩

/-- `decR` after the setup, for any number of blocks from 16 on. -/
theorem decTailR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordD (hk s₀) P)
    (hr : RemLaw (hk s₀) P) {s₁ : State} (hR : Ready s₀ P s₁) :
    WP isa (.seq (.loop dbody .ae) (.seq (.block [.alu .test .r9 (.reg .r9)])
      (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remD)))) s₁ (DPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hI₁ : DInv s₀ P 0 s₁ :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  refine WP.seq (WP.mono (loopDR_ok hp hf hI₁) fun s₅ ⟨e, hlt, hI₅⟩ => ?_)
  have hle₅ := hI₅.a.le
  refine WP.seq (WP.mono (test99_ok s₅) fun s₆ ⟨z₆, g₆, l₆, m₆, rd₆, wr₆⟩ => ?_)
  have yf : YFrame [] s₅ s₆ :=
    ⟨g₆, m₆, rd₆, wr₆, fun x _ l hl => by rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₆]⟩
  have hI₆ : DInv s₀ P e s₆ :=
    ⟨hI₅.a.yframe yf (by simp) (by simp) (by simp), by rw [g₆]; exact hI₅.rdx, by rw [g₆]; exact hI₅.r9,
      by rw [g₆]; exact hI₅.rax, fun r h1 h2 h3 h4 => by rw [g₆]; exact hI₅.gpr r h1 h2 h3 h4,
      fun k hk l hl => by rw [m₆]; exact hI₅.pw k hk l hl, fun l hl => by rw [yf.lane _ (by simp) l hl]; exact hI₅.m1 l hl,
      by rw [yf.lane _ (by simp) 0 (by decide)]; exact hI₅.y, by rw [yf.lane _ (by simp) 1 (by decide)]; exact hI₅.y1⟩
  have hz : (s₅.gpr .r9 &&& s₅.gpr .r9 == 0) = decide (nb s₀ = 16 * e) := by
    rw [BitVec.and_self, hI₅.r9]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * e = 0 by omega_arith, decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * e) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_arith
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₆, hz]) (fun h => ?_) (fun h => ?_)
  · exact dfinal_ok hp (by simpa using h) hI₆
  · exact remD_ok hp hr hI₆ hlt (by simpa using h)

end VG.Proof.Gcm.X86_64.StitchR
