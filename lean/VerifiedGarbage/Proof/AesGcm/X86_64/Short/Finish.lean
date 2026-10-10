import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec

/-!
# AES-GCM on x86-64 with AVX-512: the end of a long `seal`

Untrusted: everything here is checked by Lean. After `oneBlocks`, `finish`
(`Impl.AesGcm.X86_64.Short`) leaves what `oneCrypt` and `oneTag 0` do
(`sealBody_ok`), without calls: `H'` and `H'²` (`ShortFacts.finPow`, from
`Pow.lean`, which imports the field's algebra), the
keystream of `J₀` and of the counter block (`finKs_ok`), the bytes left
encrypted in place and copied to `G[0]` (`xorText_ok`), the lengths block at
`G[1]` (`finLens_ok`), `GHASH` continued over `G` from the state's
accumulator (`finGh2_ok`, `finGh1_ok`), and the tag (`tagK_ok`):
`sealBodyF_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (ldrev_ok Only)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)
open VG.Proof.Aes.X86_64.VaesZ (aesZ_ok blockAt_writeW_lane zmm_lane)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq st)
open VG.Spec.Aes (cipher)

/-! ## The keystream of `J₀` and of the counter block -/

/-- `r10 := 16 rsi + rdi`, by doubling four times. -/
theorem dbl4 (nr : Nat) (C : Addr) :
    BitVec.ofNat 64 nr + BitVec.ofNat 64 nr + (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr) +
        (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr + (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr)) +
      (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr + (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr) +
        (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr + (BitVec.ofNat 64 nr + BitVec.ofNat 64 nr))) + C =
      C + BitVec.ofNat 64 (16 * nr) := by
  rw [BitVec.add_comm _ C]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The two loads and the insert of `finCtrs`. -/
theorem finLanes_ok {St : Addr} (s : State) (h14 : s.gpr .r14 = St)
    (r0 : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 0) 16)
    (r48 : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 48) 16) :
    ∃ t, runBlock isa [.vmovdquLoad .l128 .xmm5 (at_ .r14 0), .vmovdquLoad .l128 .xmm7 (at_ .r14 48),
        .vop (.vinserti128 .xmm5 .xmm5 .xmm7 1)] s = some t ∧
      t.zlane .xmm5 0 = s.mem.readW St 128 ∧ t.zlane .xmm5 1 = s.mem.readW (St + BitVec.ofNat 64 48) 128 ∧
      t.zlane .xmm5 2 = 0 ∧ t.zlane .xmm5 3 = 0 ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  have e0 : s.gpr .r14 + BitVec.ofInt 64 ((0 : Nat) : Int) = St + BitVec.ofNat 64 0 := by
    rw [h14, BitVec.ofInt_natCast]
  have e48 : s.gpr .r14 + BitVec.ofInt 64 ((48 : Nat) : Int) = St + BitVec.ofNat 64 48 := by
    rw [h14, BitVec.ofInt_natCast]
  refine ⟨_, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.load128, State.ea,
      State.setV, e0, e48, r0, r48, ite_true, Option.map_some, Option.bind_some, State.lane, reduceCtorEq,
      ↓reduceIte, show (1 : BitVec 8).getLsbD 0 = true from rfl]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, fun r a b l hl => ?_⟩
  · simp [State.zlane, State.lane, State.setV]
  · simp [State.zlane, State.lane, State.setV]
  · simp [State.zlane, State.lane, State.setV]
  · simp [State.zlane, State.lane, State.setV]
  · rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
      simp [State.zlane, State.lane, State.setV, a, b]

/-- `finCtrs`: `J₀` and the counter block in the first two lanes of `zmm5`
(the others zero), and `aesZ`'s registers. -/
theorem finCtrs_ok {Ctx St W SP : Addr} {nr : Nat} (s : State) (he : Env Ctx St W SP s)
    (hR : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr) :
    ∃ t, runBlock isa finCtrs s = some t ∧
      t.zlane .xmm5 0 = s.mem.readW St 128 ∧ t.zlane .xmm5 1 = s.mem.readW (St + BitVec.ofNat 64 48) 128 ∧
      t.zlane .xmm5 2 = 0 ∧ t.zlane .xmm5 3 = 0 ∧
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  obtain ⟨s₁, run₁, z0, z1, z2, z3, g₁, m₁, rd₁, wr₁, k₁⟩ := finLanes_ok s he.r14 (he.perm.stR (by decide))
    (he.perm.stR (by decide))
  have r176 : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 176) 8 := by
    rw [rd₁, wr₁]; exact he.perm.wR (by decide)
  have d4 := dbl4 nr Ctx
  obtain ⟨t, run₂, di, si, r10, g₂, m₂, rd₂, wr₂, x₂, y₂, z₂⟩ : ∃ t, runBlock isa
      [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .r10 (.reg .rsi),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] s₁ = some t ∧
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s₁.gpr r) ∧ t.mem = s₁.mem ∧ t.rd = s₁.rd ∧
      t.wr = s₁.wr ∧ t.xmm = s₁.xmm ∧ t.ymmHi = s₁.ymmHi ∧ t.zmmHi = s₁.zmmHi := by
    refine ⟨_, by xrun [g₁, he.r13, he.r15, r176, m₁, hR, d4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp [gpr_setReg, gpr_arithFlags, g₁, he.r13, he.r15, m₁, hR, d4]; done)
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals rfl
  have run : runBlock isa finCtrs s = some t := by
    rw [show finCtrs = [.vmovdquLoad .l128 .xmm5 (at_ .r14 0), .vmovdquLoad .l128 .xmm7 (at_ .r14 48),
        .vop (.vinserti128 .xmm5 .xmm5 .xmm7 1)] ++ [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
        .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] from rfl,
      runBlock_append, run₁]
    exact run₂
  have zl : ∀ r l, t.zlane r l = s₁.zlane r l := fun r l => by simp only [State.zlane, State.lane, x₂, y₂, z₂]
  refine ⟨t, run, by rw [zl, z0], by rw [zl, z1], by rw [zl, z2], by rw [zl, z3], di, si, r10,
    fun r a b c => by rw [g₂ r a b c, g₁], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    fun r a b l hl => by rw [zl, k₁ r a b l hl]⟩

/-- The keystream block of a block loaded into a lane. -/
theorem ks_lane {nr : Nat} {w : List Byte} {R L : BitVec 128} {m : Mem} {a : Addr} (hL : L = m.readW a 128)
    (h : st R = cipher nr w (st L)) :
    XBinOp.eval .pshufb R revMask = aesWith nr w (blockAt m a) := by
  refine (aesWith_eq nr w _ R ?_).symm
  rw [h, hL, VG.Proof.Gcm.X86_64.blockAt_eq, VG.Proof.Gcm.X86_64.pshufb_rev_rev]

/-- `finKs`: the keystream of `J₀` and of the counter block (the state's
first and fourth blocks) at `K = W + 1024`. -/
theorem finKs_ok {Ctx W SP : Addr} {nr : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hR : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr) (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) :
    WP isa finKs s fun t =>
      blockAt t.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx nr (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
      blockAt t.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
        ciphOf s.mem Ctx nr (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      Frame [⟨W + BitVec.ofNat 64 1024, 64⟩] s.mem t.mem ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → r ≠ .xmm13 → t.xmm r = s.xmm r) := by
  obtain ⟨s₁, run₁, z0, z1, z2, z3, di₁, si₁, r10₁, g₁, m₁, rd₁, wr₁, k₁⟩ := finCtrs_ok s he hR
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  generalize hw : bytesAt s.mem Ctx (16 * (nr + 1)) = w
  have hK : Keys nr w s₁ := ⟨by rw [di₁, m₁, hw], by omega, fun j hj => by
    rw [rd₁, wr₁, di₁, BitVec.ofInt_natCast]; exact he.perm.ctxR (by omega)⟩
  refine WP.seq (WP.mono (aesZ_ok .xmm13 [.xmm5] (by decide) (by decide) hnr (fun _ => []) [] (by simp)
    (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial)
    s₁ hK trivial si₁ (by rw [r10₁, di₁])) fun s₂ ⟨e₂, _, f₂⟩ => ?_)
  have hw₂ : InRegions s₂.wr (W + BitVec.ofNat 64 1024) 64 := by rw [f₂.wr, wr₁]; exact he.perm.wW (by decide)
  have ea : s₂.gpr .r15 + BitVec.ofInt 64 ((kO : Nat) : Int) = W + BitVec.ofNat 64 1024 := by
    rw [f₂.gpr, g₁ _ (by decide) (by decide) (by decide), he.r15, BitVec.ofInt_natCast]; rfl
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, State.store512_eq, State.ea, ea,
      hw₂, ite_true, Option.bind_some]
    rfl, ?_⟩
  have L0 := e₂ .xmm5 (List.mem_singleton_self _) 0 (by decide)
  have L1 := e₂ .xmm5 (List.mem_singleton_self _) 1 (by decide)
  have hc : ciphOf s.mem Ctx nr = aesWith nr w := by rw [← hw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setMem]
    have e := blockAt_writeW_lane s₂.mem (W + BitVec.ofNat 64 1024) (s₂.zmm .xmm5) (l := 0) (by decide)
    rw [Nat.mul_zero, BitVec.add_zero] at e
    rw [e, show BitVec.extractLsb' 0 128 (s₂.zmm .xmm5) = s₂.zlane .xmm5 0 from zmm_lane s₂ .xmm5 (l := 0) (by decide),
      hc]
    exact ks_lane z0 L0
  · simp only [State.setMem]
    rw [blockAt_writeW_lane _ _ _ (l := 1) (by decide), zmm_lane _ _ (by decide), hc]
    exact ks_lane z1 L1
  · simp only [State.setMem]
    rw [f₂.mem, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · intro r a b c; simp only [State.setMem]; rw [f₂.gpr, g₁ r a b c]
  · simp only [State.setMem]; rw [f₂.rd, rd₁]
  · simp only [State.setMem]; rw [f₂.wr, wr₁]
  · intro r a b c
    have h₁ : s₂.xmm r = s₁.xmm r := by
      simpa [State.zlane, State.lane] using f₂.zlane r (by simp [a, c]) 0 (by decide)
    have h₂ : s₁.xmm r = s.xmm r := by simpa [State.zlane, State.lane] using k₁ r a b 0 (by decide)
    simp only [State.setMem]
    rw [h₁, h₂]

/-- What `finishWith` needs of its keystream program `ks`: `finKs_ok`'s
effect, with `xmm8` also written (`AesNi.aes`'s round key). -/
def KsOk (ks : Prog isa) : Prop :=
  ∀ {Ctx W SP : Addr} {nr : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr → (nr = 10 ∨ nr = 12 ∨ nr = 14) →
    WP isa ks s fun t =>
      blockAt t.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx nr (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
      blockAt t.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
        ciphOf s.mem Ctx nr (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      Frame [⟨W + BitVec.ofNat 64 1024, 64⟩] s.mem t.mem ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm13 → t.xmm r = s.xmm r)

theorem finKs_ksOk : KsOk finKs := fun s he hR hnr =>
  WP.mono (finKs_ok s he hR hnr) fun _ ⟨a, b, c, d, e, f, g⟩ =>
    ⟨a, b, c, d, e, f, fun r h5 h7 _ h13 => g r h5 h7 h13⟩

/-! ## `GHASH` of `G` from the state's accumulator -/

/-- `pxor xmm7, xmm12`. -/
theorem pxor712_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm7 .xmm12)]) s fun s' =>
      s'.xmm .xmm7 = s.xmm .xmm7 ^^^ s.xmm .xmm12 ∧ Only [.xmm7] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- With bytes left: `GHASH` over `G[0]` and `G[1]` from the state's `Y`, into
`xmm2`. -/
theorem finGh2_ok {Ctx St W SP : Addr} {H : Block} (s : State) (he : Env Ctx St W SP s)
    (x0 : s.xmm .xmm0 = revMask) (x1 : s.xmm .xmm1 = poly) (h2 : IsH2 H (s.xmm .xmm3) (s.xmm .xmm6)) :
    WP isa (.block finGh2) s fun t =>
      t.xmm .xmm2 = Spec.Gcm.ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 16))
        [blockAt s.mem (W + BitVec.ofNat 64 512), blockAt s.mem (W + BitVec.ofNat 64 528)] ∧
      Only [.xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t := by
  have eY : s.gpr .r14 + BitVec.ofInt 64 ((16 : Nat) : Int) = St + BitVec.ofNat 64 16 := by
    rw [he.r14, BitVec.ofInt_natCast]
  have eG : ∀ d, s.gpr .r15 + BitVec.ofInt 64 ((d : Nat) : Int) = W + BitVec.ofNat 64 d := fun d => by
    rw [he.r15, BitVec.ofInt_natCast]
  simp only [finGh2, finY, gO, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm12 .r14 16 s (by decide) x0 (by rw [eY]; exact he.perm.stR (by decide)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [eY] at l₁
  rw [show ([.movdquLoad .xmm7 (at_ .r15 512), .xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pxor .xmm7 .xmm12)] ++
      _ : List Instr) = [.movdquLoad .xmm7 (at_ .r15 512), .xop (.bin .pshufb .xmm7 .xmm0)] ++
      ([.xop (.bin .pxor .xmm7 .xmm12)] ++ _) from rfl, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r15 512 s₁ (by decide) (by rw [o₁.xmm _ (by decide), x0])
    (by rw [o₁.rd, o₁.wr, o₁.gpr _ (by decide), eG]; exact he.perm.wR (by decide))) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [o₁.gpr _ (by decide), eG, o₁.mem] at l₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor712_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.zero_ok s₃) fun s₄ ⟨p₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.acc_ok .xmm7 .xmm6 s₄ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨p₅, o₅⟩ => ?_
  have O₄ := o₁.trans (o₂.trans (o₃.trans o₄))
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r15 528 s₅ (by decide) (by rw [(O₄.trans o₅).xmm _ (by decide), x0])
    (by rw [(O₄.trans o₅).rd, (O₄.trans o₅).wr, (O₄.trans o₅).gpr _ (by decide), eG]; exact he.perm.wR (by decide)))
    fun s₆ ⟨l₆, o₆⟩ => ?_
  rw [(O₄.trans o₅).gpr _ (by decide), eG, (O₄.trans o₅).mem] at l₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.acc_ok .xmm7 .xmm3 s₆ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₇ ⟨p₇, o₇⟩ => ?_
  have O₇ := (O₄.trans o₅).trans (o₆.trans o₇)
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.reduce_ok .xmm2 s₇ (by decide) (by decide) (by decide) (by decide)
    (by rw [O₇.xmm _ (by decide), x1])) fun t ⟨r, o⟩ => ⟨?_, (O₇.trans o).weaken fun r hr => ?_⟩
  · have v7 : s₄.xmm .xmm7 = blockAt s.mem (St + BitVec.ofNat 64 16) ^^^ blockAt s.mem (W + BitVec.ofNat 64 512) := by
      rw [o₄.xmm _ (by decide), l₃, l₂, o₂.xmm _ (by decide), l₁, BitVec.xor_comm]
    have v6 : s₄.xmm .xmm6 = s.xmm .xmm6 := O₄.xmm _ (by decide)
    have v3 : s₆.xmm .xmm3 = s.xmm .xmm3 := ((O₄.trans o₅).trans o₆).xmm _ (by decide)
    rw [r, p₇, o₆.prod (by decide) (by decide) (by decide), p₅, p₄, l₆, v7, v6, v3]
    exact h2 _ _ _
  · revert hr; cases r <;> decide

/-- Without bytes left: `GHASH` over `G[1]` from the state's `Y`, into `xmm2`. -/
theorem finGh1_ok {Ctx St W SP : Addr} {H : Block} (s : State) (he : Env Ctx St W SP s)
    (x0 : s.xmm .xmm0 = revMask) (x1 : s.xmm .xmm1 = poly) (h1 : IsH1 H (s.xmm .xmm3)) :
    WP isa (.block finGh1) s fun t =>
      t.xmm .xmm2 = Spec.Gcm.ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 16))
        [blockAt s.mem (W + BitVec.ofNat 64 528)] ∧
      Only [.xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t := by
  have eY : s.gpr .r14 + BitVec.ofInt 64 ((16 : Nat) : Int) = St + BitVec.ofNat 64 16 := by
    rw [he.r14, BitVec.ofInt_natCast]
  have eG : ∀ d, s.gpr .r15 + BitVec.ofInt 64 ((d : Nat) : Int) = W + BitVec.ofNat 64 d := fun d => by
    rw [he.r15, BitVec.ofInt_natCast]
  simp only [finGh1, finY, gO, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm12 .r14 16 s (by decide) x0 (by rw [eY]; exact he.perm.stR (by decide)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [eY] at l₁
  rw [show ([.movdquLoad .xmm7 (at_ .r15 (512 + 16)), .xop (.bin .pshufb .xmm7 .xmm0),
      .xop (.bin .pxor .xmm7 .xmm12)] ++ _ : List Instr) = [.movdquLoad .xmm7 (at_ .r15 528),
      .xop (.bin .pshufb .xmm7 .xmm0)] ++ ([.xop (.bin .pxor .xmm7 .xmm12)] ++ _) from rfl, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r15 528 s₁ (by decide) (by rw [o₁.xmm _ (by decide), x0])
    (by rw [o₁.rd, o₁.wr, o₁.gpr _ (by decide), eG]; exact he.perm.wR (by decide))) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [o₁.gpr _ (by decide), eG, o₁.mem] at l₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor712_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.zero_ok s₃) fun s₄ ⟨p₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.acc_ok .xmm7 .xmm3 s₄ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨p₅, o₅⟩ => ?_
  have O₅ := o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))
  refine WP.mono (VG.Proof.Gcm.X86_64.Pclmul.reduce_ok .xmm2 s₅ (by decide) (by decide) (by decide) (by decide)
    (by rw [O₅.xmm _ (by decide), x1])) fun t ⟨r, o⟩ => ⟨?_, (O₅.trans o).weaken fun r hr => ?_⟩
  · have v7 : s₄.xmm .xmm7 = blockAt s.mem (St + BitVec.ofNat 64 16) ^^^ blockAt s.mem (W + BitVec.ofNat 64 528) := by
      rw [o₄.xmm _ (by decide), l₃, l₂, o₂.xmm _ (by decide), l₁, BitVec.xor_comm]
    have v3 : s₄.xmm .xmm3 = s.xmm .xmm3 := (o₁.trans (o₂.trans (o₃.trans o₄))).xmm _ (by decide)
    rw [r, p₅, p₄, v7, v3]
    exact h1 _ _
  · revert hr; cases r <;> decide

/-! ## The text's arguments and the lengths block -/

/-- A 16-byte store of zero is a write of 16 zero bytes. -/
theorem writeW_zero128 (m : Mem) (a : Addr) : m.writeW a (0 : BitVec 128) = writeBytes m a (List.replicate 16 0) := by
  rw [Mem.writeW, write_eq_writeBytes]
  refine congrArg (writeBytes m a) ?_
  apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_replicate])
  intro j h₁ h₂
  rw [List.getElem_map, List.getElem_replicate]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, getLsbD_zero', Bool.and_false]

/-- `finTextArgs`: `G[0]` zeroed, and the arguments of `xorText true`. -/
theorem finTextArgs_ok {Ctx St W SP D : Addr} {r : Nat} (s : State) (he : Env Ctx St W SP s)
    (hd : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hl : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r) :
    ∃ t, runBlock isa finTextArgs s = some t ∧
      t.mem = writeBytes s.mem (W + BitVec.ofNat 64 512) (List.replicate 16 0) ∧
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
      t.gpr .rcx = BitVec.ofNat 64 r ∧
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ q, q ≠ .xmm7 → t.xmm q = s.xmm q) := by
  have w512 : InRegions s.wr (W + BitVec.ofNat 64 512) 16 := he.perm.wW (by decide)
  have e512 : s.gpr .r15 + BitVec.ofInt 64 ((512 : Nat) : Int) = W + BitVec.ofNat 64 512 := by
    rw [he.r15, BitVec.ofInt_natCast]
  obtain ⟨s₁, run₁, m₁, x₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.xop (.bin .pxor .xmm7 .xmm7),
      .movdquStore (at_ .r15 gO) .xmm7] s = some s₁ ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 512) (0 : BitVec 128) ∧
      (∀ q, q ≠ .xmm7 → s₁.xmm q = s.xmm q) ∧ s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [gO, at_, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
        State.store128, State.ea, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, BitVec.xor_self, e512, w512, ite_true,
        Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [State.setMem, State.setXmm]
    · intro q hq; simp [State.setMem, State.setXmm, hq]
    all_goals rfl
  have sep : ∀ d, d + 8 ≤ 512 → (s.mem.writeW (W + BitVec.ofNat 64 512) (0 : BitVec 128)).readW
      (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h =>
    Mem.readW_writeW_sep (Offset.sep W (.inl (by omega)) (by omega) (by have := he.perm.w; omega)) (by decide)
  have r200 : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 200) 8 := by
    rw [rd₁, wr₁]; exact he.perm.wR (by decide)
  have r208 : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 208) 8 := by
    rw [rd₁, wr₁]; exact he.perm.wR (by decide)
  have h200 := sep 200 (by decide)
  have h208 := sep 208 (by decide)
  rw [hd] at h200
  rw [hl] at h208
  obtain ⟨t, run₂, di, si, dx, cx, g₂, m₂, rd₂, wr₂, x₂⟩ : ∃ t, runBlock isa (ptr .rdi .r15 gO ++
      [.mov .rsi (.mem (at_ .r15 dataO))] ++ ptr .rdx .r15 (kO + 16) ++ [.mov .rcx (.mem (at_ .r15 lenO))]) s₁ =
      some t ∧ t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
      t.gpr .rcx = BitVec.ofNat 64 r ∧
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → t.gpr g = s₁.gpr g) ∧ t.mem = s₁.mem ∧ t.rd = s₁.rd ∧
      t.wr = s₁.wr ∧ t.xmm = s₁.xmm := by
    refine ⟨_, by xrun [g₁, he.r15, r200, r208, m₁, h200, h208, kO, gO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp [gpr_setReg, gpr_arithFlags, g₁, he.r15, m₁, h200, h208]; done)
    · intro g a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
    all_goals rfl
  refine ⟨t, ?_, by rw [m₂, m₁, writeW_zero128], di, si, dx, cx, fun g a b c d => by rw [g₂ g a b c d, g₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun q hq => by rw [x₂, x₁ q hq]⟩
  rw [show finTextArgs = [.xop (.bin .pxor .xmm7 .xmm7), .movdquStore (at_ .r15 gO) .xmm7] ++
    (ptr .rdi .r15 gO ++ [.mov .rsi (.mem (at_ .r15 dataO))] ++ ptr .rdx .r15 (kO + 16) ++
      [.mov .rcx (.mem (at_ .r15 lenO))]) from rfl, runBlock_append, run₁, Option.bind_some]
  exact run₂

/-- `finLens`: the lengths block at `G[1]`. -/
theorem finLens_ok {Ctx St W SP : Addr} {al n : Nat} (s : State) (he : Env Ctx St W SP s)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hn : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n) :
    ∃ t, runBlock isa finLens s = some t ∧
      Frame [⟨W + BitVec.ofNat 64 528, 16⟩] s.mem t.mem ∧
      bytesAt t.mem (W + BitVec.ofNat 64 528) 16 = Proof.Gcm.lensBlock al n ∧
      (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm = s.xmm := by
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := he.perm.wR (by decide)
  have r₃ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 192) 8 := he.perm.wR (by decide)
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 528) 8 := he.perm.wW (by decide)
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 528 + BitVec.ofNat 64 8) 8 := by
    rw [add_ofNat_ofNat]; exact he.perm.wW (by decide)
  have shl3 : ∀ a : Nat, BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := fun a => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have e₂ := shl3 al
  have e₃ := shl3 n
  have e536 : W + BitVec.ofNat 64 536 = W + BitVec.ofNat 64 528 + BitVec.ofNat 64 8 := by rw [add_ofNat_ofNat]
  refine ⟨_, by xrun [finLens, execShift, he.r15, hal, hn, r₂, r₃, gO, e₂, e₃, w₁, w₂, e536], ?_⟩
  have rdn : ∀ v : BitVec 64, (s.mem.writeW (W + BitVec.ofNat 64 528) v).readW (W + BitVec.ofNat 64 192) 64 =
      BitVec.ofNat 64 n :=
    fun v => by
      rw [Mem.readW_writeW_sep (Offset.sep W (.inl (by omega)) (by omega) (by omega)) (by decide), hn]
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
    rw [rdn, e₃, Proof.Cmac.bytesAt_store2, bswap64_eq, Proof.Gcm.le8_byteRev64, Proof.Gcm.le8_byteRev64,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl
  · intro g a; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a]

/-- The test of the bytes left. -/
theorem finTest_ok {Ctx St W SP : Addr} {r : Nat} (hr : r < 2 ^ 64) (s : State) (he : Env Ctx St W SP s)
    (hl : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (decide (r = 0)) ∧ (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have hz := and_self_beq hr
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hz]
  · intro g hg; simp [gpr_setReg, gpr_arithFlags, hg]
  all_goals rfl

/-! ## The ends of `finish` -/

/-- What both ends of `finish` start from: `H'` and `H'²`, the slots of `W`,
and the `r < 16` bytes left at `D`. -/
structure FinPre (Ctx W SP : Addr) (H : Block) (al n r : Nat) (D : Addr) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  h1 : IsH1 H (s.xmm .xmm3)
  h2 : IsH2 H (s.xmm .xmm3) (s.xmm .xmm6)
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r
  r16 : r < 16
  rd : Covers [⟨D, r⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, r⟩] s.wr
  dW : (⟨D, r⟩ : Region).Disjoint ⟨W, 2560⟩

/-- With bytes left: they are encrypted with the keystream at `K[1]` and
copied to `G[0]`, and the tag of `GHASH` continued over `G[0]` and the
lengths block is at `W`. -/
theorem finTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : FinPre Ctx W SP H al n r D s) :
    WP isa (.seq (.block finTextArgs) (.seq (xorText true) (.block (finLens ++ finGh2 ++ tagK 0)))) s fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨W, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D, r⟩] s.mem t.mem ∧
      bytesAt t.mem D r = xb s.mem D (W + BitVec.ofNat 64 1040) r ∧
      blockAt t.mem W = Spec.Gcm.ghashFrom H (blockAt s.mem (yA W))
          [Spec.Gcm.ofBytes (xb s.mem D (W + BitVec.ofNat 64 1040) r ++ Spec.Gcm.zeros (16 - r)),
            Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n)] ^^^
        blockAt s.mem (W + BitVec.ofNat 64 1024) := by
  have he := P.env
  have hr := P.r16
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨D, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => P.dW.sub_right (Lay.wSub h)
  have dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h _ _ => Offset.disjoint W h (by omega) (by omega)
  -- `G[0]` zeroed, and the arguments.
  obtain ⟨s₁, run₁, m₁, di₁, si₁, dx₁, cx₁, g₁, rd₁, wr₁, x₁⟩ := finTextArgs_ok s he P.dat P.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have xp : XorPre true s₁ D (W + BitVec.ofNat 64 1040) (W + BitVec.ofNat 64 512) r :=
    ⟨si₁, dx₁, di₁, cx₁, by omega, by rw [rd₁, wr₁]; exact P.rd,
      by rw [rd₁, wr₁]; exact covers_left (he.perm.wC (by omega)), by rw [wr₁]; exact P.wr,
      fun _ => by rw [wr₁]; exact he.perm.wC (by omega), dW (by omega), fun _ => dW (by omega),
      fun _ => dWW (.inr (by omega)) (by omega) (by omega)⟩
  -- The text.
  refine WP.seq (WP.mono (xorText_ok true s₁ xp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)) rd₁ wr₁
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)) rd₂ wr₂
  have x₂ : ∀ q, q ≠ .xmm4 → q ≠ .xmm7 → s₂.xmm q = s.xmm q := fun q a b => by
    rw [show s₂.xmm q = s₂.zlane q 0 from rfl, z₂ q (by simp [a]) 0 (by decide)]
    exact x₁ q b
  generalize hc : xb s₁.mem D (W + BitVec.ofNat 64 1040) r = c at m₂
  have hcl : c.length = r := by rw [← hc, length_xb]
  have f₁ : Frame [⟨W + BitVec.ofNat 64 512, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame' _ (List.length_replicate ..)
  have f₂ : Frame [⟨D, r⟩, ⟨W + BitVec.ofNat 64 512, r⟩] s₁.mem s₂.mem := by
    rw [m₂]; have := xw_frame true s₁.mem D (W + BitVec.ofNat 64 512) c; rwa [hcl] at this
  have F₂ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D, r⟩] s.mem s₂.mem := by
    refine (f₁.sub fun q hq => ?_).trans (f₂.sub fun q hq => ?_)
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨⟨D, r⟩, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩
  have kW : ∀ q ∈ [(⟨W + BitVec.ofNat 64 512, 32⟩ : Region), ⟨D, r⟩], ∀ {d k : Nat}, d + k ≤ 512 ∨ (1024 ≤ d ∧ d + k ≤ 2560) →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := by
    intro q hq d k h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact dWW (by omega) (by omega) (by decide)
    · exact (dW (by omega)).symm
  have rW₂ : ∀ d, d + 8 ≤ 512 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => F₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun q hq => kW q hq (.inl h)) (by decide)
  -- The lengths block.
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s₂ he₂ (by rw [rW₂ 184 (by decide)]; exact P.alen)
    (by rw [rW₂ 192 (by decide)]; exact P.tlen)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  have x₃' : ∀ q, q ≠ .xmm4 → q ≠ .xmm7 → s₃.xmm q = s.xmm q := fun q a b => by rw [x₃, x₂ q a b]
  have F₃ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D, r⟩] s.mem s₃.mem :=
    F₂.trans (f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩)
  -- `GHASH`.
  rw [WP.block_append_iff]
  refine WP.mono (finGh2_ok s₃ he₃ (H := H) (by rw [x₃' _ (by decide) (by decide)]; exact P.x0)
    (by rw [x₃' _ (by decide) (by decide)]; exact P.x1)
    (by rw [x₃' .xmm3 (by decide) (by decide), x₃' .xmm6 (by decide) (by decide)]; exact P.h2)) fun s₄ ⟨y₄, o₄⟩ => ?_
  -- The tag.
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 0) s₄ ((o₄.gpr _ (by decide)).trans he₃.r15)
    (by rw [o₄.wr]; exact he₃.perm.w) (by decide) (by rw [o₄.xmm _ (by decide), x₃' _ (by decide) (by decide)]; exact P.x0)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have m₄ := o₄.mem
  have bD : bytesAt s₃.mem D r = c := by
    rw [bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dW (by decide)) (by omega), m₂]
    simp only [xw, ↓reduceIte]
    rw [bytesAt_frame (writeBytes_frame' _ hcl) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dW (by omega)) (by omega), ← hcl]
    exact bytesAt_writeBytes_self _ _ _ (by omega)
  have hc' : c = xb s.mem D (W + BitVec.ofNat 64 1040) r := by
    rw [← hc]; simp only [xb]
    rw [bytesAt_frame f₁ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dW (by decide)) (by omega),
      bytesAt_frame f₁ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dWW (.inr (by omega)) (by omega) (by decide)) (by omega)]
  -- `G[0]`: the ciphertext and zeros.
  have z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) = Spec.Gcm.zeros (16 - r) := by
    have e := bytesAt_add s₁.mem (W + BitVec.ofNat 64 512) r (16 - r)
    have e16 : bytesAt s₁.mem (W + BitVec.ofNat 64 512) 16 = List.replicate 16 0 := by
      rw [m₁]; exact bytesAt_writeBytes_self _ _ _ (by decide)
    rw [Nat.add_sub_cancel' (by omega), e16, show List.replicate 16 (0 : Byte) = List.replicate r 0 ++
      List.replicate (16 - r) 0 by rw [List.replicate_append_replicate, Nat.add_sub_cancel' (by omega)]] at e
    exact ((List.append_inj e (by rw [List.length_replicate, length_bytesAt])).2).symm
  have hG0 : bytesAt s₃.mem (W + BitVec.ofNat 64 512) 16 = c ++ Spec.Gcm.zeros (16 - r) := by
    rw [bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dWW (.inl (by decide)) (by decide) (by decide))
      (by decide), ← Nat.add_sub_cancel' (show r ≤ 16 by omega), bytesAt_add, Nat.add_sub_cancel' (by omega), m₂]
    simp only [xw, ↓reduceIte]
    have a₁ : bytesAt (writeBytes (writeBytes s₁.mem D c) (W + BitVec.ofNat 64 512) c) (W + BitVec.ofNat 64 512) r = c := by
      rw [← hcl]; exact bytesAt_writeBytes_self _ _ _ (by omega)
    have a₂ : bytesAt (writeBytes (writeBytes s₁.mem D c) (W + BitVec.ofNat 64 512) c)
        (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) =
        bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) := by
      rw [bytesAt_frame (writeBytes_frame' _ hcl) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact Offset.disjoint_base (W + BitVec.ofNat 64 512) (Nat.le_refl r) (by omega)) (by omega),
        bytesAt_frame (writeBytes_frame' _ hcl) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          rw [add_ofNat_ofNat]; exact (dW (by omega)).symm) (by omega)]
    rw [a₁, a₂, z₁]
  have bW : ∀ {d : Nat}, d + 16 ≤ 512 ∨ (1024 ≤ d ∧ d + 16 ≤ 2560) →
      blockAt s₃.mem (W + BitVec.ofNat 64 d) = blockAt s.mem (W + BitVec.ofNat 64 d) :=
    fun h => blockAt_frame F₃ fun q hq => kW q hq h
  have hY : blockAt s₃.mem (yA W) = blockAt s.mem (yA W) := by
    simp only [yA, add_ofNat_ofNat]; exact bW (.inl (by decide))
  have hb₀ : blockAt s₃.mem (W + BitVec.ofNat 64 512) = Spec.Gcm.ofBytes (c ++ Spec.Gcm.zeros (16 - r)) := by
    rw [Spec.Gcm.blockAt, hG0]
  have hb₁ : blockAt s₃.mem (W + BitVec.ofNat 64 528) = Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n) := by
    rw [Spec.Gcm.blockAt, hL₃]
  have t₅ : blockAt s₅.mem W = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) := by simpa using tag₅
  refine ⟨he₃.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, o₄.wr, wr₃, wr₂, wr₁], ?_, ?_, ?_⟩
  · refine (F₃.sub fun q hq => ⟨q, List.mem_cons_of_mem _ hq, fun _ h => h⟩).trans ?_
    rw [← m₄]
    exact fW.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W, 16⟩, List.mem_cons_self .., by simpa using Region.sub_prefix (base := W) (Nat.le_refl 16)⟩
  · rw [bytesAt_frame fW (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simpa using dW (d := 0) (k := 16) (by decide)) (by omega),
      m₄, bD, hc']
  · rw [t₅, y₄, m₄, hY, bW (.inr ⟨Nat.le_refl _, by decide⟩), hb₀, hb₁, hc']

/-- Without bytes left: the tag of `GHASH` continued over the lengths block is
at `W`. -/
theorem finNoTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : FinPre Ctx W SP H al n r D s) :
    WP isa (.block (finLens ++ finGh1 ++ tagK 0)) s fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨W, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D, r⟩] s.mem t.mem ∧
      blockAt t.mem W = Spec.Gcm.ghashFrom H (blockAt s.mem (yA W)) [Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n)] ^^^
        blockAt s.mem (W + BitVec.ofNat 64 1024) := by
  have he := P.env
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s he P.alen P.tlen
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  rw [WP.block_append_iff]
  refine WP.mono (finGh1_ok s₃ he₃ (H := H) (by rw [x₃]; exact P.x0) (by rw [x₃]; exact P.x1)
    (by rw [x₃]; exact P.h1)) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 0) s₄ ((o₄.gpr _ (by decide)).trans he₃.r15)
    (by rw [o₄.wr]; exact he₃.perm.w) (by decide) (by rw [o₄.xmm _ (by decide), x₃]; exact P.x0)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have m₄ := o₄.mem
  have bW : ∀ {d : Nat}, d + 16 ≤ 528 ∨ 544 ≤ d → d + 16 ≤ 2560 →
      blockAt s₃.mem (W + BitVec.ofNat 64 d) = blockAt s.mem (W + BitVec.ofNat 64 d) :=
    fun h h' => blockAt_frame f₃ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (by omega) (by omega) (by decide)
  have hY : blockAt s₃.mem (yA W) = blockAt s.mem (yA W) := by
    simp only [yA, add_ofNat_ofNat]; exact bW (.inl (by decide)) (by decide)
  have hb₁ : blockAt s₃.mem (W + BitVec.ofNat 64 528) = Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n) := by
    rw [Spec.Gcm.blockAt, hL₃]
  have t₅ : blockAt s₅.mem W = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) := by simpa using tag₅
  refine ⟨he₃.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd, rd₃], by rw [wr₅, o₄.wr, wr₃], ?_, ?_⟩
  · refine (f₃.sub fun q hq => ?_).trans ?_
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    rw [← m₄]
    exact fW.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W, 16⟩, List.mem_cons_self .., by simpa using Region.sub_prefix (base := W) (Nat.le_refl 16)⟩
  · rw [t₅, y₄, m₄, hY, hb₁, bW (d := 1024) (.inr (by decide)) (by decide)]

/-! ## `oneBlocks` and `finish` -/

open VG.Spec.Gcm (ghashFrom zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- The bytes left encrypted with the keystream block of the counter after
the whole blocks. -/
theorem tail_xorKs {m m' : Mem} {cb ks S : Addr} {ciph : Block → Block} {icb : Block} {q r : Nat} (hr : r ≤ 16)
    (hcb : blockAt m cb = Nat.repeat inc32 q icb) (hk : blockAt m' ks = ciph (blockAt m cb)) :
    xb m' S ks r = xorKs ciph icb (16 * q) (bytesAt m' S r) := by
  rw [xb]
  refine Proof.Gcm.zipWith_eq_xorKs (by rw [length_bytesAt, length_bytesAt]) fun k hk' => ?_
  rw [length_bytesAt] at hk'
  rw [Proof.Gcm.getD_bytesAt' _ _ hk', Proof.Gcm.bytes_toBytes_blockAt m' ks (k := k) (by omega), hk, hcb,
    Proof.Gcm.ksByte, show (16 * q + k) / 16 = q by omega, show (16 * q + k) % 16 = k by omega]

/-- `GHASH` of whole blocks, then of one more, is `ghashFrom` over it. -/
theorem ghash_snoc (H : Block) (xs : List Block) (g : Block) :
    Spec.Gcm.ghash H (xs ++ [g]) = ghashFrom H (Spec.Gcm.ghash H xs) [g] := Proof.Gcm.ghashFrom_append H 0 xs [g]

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
  {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
include L

/-- The body of `seal` with `finishWith ks`: what `sealBody_ok` leaves. -/
theorem sealBodyF_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) {R : Nat} {D : Addr} {n al : Nat} {H icb : Block} {a : List Byte} {s : State}
    (h : ObPre M Ctx W SP R D n s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hcb : blockAt s.mem (cbA W) = icb) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))) :
    WP isa (.seq (oneBlocks B.enc) (finishWith ks)) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (oneFrameB W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (Spec.Gcm.ghash H (Spec.Gcm.blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hR := h.rounds.2
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (oneBlocksE_ok L B h) fun s₃ ⟨P, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h P hH hcb habs hxa o₁ o₂
    (Z := bytesAt s₃.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega)
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  generalize hq : n / 16 = q at *
  have Plen := P.len
  generalize hr : n % 16 = r at Plen
  have hnr : n = 16 * q + r := by omega
  have hr16 : r < 16 := by omega
  rw [show n - 16 * q = r by omega] at ht₃
  have he₃ := P.env
  have kW₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L hD h.t_w hd) (by decide)
  -- `H'` and `H'²`.
  simp only [finishWith]
  refine WP.seq (WP.mono (hF.finPow s₃ (by rw [he₃.r13, BitVec.ofInt_natCast]; exact he₃.perm.ctxR (by decide)))
    fun s₄ ⟨x0, x1, h1, h2, o₄⟩ => ?_)
  rw [he₃.r13, BitVec.ofInt_natCast, hH₃] at h1 h2
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun g hg => o₄.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₄.rd o₄.wr
  -- The keystream.
  refine WP.seq (WP.mono (hks s₄ he₄ (by rw [o₄.mem]; exact hR₃.1) hR) fun s₅ ⟨k₀, k₁, fK, g₅, rd₅, wr₅, x₅⟩ => ?_)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide)) rd₅ wr₅
  rw [o₄.mem] at k₀ k₁ fK
  have rK : ∀ d, d + 8 ≤ 1024 → s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => fK.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide))
      (by decide)
  -- The test.
  refine WP.seq (WP.mono (finTest_ok (r := r) (by omega) s₅ he₅ (by rw [rK 208 (by decide)]; exact Plen))
    fun s₆ ⟨z₆, g₆, m₆, rd₆, wr₆, x₆⟩ => ?_)
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₅.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) rd₆ wr₆
  have xx : ∀ q, q ≠ .xmm5 → q ≠ .xmm7 → q ≠ .xmm8 → q ≠ .xmm13 → s₆.xmm q = s₄.xmm q := fun q a b c d => by
    rw [x₆, x₅ q a b c d]
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W SP s (D + BitVec.ofNat 64 (16 * q)) r := by
    have := h.data.drop (k := 16 * q) (by omega); rwa [show n - 16 * q = r by omega] at this
  have FP : FinPre Ctx W SP H al n r (D + BitVec.ofNat 64 (16 * q)) s₆ :=
    { env := he₆
      x0 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x0
      x1 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x1
      h1 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact h1
      h2 := by rw [xx .xmm3 (by decide) (by decide) (by decide) (by decide), xx .xmm6 (by decide) (by decide) (by decide) (by decide)]; exact h2
      alen := by rw [m₆, rK 184 (by decide), kW₃ 184 (.inl ⟨by decide, by decide⟩)]; exact hal
      tlen := by rw [m₆, rK 192 (by decide)]; exact P.tlen
      dat := by rw [m₆, rK 200 (by decide)]; rw [← hq]; exact P.dat
      len := by rw [m₆, rK 208 (by decide)]; exact Plen
      r16 := hr16
      rd := by rw [rd₆, wr₆, rd₅, wr₅, o₄.rd, o₄.wr, P.rd, P.wr]; exact hdw.ok.rd
      wr := by rw [wr₆, wr₅, o₄.wr, P.wr]; exact hdw.wr
      dW := hdw.ok.w }
  -- What both ends share.
  have m₆₃ : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩] s₃.mem s₆.mem := by rw [m₆]; exact fK
  have hXZ : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q)).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega
  have hY : blockAt s₆.mem (yA W) =
      Spec.Gcm.ghash H (Spec.Gcm.blocks (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q))) := by
    rw [blockAt_frame m₆₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simp only [yA, add_ofNat_ofNat]
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)), ab₃.1, Proof.Gcm.whole_of_mod hXZ,
      List.take_length]
  have hK₀ : blockAt s₆.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
    rw [m₆, k₀, hc₃, hJ₃]
  have hcb₃ : blockAt s₃.mem (cbA W) = Nat.repeat inc32 q icb := by rw [ct₃.1]; congr 1; omega
  have hK₁ : blockAt s₆.mem (W + BitVec.ofNat 64 1040) = ciphOf s.mem Ctx R (blockAt s₃.mem (cbA W)) := by
    rw [m₆, show W + BitVec.ofNat 64 1040 = W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 by rw [add_ofNat_ofNat], k₁,
      hc₃]
  have dDW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ {e j : Nat}, e + j ≤ n →
      (⟨D + BitVec.ofNat 64 e, j⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ _ _ h₂ => (hD.sub_left (Offset.sub_base D h₂)).sub_right (Lay.wSub h₁)
  have split : ∀ m : Mem, bytesAt m D n = bytesAt m D (16 * q) ++ bytesAt m (D + BitVec.ofNat 64 (16 * q)) r :=
    fun m => by rw [hnr, ← bytesAt_add]
  have hpre : ∀ m : Mem, Frame [⟨W, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D + BitVec.ofNat 64 (16 * q), r⟩] s₆.mem m →
      bytesAt m D (16 * q) = bytesAt s₃.mem D (16 * q) := fun m f => by
    rw [bytesAt_frame f (fun q' hq' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl | rfl
        · simpa using dDW (d := 0) (k := 16) (e := 0) (j := 16 * q) (by decide) (by omega)
        · simpa using dDW (d := 512) (k := 32) (e := 0) (j := 16 * q) (by decide) (by omega)
        · simpa using Offset.disjoint D (d := 0) (n := 16 * q) (e := 16 * q) (k := r) (.inl (by omega)) (by omega)
            (by omega)) (by omega),
      bytesAt_frame m₆₃ (fun q' hq' => by
        simp only [List.mem_singleton] at hq'; subst hq'
        simpa using dDW (d := 1024) (k := 64) (e := 0) (j := 16 * q) (by decide) (by omega)) (by omega)]
  have hFr : ∀ m : Mem, Frame [⟨W, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩, ⟨D + BitVec.ofNat 64 (16 * q), r⟩] s₆.mem m →
      Frame (oneFrameB W D SP n) s.mem m := fun m f =>
    oneB_trans f₃ (oneB_trans (m₆₃.sub fun q' hq' => by
        simp only [List.mem_singleton] at hq'; subst hq'
        exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩)
      (f.sub fun q' hq' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl | rfl
        · exact ⟨⟨W, 128⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩))
  have hrw : ∀ t : State, t.rd = s₆.rd → t.wr = s₆.wr → t.rd = s.rd ∧ t.wr = s.wr := fun t a b =>
    ⟨by rw [a, rd₆, rd₅, o₄.rd, P.rd], by rw [b, wr₆, wr₅, o₄.wr, P.wr]⟩
  have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
  refine WP.ite (decide (r = 0)) (eval_e z₆) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    have h0' : r = 0 := of_decide_eq_true h0
    subst h0'
    refine WP.mono (finNoTail_ok FP) fun t ⟨het, rdt, wrt, ft, tagt⟩ => ?_
    have hct : bytesAt t.mem D n = bytesAt s₃.mem D (16 * q) := by rw [split, hpre _ ft, b0, List.append_nil]
    refine ⟨het, (hrw t rdt wrt).1, (hrw t rdt wrt).2, hFr _ ft, ?_, ?_⟩
    · rw [hct, hw₃, split s.mem, b0, List.append_nil]
    · rw [bytesAt_toBytes', tagt, hY, hK₀, hct, ← padded_eq, Proof.Gcm.padLen_of_mod hXZ,
        show zeros 0 = [] from rfl, List.append_nil]
  · -- Bytes left.
    have h0' : r ≠ 0 := of_decide_eq_false h0
    refine WP.mono (finTail_ok FP) fun t ⟨het, rdt, wrt, ft, bDt, tagt⟩ => ?_
    have hT : xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r =
        xorKs (ciphOf s.mem Ctx R) icb (16 * q) (bytesAt s.mem (D + BitVec.ofNat 64 (16 * q)) r) := by
      rw [tail_xorKs (by omega) hcb₃ hK₁, bytesAt_frame m₆₃ (fun q' hq' => by
          simp only [List.mem_singleton] at hq'; subst hq'; exact dDW (by decide) (by omega)) (by omega), ht₃]
    have hct : bytesAt t.mem D n =
        bytesAt s₃.mem D (16 * q) ++ xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r := by
      rw [split, hpre _ ft, bDt]
    refine ⟨het, (hrw t rdt wrt).1, (hrw t rdt wrt).2, hFr _ ft, ?_, ?_⟩
    · rw [hct, hw₃, hT, split s.mem, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add]
    · have hpl : padLen (a ++ zeros (padLen a.length) ++ (bytesAt s₃.mem D (16 * q) ++
          xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r)).length = 16 - r := by
        have := hxa
        simp only [padLen, List.length_append, length_bytesAt, length_xb, Proof.Gcm.length_zeros] at this ⊢
        omega
      have e : a ++ zeros (padLen a.length) ++ (bytesAt s₃.mem D (16 * q) ++
          xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r) ++ zeros (16 - r) =
          a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q) ++
            (xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r ++ zeros (16 - r)) := by
        simp only [List.append_assoc]
      have bs := Proof.Gcm.blocks_single (bs := xb s₆.mem (D + BitVec.ofNat 64 (16 * q)) (W + BitVec.ofNat 64 1040) r ++
        zeros (16 - r)) (by rw [List.length_append, length_xb, Proof.Gcm.length_zeros]; omega)
      rw [bytesAt_toBytes', tagt, hY, hK₀, hct, ← padded_eq, hpl, e, Proof.Gcm.blocks_append hXZ, bs, ghash_snoc,
        ← Proof.Gcm.ghashFrom_append]
      rfl

end

end VG.Proof.AesGcm.X86_64.Short
