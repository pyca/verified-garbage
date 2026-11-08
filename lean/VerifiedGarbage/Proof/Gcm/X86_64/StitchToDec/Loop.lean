module

-- separate module: the loop's proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchToDec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecToDec
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt

/-!
# The out-of-place VAES decryption loop

Untrusted: everything here is checked by Lean. The loop is the in-place one,
`Stitch.dbody`, out of place, and so is its proof (`Stitch.decTailM_ok`):
`rdx` points at the ciphertext, which both the GHASH loads and the XOR read
and nothing writes, and `r8` holds `dst - src`.

`setupCToDec_ok`: the end of the setup loads `Y` and makes the counter pair
and the increment as `Stitch.setupC`, and leaves `src` in `rdx` and
`dst - src` in `r8`; with the powers stored before it, the state the loop
starts from (`setupTToDec_ok`, `ReadyToDec`), from which
`Stitch.decTailM_ok` decrypts (`decTailToDec_ok`), its result the contract
(`DPostM.toDPostTo`).

`decToR_okN`: the whole loop, for a prepared key context, given that the
powers it loads give the products of a decryption body (`PowFinD`), which
`Stitch.finD` proves where the field is imported (`AesGcm/X86_64/Instances.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchToDec

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo DPostTo CtxMode AInvM DInvM DPostM LPre sp op nb pp cp yp hk y₀ dp pR
  in_rdwr in_sub_int storesK_ok pregs_get blockAt_outP FinOk)
open VG.Proof.Gcm.X86_64.StitchZTo (blocks_ctr32To)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (dbody ordD storeCtr storeY storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchToDec (setupCToDec)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Spec.Gcm (Block blockAt ghashFrom inc32)

/-! ## The setup -/

theorem setupCToDec_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupCToDec) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .r10 - s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupCToDec, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, trivial, fun r h1 h2 h3 h4 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3, h4]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

/-- The state the loop starts from. -/
structure ReadyToDec (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvM true s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  r8 : s.gpr .r8 = op s₀ - dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

/-- The setup after the powers: they are stored in the working space, then
`Y`, the counter, the increment and the pointers. -/
theorem setupTToDec_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {s₁ : State}
    (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask) (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly)
    (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupCToDec)) s₁ (ReadyToDec s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega_arith))
    (by rw [hr11]; simp [pregs]; omega_arith)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  refine WP.mono (setupCToDec_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, r8, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, fun l hl => by rw [c15 l hl],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [r10, gs _ (by decide), gs _ (by decide)],
    by rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr,
    fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk _ => by
      have := hp.wrap_s
      rw [m₃, hp₂ (hp.s_p.sub_left (Offset.sub_base _ (by omega_arith)))],
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩,
    by rw [rdx, gs _ (by decide)], by rw [r8, gs _ (by decide), gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [gk r h1 h2 h3 h4, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm, Nat.zero_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

/-! ## The loop -/

theorem _root_.VG.Proof.Gcm.X86_64.Stitch.DPostM.toDPostTo {s₀ s : State} (h : DPostM true s₀ s) : DPostTo s₀ s :=
  ⟨blocks_ctr32To h.data, h.ctr, h.y, h.frame, fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (fun _ => h3) h4 h5, h.rd, h.wr⟩

/-- The decryption after the setup. -/
theorem decTailToDec_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordD (hk s₀) P) {s₁ : State} (hR : ReadyToDec s₀ P s₁) :
    WP isa (.seq (.loop (dbody true) .ae) (.block (storeCtr ++ storeY))) s₁ (DPostTo s₀) :=
  WP.mono (Stitch.decTailM_ok hp.toM hp.nb16 hm hf
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun _ => hR.r8,
      fun r h1 h2 h3 _ h5 => hR.gpr r h1 h2 (h3 rfl) h5, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩)
    fun _ h => h.toDPostTo

/-! ## The whole loop -/

/-- The prepared powers `H'¹⁶⁻²ᵏ⁻ˡ` the setup loads give the products of a
decryption body. -/
def PowFinD : Prop :=
  ∀ H : Block, FinOk ordD H fun k l => StitchZP.hInvF (Spec.Gcm.hpow H (16 - 2 * k - l))

/-- The setup: the state the loop starts from, with the prepared powers. -/
theorem setupToDec_ok {s₀ : State} {np : Nat} {hn : 8 ≤ np ∧ np ≤ 24} (hp : SPreTo (CtxMode.preparedN np hn) s₀)
    (h8 : 8 ≤ np) :
    WP isa (.block Impl.Gcm.X86_64.StitchToDec.setup) s₀
      (ReadyToDec s₀ fun k l => StitchZP.hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) := by
  rw [Impl.Gcm.X86_64.StitchToDec.setup, Impl.Gcm.X86_64.StitchToDec.setupWith, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (StitchZRTo.setupGPTo_ok hp h8) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (setupTToDec_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun s hR => ?_
  exact { hR with pw := fun k hk l hl => by rw [hR.pw k hk l hl, pw k hk l hl] }

/-- The out-of-place decryption loop, for a prepared key context, for any
number of blocks from 16 on that is a multiple of 16. -/
theorem decToR_okN (hf : PowFinD) (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) (h8 : 8 ≤ np := by decide) :
    Stitch.StitchToDecOkM (CtxMode.preparedN np hn) Impl.Gcm.X86_64.StitchToDec.decToR := fun _ hp hm =>
  WP.seq (WP.mono (setupToDec_ok hp h8) fun _ hR => decTailToDec_ok hp hm (hf _) hR)

end VG.Proof.Gcm.X86_64.StitchToDec
