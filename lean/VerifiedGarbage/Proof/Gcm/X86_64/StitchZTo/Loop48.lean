module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The out-of-place AVX-512 loop: 48 blocks at a time

As `StitchZ/Loop48.lean` does in place, and by its proofs: `bigRestTo_ok`,
`bigTo_ok` and `encTailGTo_ok` are `StitchZ.bigRestM_ok`, `bigM_ok` and
`encTailGM_ok` for the output at `r10`. `encTailGTo_ok` is the loop after
the setup, for any code `bigC` of 256 blocks on that ends in `EInvTo`
(`bigTo_ok`, and `bigPTo_ok` in `StitchZTo/LoopP.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv GEnv48 QG48 gRegs48 gRegs48_ok gq48_ok QG48.data QG48.next keepW T48
  FinOk FinOk48 ghRun_ok ghFin adv_ok next48_ok cmp_ok reload_ok ghash_append48 pw16 pow48_ok)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (gq48 pow48 lastG adv tab)
open VG.Impl.Gcm.X86_64.StitchZTo (batchTo bodyTo body48To bigRestTo bigTo firstTo)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## As the in-place loops', out of place -/

/-- The encryption state kept by writes to the working space alone. -/
theorem AInvTo.pow {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s s' : State} (h : AInvTo s₀ c s)
    (hf : Frame [pR s₀] s.mem s'.mem) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hl : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
      s'.zlane r l = s.zlane r l) : AInvTo s₀ c s' := by
  have hw := hp.wrap_o
  have k : ∀ r ∈ ([.xmm14, .xmm0, .xmm15] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l := by
    intro r hr l hl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hl _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl'
  refine ⟨h.le, fun l hl' => by rw [k _ (by decide) l hl']; exact h.ctr l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.msk l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.inc l hl',
    by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.r10, by rw [hg]; exact h.r8,
    h.frame.trans (hf.sub fun r hr => ⟨pR s₀, by simp, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr; exact ha⟩),
    fun k hk => ?_, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩
  rw [blockAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o_p.sub_left (Offset.sub_base _ (by have := h.le; omega_arith))]
  exact h.blocks k hk

theorem EInvTo.of_eq {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s s' : State} (h : EInvTo s₀ P e s)
    (hg : s'.gpr = s.gpr) (hl : ∀ r l, s'.zlane r l = s.zlane r l) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : EInvTo s₀ P e s' :=
  ⟨h.a.gpr2 (fun r _ _ => by rw [hg]) hl hm hrd hwr, h.one, by rw [hg]; exact h.rdx, by rw [hg]; exact h.r9,
    by rw [hg]; exact h.rax, fun r h1 h2 h3 h4 h5 => by rw [hg]; exact h.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl' => by rw [hm]; exact h.pw k hk l hl', fun l hl' => by rw [hl]; exact h.m1 l hl',
    by rw [hl]; exact h.y, fun l h1 h4 => by rw [hl]; exact h.y1 l h1 h4⟩

/-- What `bigTo` does after the tables: the next two groups, the loop, and
two of the three groups left to hash, for any tables `T` whose last is `P`. -/
theorem bigRestTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h96 : 96 ≤ nb s₀) {s s₁ : State} (hI : EInvTo s₀ P 1 s) (hA₁ : AInvTo s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l) :
    WP isa bigRestTo s₁ fun s' => ∃ e, EInvTo s₀ P e s' :=
  WP.mono (StitchZ.bigRestM_ok hp.toM hf hT hT2 h96 (hI.toM hp) (hA₁.toM hp) hv₁ hm₁ hg₁ hl₁)
    fun _ ⟨e, h⟩ => ⟨e, h.toTo⟩

/-- `bigTo`: from the first group encrypted to all but up to two groups, all
but the last encrypted group hashed. -/
theorem bigTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hT : FinOk48 (hk s₀) (T48 P)) (h96 : 96 ≤ nb s₀) {s : State} (hI : EInvTo s₀ P 1 s) :
    WP isa bigTo s fun s' => ∃ e, EInvTo s₀ P e s' :=
  WP.mono (StitchZ.bigM_ok hp.toM hf hT h96 (hI.toM hp)) fun _ ⟨e, h⟩ => ⟨e, h.toTo⟩

/-- The encryption after the setup, for any code `bigC` from `t` blocks on. -/
theorem encTailGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk (hk s₀) P) {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → EInvTo s₀ P 1 s → WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s')
    {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm i)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (.block (storeCtr ++ lastG ++ storeY))))))) s (EPostTo s₀) :=
  WP.mono (StitchZ.encTailGM_ok hp.toM hp.nb16 hm hf t hi ht
    (fun s h hI => WP.mono (hbig s h hI.toTo) fun _ ⟨e, h⟩ => ⟨e, h.toM hp⟩) (hR.toM hp)) fun _ h => h.toEPostTo

end VG.Proof.Gcm.X86_64.StitchZTo
