module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Aes
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# The out-of-place VAES loop: the loop of one group, and the stores

As `Stitch/Loop.lean` and `Stitch/Enc.lean` do in place. The setup is
`StitchZTo.setupTTo_ok`'s (`Ready2To`), from which the loop starts
(`ReadyTo.ofReady2`).

`EInvTo s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInvTo`),
the ciphertext of the first `e - 1` hashed into `Y`; `rdx` points to output
group `e - 1`, the next to hash. The loop is the in-place one, out of place,
and so are its proofs: `bodyTo_ok`, `firstTo_ok`, `finalTo_ok` and
`encTailTo_ok` are `Stitch.bodyM_ok` and its neighbours for the output at
`r10` (`EInvTo.toM`, `EPostM.toEPostTo`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  GEnv QG gRegs gRegs_ok gq_ok QG.data nextE_ok FinOk ghRun_ok ghFin store16_ok)
open VG.Proof.Gcm.X86_64.StitchZTo (dst sAddr pblk ctbT oAddr Ready2To blocks_ctr32To)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs gA gB ordE storeCtr lastG storeY)
open VG.Impl.Gcm.X86_64.StitchTo (firstTo bodyTo)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## The state the loop starts from -/

structure ReadyTo (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvTo s₀ 0 s
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem ReadyTo.ofReady2 {s₀ : State} {P : Nat → Nat → Block} {s : State} (h : Ready2To s₀ P s) :
    ReadyTo s₀ P s :=
  ⟨⟨Nat.zero_le _, fun l hl => by rw [h.ctr l hl, Nat.zero_add], h.msk, h.inc, h.rdi, h.rsi, h.r10, h.r8,
    h.frame.mono fun r hr => by simp at hr ⊢; exact Or.inr hr, fun k hk => absurd hk (Nat.not_lt_zero _),
    h.rd, h.wr⟩, h.rdx, h.rax, h.gpr, h.pw, h.m1, h.y, h.y1⟩

/-! ## The loop of one group -/

structure EInvTo (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvTo s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : s.lane .xmm2 1 = 0

/-! ## As the in-place loop's, out of place -/

theorem EInvTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {e : Nat} {s : State}
    (h : EInvTo s₀ P e s) : Stitch.EInvM true s₀ P e s :=
  ⟨h.a.toM hp, h.one, h.rdx, h.r9, h.rax, fun _ => h.a.r8, fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (h3 rfl) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

theorem _root_.VG.Proof.Gcm.X86_64.Stitch.EInvM.toTo {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State}
    (h : Stitch.EInvM true s₀ P e s) : EInvTo s₀ P e s :=
  ⟨h.a.toTo rfl (h.r8 rfl), h.one, h.rdx, h.r9, h.rax, fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (fun _ => h3) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

theorem ReadyTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (h : ReadyTo s₀ P s) : Stitch.ReadyM true s₀ P s :=
  ⟨h.a.toM hp, h.rdx, fun _ => h.a.r8, h.rax, fun r h1 h2 h3 h4 => h.gpr r h1 h2 (h3 rfl) h4, h.pw, h.m1, h.y, h.y1⟩

theorem _root_.VG.Proof.Gcm.X86_64.Stitch.EPostM.toEPostTo {s₀ s : State} (h : Stitch.EPostM true s₀ s) :
    EPostTo s₀ s :=
  ⟨blocks_ctr32To h.data, h.ctr, by rw [h.y]; exact congrArg _ h.blocks.symm, h.frame,
    fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (fun _ => h3) h4 h5, h.rd, h.wr⟩

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) :=
  WP.mono (Stitch.bodyM_ok hp.toM hf he (hI.toM hp)) fun _ ⟨h, hc⟩ => ⟨h.toTo, hc⟩

theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s) : WP isa firstTo s (EInvTo s₀ P 1) :=
  WP.mono (Stitch.firstM_ok hp.toM hp.nb16 (hR.toM hp)) fun _ h => h.toTo

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInvTo s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

theorem loopE_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInvTo s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s' :=
  WP.mono (Stitch.loopEM_from_ok hm hp.toM hf (hI.toM hp) hcf) fun _ ⟨e, he, h⟩ => ⟨e, he, h.toTo⟩

theorem finalTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPostTo s₀) :=
  WP.mono (Stitch.finalM_ok hp.toM hf he (hI.toM hp)) fun _ h => h.toEPostTo

theorem encTailTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s
      (EPostTo s₀) :=
  WP.mono (Stitch.encTailM_ok hp.toM hp.nb16 hm hf (hR.toM hp)) fun _ h => h.toEPostTo

end VG.Proof.Gcm.X86_64.StitchTo
