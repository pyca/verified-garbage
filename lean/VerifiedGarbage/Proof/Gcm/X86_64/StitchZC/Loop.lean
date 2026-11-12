module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZC
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
public import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pair
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-!
# GCM encryption hashing each group from registers

`bigRestCM_ok`: `StitchZC.bigRestC`, from one group encrypted and not yet
hashed (`StitchZ.EInvM`) to one such (as `StitchZH.bigRestM_ok`). Between
`enter` and `leave` the invariant is `CInv`: `EInvM` with the last group in
the copies, the powers of 48 blocks and the reduction constant in the
working space, and the increment there too.

* `pairC_ok`: `pairC ka g first` adds, in each lane, the products of copies
  `ka` and `ka + 1` (`creg`) with their powers (at `scratch + tab g + 64 k`)
  to the lane's (`StitchZ.pair_ok`, for blocks in registers and one register
  of powers): `halfA` and `halfB`, each the SSE code of its lanes
  (`WP.zlanes`), after each load of the powers.
* `gqC_ok`: the GHASH work between the rounds of a group (`gqC`), on the
  copies of the group before, group `g` of three: its two pairs add the
  products of its sixteen blocks to those of the groups before it
  (`StitchZ.acc48`, of 48 blocks `X`, the group's being `X (16 g) …`), the
  first pair of the first group with `Y`, and after round 9 of the last one
  the four lanes are reduced into `Y` (`StitchZ.fin_ok`).
* `grpM_ok`: `grpC j g ld` encrypts the sixteen data blocks at
  `rdx + 64 j`, in place or from `rdx + r8 + 64 j`, as `StitchZH.batch` does
  (`Cached/Aes.lean`), with the counters' increment loaded from
  `scratch + 896` (`CA`, `StitchZ.AInvM` with the increment there), and
  leaves the blocks stored in the copies, as GHASH takes them.
* A body of `m` groups (`body48C`, `body32C`, `body16C`) hashes the group in
  the copies and the first `m - 1` it encrypts: their products are those of
  48 blocks, the first `48 - 16 m` zero (`padX`), which add nothing
  (`acc48_pad`) and leave `GHASH` as it is (`ghash_pad`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZC

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (zero_xor_b)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (ldZ ldZ_zlane ldZ_zlane_ne)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZC (creg halfA halfB pairC)
open VG.Proof.Gcm.X86_64.Stitch (pp nr sch ite_t ite_f zero_xor_b)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (acc48 acc48_succ inp48 pa yNew48 gRegs48 fin_ok ldZ ldZ_zlane ldZ_zlane_ne
  ofInt_add_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchZ (fin48 fin tab)
open VG.Impl.Gcm.X86_64.StitchZC (creg pairC gqC)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm.X86_64.Stitch (nb nr kp pp cb dp dR pR bAddr blk ctb ciph sch addr_eq in_sub in_sub_int in_rdwr)
open VG.Proof.Gcm.X86_64.Pclmul (Only ea_at)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZC (creg incAt copies grpC)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Proof.Gcm.X86_64.StitchZ (aregs_ok ldZ ldZ_zlane ldZ_zlane_ne ofInt_add_ofNat keepWM)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)
open VG.Proof.Gcm.X86_64.Stitch (nb nr kp pp cp cb dp dR pR bAddr blk ctb ciph sch hk y₀ ite_t ite_f addr_eq
  in_sub in_sub_int in_rdwr zero_xor_b)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat ea_at)
open VG.Impl.Gcm.X86_64.StitchZ (tab adv)
open VG.Impl.Gcm.X86_64.StitchZC (creg incAt gqC grpC body48C body32C body16C enter leave bigRestC)
open VG.Proof.Gcm.X86_64.StitchZ (acc48 acc48_succ inp48 pa yNew48 FinOk48 gRegs48 keepWM adv_ok next48_ok cmp_ok
  EInvM AInvM)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt ghashFrom inc32 mul)

/-! ## A pair of copies -/

/-- The SSE block of `halfA`'s lanes. -/
def halfASse (first : Bool) (a : XReg) : List Instr :=
  if first then
    [.xop (.bin .pxor a .xmm2),
     .xop (.bin .movdqa .xmm9 a), .xop (.pclmulqdq .xmm9 .xmm13 0x01),
     .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 .xmm13 0x10),
     .xop (.bin .pxor .xmm9 .xmm11),
     .xop (.bin .movdqa .xmm8 a), .xop (.pclmulqdq .xmm8 .xmm13 0x00),
     .xop (.pclmulqdq a .xmm13 0x11)]
  else
    [.xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 .xmm13 0x01),
     .xop (.bin .movdqa .xmm2 a), .xop (.pclmulqdq .xmm2 .xmm13 0x10),
     .xop (.bin .pxor .xmm9 .xmm11), .xop (.bin .pxor .xmm9 .xmm2),
     .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 .xmm13 0x00),
     .xop (.pclmulqdq a .xmm13 0x11)]

/-- The SSE block of `halfB`'s lanes. -/
def halfBSse (first : Bool) (a b : XReg) : List Instr :=
  (if first then
    [.xop (.bin .movdqa .xmm2 b), .xop (.pclmulqdq .xmm2 .xmm13 0x00), .xop (.bin .pxor .xmm8 .xmm2),
     .xop (.bin .movdqa .xmm10 b), .xop (.pclmulqdq .xmm10 .xmm13 0x11), .xop (.bin .pxor .xmm10 a)]
  else
    [.xop (.bin .movdqa .xmm2 b), .xop (.pclmulqdq .xmm2 .xmm13 0x00),
     .xop (.bin .pxor .xmm8 .xmm11), .xop (.bin .pxor .xmm8 .xmm2),
     .xop (.bin .movdqa .xmm2 b), .xop (.pclmulqdq .xmm2 .xmm13 0x11),
     .xop (.bin .pxor .xmm10 a), .xop (.bin .pxor .xmm10 .xmm2)]) ++
  ([.xop (.bin .movdqa .xmm11 b), .xop (.pclmulqdq .xmm11 .xmm13 0x01),
    .xop (.bin .movdqa .xmm2 b), .xop (.pclmulqdq .xmm2 .xmm13 0x10),
    .xop (.bin .pxor .xmm9 .xmm11), .xop (.bin .pxor .xmm9 .xmm2)] : List Instr)

theorem lane_halfA (first : Bool) {ka : Nat} (hka : ka = 0 ∨ ka = 2) :
    zlaneSseBlock (halfA first (creg ka)) = some (halfASse first (creg ka)) := by
  rcases hka with rfl | rfl <;> cases first <;> rfl

theorem lane_halfB (first : Bool) {ka : Nat} (hka : ka = 0 ∨ ka = 2) :
    zlaneSseBlock (halfB first (creg ka) (creg (ka + 1))) = some (halfBSse first (creg ka) (creg (ka + 1))) := by
  rcases hka with rfl | rfl <;> cases first <;> rfl

/-- What `halfA` leaves of the copy in a lane: its products with the
powers, the middle one added (or written), the low one in `xmm11` (or
`xmm8`) and the high one in the copy's register. -/
def HalfA (first : Bool) (a : XReg) (u u' : State) : Prop :=
  let A := (if first then u.xmm .xmm2 else 0) ^^^ u.xmm a
  u'.xmm .xmm9 = (if first then 0 else u.xmm .xmm9) ^^^ pclmul A (u.xmm .xmm13) 0x01 ^^^ pclmul A (u.xmm .xmm13) 0x10 ∧
  u'.xmm (if first then .xmm8 else .xmm11) = pclmul A (u.xmm .xmm13) 0x00 ∧
  u'.xmm a = pclmul A (u.xmm .xmm13) 0x11 ∧
  (first = false → u'.xmm .xmm8 = u.xmm .xmm8) ∧
  Only [a, .xmm2, .xmm8, .xmm9, .xmm11] u u'

theorem halfASse_ok (first : Bool) {ka : Nat} (hka : ka = 0 ∨ ka = 2) (u : State) :
    WP isa (.block (halfASse first (creg ka))) u (HalfA first (creg ka) u) := by
  apply WP.of_runBlock
  rcases hka with rfl | rfl <;> cases first <;>
  simp only [halfASse, HalfA, creg, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa, Option.some.injEq,
    exists_eq_left', zero_xor_b, true_and, implies_true, BitVec.xor_comm (u.xmm .xmm2),
    false_implies] <;>
  refine ⟨fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- What `halfB` leaves in a lane: the products `halfA` left added with
those of the second copy. -/
def HalfB (first : Bool) (a b : XReg) (v v' : State) : Prop :=
  prod v' =
    ⟨(if first then v.xmm .xmm8 else v.xmm .xmm8 ^^^ v.xmm .xmm11) ^^^ pclmul (v.xmm b) (v.xmm .xmm13) 0x00,
     v.xmm .xmm9 ^^^ pclmul (v.xmm b) (v.xmm .xmm13) 0x01 ^^^ pclmul (v.xmm b) (v.xmm .xmm13) 0x10,
     (if first then v.xmm a else v.xmm .xmm10 ^^^ v.xmm a) ^^^ pclmul (v.xmm b) (v.xmm .xmm13) 0x11⟩ ∧
  Only [.xmm2, .xmm8, .xmm9, .xmm10, .xmm11] v v'

theorem halfBSse_ok (first : Bool) {ka : Nat} (hka : ka = 0 ∨ ka = 2) (v : State) :
    WP isa (.block (halfBSse first (creg ka) (creg (ka + 1)))) v (HalfB first (creg ka) (creg (ka + 1)) v) := by
  apply WP.of_runBlock
  rcases hka with rfl | rfl <;> cases first <;>
  simp only [halfBSse, HalfB, creg, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa, Option.some.injEq,
    exists_eq_left', prod] <;>
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  all_goals first
    | (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
       simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false])
    | simp only [BitVec.xor_comm (pclmul _ _ 0x11)]

/-- The products of a pair of copies: lane `l` of copies `ka` and `ka + 1`
times the powers at `scratch + tab g + 64 k`, added to the lane's products
(or written, for the first pair, with `Y` added to the first copy). -/
theorem pairC_ok {ka g : Nat} (hka : ka = 0 ∨ ka = 2) (first : Bool) (t : State)
    (hpa : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int)) 64)
    (hpb : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * (ka + 1) : Nat) : Int)) 64) :
    WP isa (.block (pairC ka g first)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = ((if first then Prod.zero else prod (t.zproj l)).acc
        ((if first then t.zlane .xmm2 l else 0) ^^^ t.zlane (creg ka) l)
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)).acc
        (t.zlane (creg (ka + 1)) l)
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * (ka + 1) : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      ZFrame [.xmm13, creg ka, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let apa := t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int)
  let apb := t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * (ka + 1) : Nat) : Int)
  let t₁ := ldZ t .xmm13 apa
  have ha13 : creg ka ≠ .xmm13 := by rcases hka with rfl | rfl <;> decide
  have hb13 : creg (ka + 1) ≠ .xmm13 := by rcases hka with rfl | rfl <;> decide
  have hab : creg (ka + 1) ∉ ([creg ka, .xmm2, .xmm8, .xmm9, .xmm11] : List XReg) := by
    rcases hka with rfl | rfl <;> decide
  have ha : creg ka ∉ ([.xmm2, .xmm8, .xmm9, .xmm10, .xmm11] : List XReg) := by
    rcases hka with rfl | rfl <;> decide
  rw [pairC, List.append_assoc, List.append_assoc, List.singleton_append, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hpa, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.zlanes (lane_halfA first hka) fun l _ => halfASse_ok first hka (t₁.zproj l))
    fun t₂ ⟨k₂, q₂⟩ => ?_
  let t₃ := ldZ t₂ .xmm13 apb
  have e₁ : t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    simp only [t₁, ldZ, State.setZ_gpr, State.setZ_mem, State.setZ_rd, State.setZ_wr, and_self]
  have e₂ : t₂.gpr = t.gpr ∧ t₂.mem = t.mem ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr :=
    ⟨k₂.gpr.trans e₁.1, k₂.mem.trans e₁.2.1, k₂.rd.trans e₁.2.2.1, k₂.wr.trans e₁.2.2.2⟩
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨t₃, by simp only [isa, exec, State.load512, ea_at, e₂.1, e₂.2.2.1, e₂.2.2.2, hpb, ite_true,
    Option.map_some]; rfl, ?_⟩
  have e₃ : t₃.gpr = t.gpr ∧ t₃.mem = t.mem ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
    simp only [t₃, ldZ, State.setZ_gpr, State.setZ_mem, State.setZ_rd, State.setZ_wr, e₂, and_self]
  refine WP.mono (WP.zlanes (lane_halfB first hka) fun l _ => halfBSse_ok first hka (t₃.zproj l))
    fun t' ⟨k', q'⟩ => ⟨fun l hl => ?_, ?_⟩
  · -- The lane's values at each state.
    have z₁ : ∀ r, r ≠ .xmm13 → t₁.zlane r l = t.zlane r l := fun r h => ldZ_zlane_ne _ _ h hl
    have p₁ : t₁.zlane .xmm13 l = t.mem.readW (apa + BitVec.ofNat 64 (16 * l)) 128 := ldZ_zlane t _ _ hl
    have z₃ : ∀ r, r ≠ .xmm13 → t₃.zlane r l = t₂.zlane r l := fun r h => ldZ_zlane_ne _ _ h hl
    have p₃ : t₃.zlane .xmm13 l = t.mem.readW (apb + BitVec.ofNat 64 (16 * l)) 128 := by
      rw [ldZ_zlane t₂ _ _ hl, e₂.2.1]
    obtain ⟨m₂, lo₂, hi₂, k8₂, o₂⟩ := q₂ l hl
    have kb : t₂.zlane (creg (ka + 1)) l = t.zlane (creg (ka + 1)) l := by
      have := o₂.xmm _ hab
      simp only [State.zproj_xmm] at this
      rw [this, z₁ _ hb13]
    have k10 : t₂.zlane .xmm10 l = t.zlane .xmm10 l := by
      have := o₂.xmm .xmm10 (by rcases hka with rfl | rfl <;> decide)
      simp only [State.zproj_xmm] at this
      rw [this, z₁ _ (by decide)]
    simp only [State.zproj_xmm] at m₂ lo₂ hi₂ k8₂
    rw [(q' l hl).1]
    simp only [State.zproj_xmm, p₃, z₃ _ hb13, z₃ _ ha13, z₃ .xmm8 (by decide), z₃ .xmm9 (by decide),
      z₃ .xmm10 (by decide), z₃ .xmm11 (by decide), kb, hi₂, m₂, k10]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_xor_b] at lo₂ k8₂ ⊢
      rw [lo₂, k8₂ trivial, p₁, z₁ _ ha13, z₁ .xmm9 (by decide), z₁ .xmm8 (by decide)]
      simp only [prod, Prod.acc, State.zproj_xmm]
      rfl
    · simp only [↓reduceIte] at lo₂ ⊢
      rw [lo₂, p₁, z₁ _ ha13, z₁ .xmm2 (by decide)]
      simp only [Prod.acc, Prod.zero, zero_xor_b]
      rfl
  · refine ⟨k'.gpr.trans e₃.1, k'.mem.trans e₃.2.1, k'.rd.trans e₃.2.2.1, k'.wr.trans e₃.2.2.2,
      fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' := (q' l hl).2.xmm r (by simp [hr])
    have h₂ := (q₂ l hl).2.2.2.2.xmm r (by simp [hr])
    simp only [State.zproj_xmm] at h' h₂
    rw [h', ldZ_zlane_ne _ _ hr.1 hl, h₂, ldZ_zlane_ne _ _ hr.1 hl]

/-! ## The GHASH of a group -/

/-- The powers of 48 blocks at `scratch` and the reduction constant at
`scratch + 832`. -/
structure CEnv (s₀ : State) (T : Nat → Nat → Nat → Block) (s : State) : Prop where
  r11 : s.gpr .r11 = pp s₀
  pv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l
  pm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly
  inp : ∀ o : Nat, o + 64 ≤ 1024 → InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 (o : Int)) 64

theorem CEnv.zframe {s₀ : State} {T : Nat → Nat → Nat → Block} {s s' : State} {rs : List XReg}
    (h : CEnv s₀ T s) (f : ZFrame rs s s') : CEnv s₀ T s' :=
  ⟨by rw [f.gpr]; exact h.r11, fun g hg k hk l hl => by rw [f.mem]; exact h.pv g hg k hk l hl,
    fun l hl => by rw [f.mem]; exact h.pm l hl, fun o ho => by rw [f.rd, f.wr]; exact h.inp o ho⟩

/-- The pairs done before the blocks after round `j` of group `g`. -/
abbrev npC (g j : Nat) : Nat := 2 * g + (if j ≤ 4 then 0 else if j ≤ 7 then 1 else 2)

/-- What holds before the blocks after round `j` of a group, group `g` of
three: the copies of the group before (`W`) not yet hashed, and the products
of the pairs done (or, before the first, `Y` in `zmm2`), or, after the
reduction, the new `Y`, with the reduction constant in `zmm1`. -/
def QC (s₀ : State) (T : Nat → Nat → Nat → Block) (X W : Nat → Block) (yl : Nat → Block)
    (first last : Bool) (g j : Nat) (s : State) : Prop :=
  CEnv s₀ T s ∧
  (j ≤ 4 → ∀ k < 2, ∀ l < 4, s.zlane (creg k) l = W (4 * k + l)) ∧
  (j ≤ 7 → ∀ k < 2, ∀ l < 4, s.zlane (creg (2 + k)) l = W (4 * (2 + k) + l)) ∧
  (if last = true ∧ 9 < j then
    s.zlane .xmm2 0 = yNew48 X T (fun _ => 0) ∧ (∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0) ∧
      ∀ l < 4, s.zlane .xmm1 l = poly
   else ((first = false ∨ 4 < j) → ∀ l < 4, prod (s.zproj l) = acc48 X T (fun _ => 0) l (npC g j)) ∧
     (first = true → j ≤ 4 → ∀ l < 4, s.zlane .xmm2 l = yl l))

theorem QC.zframe {s₀ : State} {T : Nat → Nat → Nat → Block} {X W : Nat → Block} {yl : Nat → Block}
    {first last : Bool} {g j : Nat} {s s' : State} {rs : List XReg}
    (h : QC s₀ T X W yl first last g j s) (f : ZFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm7, .xmm1, .xmm12, .xmm15, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QC s₀ T X W yl first last g j s' := by
  obtain ⟨hE, c01, c23, h2⟩ := h
  have k : ∀ r ∈ ([.xmm7, .xmm1, .xmm12, .xmm15, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4,
      s'.zlane r l = s.zlane r l := fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  have kc : ∀ k < 4, ∀ l < 4, s'.zlane (creg k) l = s.zlane (creg k) l := fun k hk l hl => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> exact k _ (by decide) l hl
  have kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.zframe f, fun hj k hk l hl => by rw [kc k (by omega) l hl]; exact c01 hj k hk l hl,
    fun hj k hk l hl => by rw [kc (2 + k) (by omega) l hl]; exact c23 hj k hk l hl, ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1,
      fun l h1 h4 => by rw [k .xmm2 (by decide) l h4]; exact h2.2.1 l h1 h4,
      fun l hl => by rw [k .xmm1 (by decide) l hl]; exact h2.2.2 l hl⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
      fun hf hj l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 hf hj l hl⟩

/-- The reduction constant loaded, and the four lanes reduced into `Y`. -/
theorem finC_ok {s₀ : State} {T : Nat → Nat → Nat → Block} {s : State} (hE : CEnv s₀ T s) :
    WP isa (.block fin48) s fun s' => CEnv s₀ T s' ∧
      s'.zlane .xmm2 0 =
        (reduceB (prod (s.zproj 0)) ^^^ reduceB (prod (s.zproj 2))) ^^^
          (reduceB (prod (s.zproj 1)) ^^^ reduceB (prod (s.zproj 3))) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧
      ZFrame gRegs48 s s' := by
  let q := s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [hE.r11]; exact hE.inp 832 (by decide)
  rw [fin48, WP.block_cons_iff]
  refine ⟨ldZ s .xmm1 q, by simp only [isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have h1 : ∀ l < 4, (ldZ s .xmm1 q).zlane .xmm1 l = poly := fun l hl => by
    rw [ldZ_zlane _ _ _ hl, ofInt_add_ofNat, hE.r11]; exact hE.pm l hl
  have f₁ : ZFrame [.xmm1] s (ldZ s .xmm1 q) :=
    ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ldZ_zlane_ne _ _ (fun h => hr (by simp [h])) hl⟩
  have kp : ∀ l < 4, prod ((ldZ s .xmm1 q).zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, ldZ_zlane_ne _ _ (show XReg.xmm8 ≠ .xmm1 by decide) hl,
      ldZ_zlane_ne _ _ (show XReg.xmm9 ≠ .xmm1 by decide) hl, ldZ_zlane_ne _ _ (show XReg.xmm10 ≠ .xmm1 by decide) hl]
  refine WP.mono (fin_ok _ h1) fun s' ⟨y0, y1, f'⟩ =>
    ⟨(hE.zframe f₁).zframe f', ?_, y1, fun l hl => by rw [f'.zlane _ (by decide) l hl]; exact h1 l hl,
      (f₁.comp f').mono (by decide)⟩
  rw [y0, kp 0 (by decide), kp 1 (by decide), kp 2 (by decide), kp 3 (by decide)]

/-- `grpM_ok`'s obligation for the GHASH work between the rounds of a
group, on the copies `W` of the group before, blocks `16 g …` of `X` (with
`Y` added to the first, if `first`): the pairs after rounds 4 and 7, and,
for the last group, the reduction after round 9. -/
theorem gqC_ok {s₀ : State} {T : Nat → Nat → Nat → Block} {X W : Nat → Block} {yl : Nat → Block}
    {first last : Bool} {g : Nat} (hg : g < 3)
    (hX : ∀ k < 4, ∀ l < 4, X (16 * g + 4 * k + l) = (if first = true ∧ k = 0 then yl l else 0) ^^^ W (4 * k + l))
    (hfirst : first = true → ∀ l < 4, acc48 X T (fun _ => 0) l (2 * g) = Prod.zero)
    (hlast : last = true → g = 2) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → QC s₀ T X W yl first last g j s →
      WP isa (.block (gqC first last g j)) s fun s' =>
        QC s₀ T X W yl first last g (j + 1) s' ∧ ZFrame gRegs48 s s' := by
  intro j hj1 hj9 s _ ⟨hE, c01, c23, h2⟩
  have e2g : 2 * g / 2 = g := by omega
  have e2g1 : (2 * g + 1) / 2 = g := by omega
  have pa0 : pa (2 * g) = 0 := by simp only [pa]; omega
  have pa1 : pa (2 * g + 1) = 2 := by simp only [pa]; omega
  by_cases h4 : j = 4
  · subst h4
    rw [ite_f (by omega)] at h2
    rw [show gqC first last g 4 = pairC 0 g first from rfl]
    refine WP.mono (pairC_ok (ka := 0) (g := g) (Or.inl rfl) first s
        (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega))
        (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega)))
      fun s' ⟨p', f'⟩ => ⟨⟨hE.zframe f', fun h => absurd h (by decide),
        fun _ k hk l hl => ?_, ?_⟩, f'.mono (by decide)⟩
    · rw [f'.zlane _ (by
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl <;> decide) l hl]
      exact c23 (by decide) k hk l hl
    · rw [ite_f (by omega)]
      refine ⟨fun _ l hl => ?_, fun _ h => absurd h (by decide)⟩
      rw [p' l hl, show npC g (4 + 1) = 2 * g + 1 from rfl, acc48_succ, e2g, pa0, hE.r11, ofInt_add_ofNat,
        ofInt_add_ofNat, hE.pv g hg 0 (by decide) l hl, hE.pv g hg (0 + 1) (by decide) l hl,
        c01 (by decide) 0 (by decide) l hl, c01 (by decide) (0 + 1) (by decide) l hl]
      simp only [inp48, ite_self, zero_xor_b]
      rw [hX 0 (by decide) l hl, hX (0 + 1) (by decide) l hl]
      cases first
      · simp only [Bool.false_eq_true, false_and, ↓reduceIte, zero_xor_b]
        rw [h2.1 (Or.inl rfl) l hl]
        rfl
      · simp only [true_and, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, zero_xor_b]
        rw [hfirst rfl l hl, h2.2 rfl (by decide) l hl]
  by_cases h7 : j = 7
  · subst h7
    rw [ite_f (by omega)] at h2
    rw [show gqC first last g 7 = pairC 2 g false from rfl]
    refine WP.mono (pairC_ok (ka := 2) (g := g) (Or.inr rfl) false s
        (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega))
        (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega)))
      fun s' ⟨p', f'⟩ => ⟨⟨hE.zframe f', fun h => absurd h (by decide),
        fun h => absurd h (by decide), ?_⟩, f'.mono (by decide)⟩
    rw [ite_f (by omega)]
    refine ⟨fun _ l hl => ?_, fun _ h => absurd h (by decide)⟩
    rw [p' l hl, show npC g (7 + 1) = 2 * g + 1 + 1 from rfl, acc48_succ, e2g1, pa1, hE.r11, ofInt_add_ofNat,
      ofInt_add_ofNat, hE.pv g hg 2 (by decide) l hl, hE.pv g hg (2 + 1) (by decide) l hl,
      c23 (by decide) 0 (by decide) l hl, c23 (by decide) 1 (by decide) l hl]
    simp only [inp48, ite_self, zero_xor_b, Bool.false_eq_true, ↓reduceIte]
    rw [hX 2 (by decide) l hl, hX (2 + 1) (by decide) l hl, h2.1 (Or.inr (by decide)) l hl]
    simp only [Nat.reduceEqDiff, and_false, ↓reduceIte, zero_xor_b, Nat.reduceAdd]
    rfl
  by_cases h9 : j = 9 ∧ last = true
  · obtain ⟨rfl, rfl⟩ := h9
    obtain rfl := hlast rfl
    rw [ite_f (by decide)] at h2
    rw [show gqC first true 2 9 = fin48 from rfl]
    refine WP.mono (finC_ok hE) fun s' ⟨hE', y0, y1, m1, f'⟩ =>
      ⟨⟨hE', fun h => absurd h (by decide), fun h => absurd h (by decide), ?_⟩, f'⟩
    rw [ite_t (by decide)]
    have p := h2.1 (Or.inr (by decide))
    rw [show npC 2 9 = 6 from rfl] at p
    exact ⟨by rw [y0, p 0 (by decide), p 1 (by decide), p 2 (by decide), p 3 (by decide)], y1, m1⟩
  · -- Nothing.
    have hgq : gqC first last g j = [] := by
      simp only [gqC, h4, h7, ite_false]
      split
      · rename_i h; exact absurd h h9
      · rfl
    rw [hgq]
    have hc : ¬ (last = true ∧ 9 < j) := by omega
    have hc' : ¬ (last = true ∧ 9 < j + 1) := fun h => h9 ⟨by omega, h.1⟩
    rw [ite_f hc] at h2
    refine WP.block_nil ⟨⟨hE, fun h => c01 (by omega), fun h => c23 (by omega), ?_⟩, ZFrame.refl _ _⟩
    rw [ite_f hc']
    have hnp : npC g (j + 1) = npC g j := by
      have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 8 ∨ j = 9 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    exact ⟨fun h l hl => by
      rw [hnp]; exact h2.1 (by rcases h with h | h; exact Or.inl h; exact Or.inr (by omega)) l hl,
      fun hf h => h2.2 hf (by omega)⟩

/-! ## A group -/

/-- The encryption after `c` blocks, in place or out of place
(`StitchZ.AInvM`), with the counters' increment at `scratch + 896`. -/
structure CA (ix : Bool) (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  im : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (896 + 16 * l)) 128 = four
  r11 : s.gpr .r11 = pp s₀
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [Stitch.wR ix s₀, pR s₀] s₀.mem s.mem
  out : ∀ k < c, blockAt s.mem (Stitch.wAddr ix s₀ k) = ctb s₀ k
  src : ∀ k < nb s₀, c ≤ k → blockAt s.mem (bAddr s₀ k) = blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CA.keys {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {c : Nat} {s : State} (hI : CA ix s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, Stitch.sch_frameM hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

/-- The encryption state kept by changes of `rdx` and `r9` alone. -/
theorem CA.gpr2 {ix : Bool} {s₀ : State} {c : Nat} {s s' : State} (h : CA ix s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hl : ∀ r l, s'.zlane r l = s.zlane r l)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CA ix s₀ c s' :=
  ⟨h.le, fun l hl' => by rw [hl]; exact h.ctr l hl', fun l hl' => by rw [hl]; exact h.msk l hl',
    fun l hl' => by rw [hm]; exact h.im l hl',
    by rw [hg _ (by decide) (by decide)]; exact h.r11,
    by rw [hg _ (by decide) (by decide)]; exact h.rdi, by rw [hg _ (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide)]; exact h.r10,
    by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.out k hk,
    fun k hk hc => by rw [hm]; exact h.src k hk hc, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

/-- The increment loaded, and the counter blocks of a group. -/
theorem incCtrs_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {c : Nat} {s : State} (hI : CA ix s₀ c s) :
    WP isa (.block (.vmovdqu32Load .xmm11 incAt :: ctrsZ .xmm14 .xmm0 .xmm11 aregs)) s fun s' =>
      (∀ k (h : k < aregs.length), ∀ l < 4,
        s'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) ∧
      (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 (c + 4 * aregs.length + l) (cb s₀)) ∧
      ZFrame (.xmm11 :: .xmm14 :: aregs) s s' := by
  let q := s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)) 64 := by
    rw [hI.rd, hI.wr, hI.r11]; exact in_rdwr (in_sub_int hp.p_in (by decide))
  rw [WP.block_cons_iff]
  refine ⟨ldZ s .xmm11 q, by
    simp only [incAt, isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have f₁ : ZFrame [.xmm11] s (ldZ s .xmm11 q) :=
    ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ldZ_zlane_ne _ _ (fun h => hr (by simp [h])) hl⟩
  refine WP.mono (ctrsZ_ok .xmm14 .xmm0 .xmm11 (by decide) (by decide) aregs _ (cb s₀) c (by decide) (by decide)
    (fun l hl => by rw [ldZ_zlane_ne _ _ (by decide) hl]; exact hI.ctr l hl)
    (fun l hl => by rw [ldZ_zlane_ne _ _ (by decide) hl]; exact hI.msk l hl)
    (fun l hl => by rw [ldZ_zlane _ _ _ hl, ofInt_add_ofNat, hI.r11]; exact hI.im l hl))
    fun s' ⟨e, c', f'⟩ => ⟨e, c', f₁.comp f'⟩

/-- The SSE block of `copies`'s lanes. -/
def copiesSse : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm3), .xop (.bin .pshufb .xmm7 .xmm0),
   .xop (.bin .movdqa .xmm1 .xmm4), .xop (.bin .pshufb .xmm1 .xmm0),
   .xop (.bin .movdqa .xmm12 .xmm5), .xop (.bin .pshufb .xmm12 .xmm0),
   .xop (.bin .movdqa .xmm15 .xmm6), .xop (.bin .pshufb .xmm15 .xmm0)]

theorem lane_copies : zlaneSseBlock copies = some copiesSse := rfl

theorem copiesSse_ok (u : State) :
    WP isa (.block copiesSse) u fun u' =>
      u'.xmm .xmm7 = XBinOp.eval .pshufb (u.xmm .xmm3) (u.xmm .xmm0) ∧
      u'.xmm .xmm1 = XBinOp.eval .pshufb (u.xmm .xmm4) (u.xmm .xmm0) ∧
      u'.xmm .xmm12 = XBinOp.eval .pshufb (u.xmm .xmm5) (u.xmm .xmm0) ∧
      u'.xmm .xmm15 = XBinOp.eval .pshufb (u.xmm .xmm6) (u.xmm .xmm0) ∧
      Only [.xmm7, .xmm1, .xmm12, .xmm15] u u' := by
  apply WP.of_runBlock
  simp only [copiesSse, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa,
    State.setXmm, eval_movdqa, Option.some.injEq, exists_eq_left', true_and]
  refine ⟨fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers of the group, byte-reversed, in the copies. -/
theorem copies_ok (s : State) (h0 : ∀ l < 4, s.zlane .xmm0 l = revMask) :
    WP isa (.block copies) s fun s' =>
      (∀ k (h : k < aregs.length), ∀ l < 4,
        s'.zlane (creg k) l = XBinOp.eval .pshufb (s.zlane aregs[k] l) revMask) ∧
      ZFrame [.xmm7, .xmm1, .xmm12, .xmm15] s s' := by
  refine WP.mono (WP.zlanes lane_copies fun l _ => copiesSse_ok (s.zproj l)) fun s' ⟨k', q⟩ =>
    ⟨fun k hk l hl => ?_, k'.gpr, k'.mem, k'.rd, k'.wr, fun r hr l hl => ?_⟩
  · obtain ⟨c0, c1, c2, c3, _⟩ := q l hl
    simp only [State.zproj_xmm, h0 l hl] at c0 c1 c2 c3
    simp only [aregs, List.length_cons, List.length_nil] at hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2
    · exact c3
  · have := (q l hl).2.2.2.2.xmm r hr
    simpa only [State.zproj_xmm] using this

theorem grpC_keeps (j : Nat) (g : Nat → List Instr) (hg : ∀ j, (g j).all Instr.keepsH = true) (ld : Bool) :
    (grpC j g ld).all Instr.keepsH = true := by
  simp [grpC, Code.all, StitchZH.aes_keeps _ g hg, ctrsZ, Impl.Gcm.X86_64.StitchZ.xorDataZM, aregs, copies,
    Instr.keepsH]

/-- The registers the group's code writes besides the copies. -/
abbrev gTmp : List XReg := .xmm11 :: .xmm13 :: .xmm14 :: aregs

/-- A group: `grpC j g ix` encrypts blocks `c`–`c + 15` (`CA`), and leaves
them in the copies. `Q` is what the GHASH work `g` keeps between the
rounds; `R` what holds of it once the output is written and the copies
made. -/
theorem grpM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0)
    (Q : Nat → State → Prop) (R : State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame gTmp s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → r ∉ ([.xmm7, .xmm1, .xmm12, .xmm15] : List XReg) →
        ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem → R s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : CA ix s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hr8 : ix = true → s.gpr .r8 = dp s₀ - Stitch.op s₀)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (Stitch.wp ix s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (grpC j g ix) s fun s' => CA ix s₀ (c + 16) s' ∧ R s' ∧ s'.gpr = s.gpr ∧
      (∀ k < 4, ∀ l < 4, s'.zlane (creg k) l = ctb s₀ (c + 4 * k + l)) ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (grpC j g ix) s fun s' => CA ix s₀ (c + 16) s' ∧ R s' ∧ s'.gpr = s.gpr ∧
      (∀ k < 4, ∀ l < 4, s'.zlane (creg k) l = ctb s₀ (c + 4 * k + l)) from
    WP.mono (WP.hkeepCode (by rfl) (grpC_keeps j g hgh ix) h)
      (fun t ⟨⟨ha, hr, hg, hc⟩, hh⟩ => ⟨ha, hr, hg, hc, hCache.keep hh (ha.keys hp)⟩)
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwd := hp.wrap_d
  have hw := hp.wrap_w
  refine WP.seq (WP.mono (WP.hkeep (by decide) (incCtrs_ok hp hI)) fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys (hI.keys hp) f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => by
    simp only [List.mem_cons] at hr ⊢
    rcases hr with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h)))
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      simp only [List.mem_cons] at hr ⊢
      rcases hr with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h)))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have raddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) =
      Stitch.wp ix s₀ + BitVec.ofNat 64 (16 * (c + i)) := fun i => addr_eq (by omega)
  have addr : ∀ i, Stitch.oA s ix + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i => by
    cases ix
    · exact raddr i
    · show s.gpr .rdx + s.gpr .r8 + _ = dp s₀ + _
      rw [hr8 rfl]
      exact StitchZTo.src_addr (raddr i)
  have oaddr : ∀ i, Stitch.oA s false + BitVec.ofNat 64 (64 * j + 16 * i) = Stitch.wAddr ix s₀ (c + i) :=
    fun i => raddr i
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega
  have o₂ : Stitch.oA s₂ false = Stitch.oA s false := Stitch.oA_congr false hg₂
  have i₂ : Stitch.oA s₂ ix = Stitch.oA s ix := Stitch.oA_congr ix hg₂
  rw [WP.block_append_iff]
  refine WP.mono (StitchZ.xorDataZM_ok false ix .xmm13 aregs j s₂ hnd h13
      (fun k hk => by
        rw [i₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e64, addr]
        exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [o₂, f₂.wr, f₁.wr, hI.wr, e64, oaddr]
        exact in_sub hp.w_in (by simp [aregs] at hk; omega))
      (fun a b hab hb l hl => by
        rw [i₂, o₂, e16, show 64 * (j + a) = 64 * j + 16 * (4 * a) by omega, addr, oaddr]
        simp only [aregs, List.length_cons, List.length_nil] at hb
        cases ix
        · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
        · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right
            (Offset.sub_base _ (by omega)))
      (by simp only [aregs, List.length_cons, List.length_nil]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃, cp₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, i₂, o₂] at b₃
  rw [o₂] at cp₃
  rw [hm₂, o₂] at fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, oaddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (Stitch.wAddr ix s₀ (c + (4 * k + l))) =
        blk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega) (by omega)] at this
  have fr' : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  have dsep : ∀ k < nb s₀, c + 16 ≤ k → ∀ r ∈ [(⟨Stitch.wAddr ix s₀ c, 256⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk hck r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    cases ix
    · intro a h₁ h₂
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hwd hk hc (by omega) h₁ h₂
    · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  -- The blocks written.
  have out₃ : ∀ k < c + 16, blockAt s₃.mem (Stitch.wAddr ix s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.out k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 4) hj (i % 4) (by omega), ks (i / 4) hj (i % 4) (by omega),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]
  have m0₃ : ∀ l < 4, s₃.zlane .xmm0 l = revMask := fun l hl => by
    rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2 rfl⟩) l hl, f₁.zlane _ (by decide) l hl, hI.msk l hl]
  refine WP.mono (copies_ok s₃ m0₃) fun s₄ ⟨cp₄, f₄⟩ => ?_
  have gs₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, gs]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs₄, hI.r11], by rw [gs₄, hI.rdi],
    by rw [gs₄, hI.rsi], by rw [gs₄, hI.r10], ?_, fun k hk => by rw [f₄.mem]; exact out₃ k hk, ?_,
    by rw [f₄.rd, rd₃, f₂.rd, f₁.rd, hI.rd], by rw [f₄.wr, wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₄ hQ₂ (by rw [f₄.gpr, g₃]) (by rw [f₄.rd, rd₃]) (by rw [f₄.wr, wr₃])
      (fun r h1 h2 h3 l hl => by rw [f₄.zlane r h3 l hl, x₃ r h1 h2 l hl]) (by rw [f₄.mem, hm₂]; exact fr'),
    gs₄, fun k hk l hl => ?_⟩
  · rw [f₄.zlane _ (by decide) l hl, x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [f₄.zlane _ (by decide) l hl]; exact m0₃ l hl
  · rw [f₄.mem, keepWM hp hc fr' (by omega)]; exact hI.im l hl
  · rw [f₄.mem]
    refine hI.frame.trans (fr'.sub fun r hr => ⟨Stitch.wR ix s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  · intro k hk hck
    rw [f₄.mem, blockAt_frame fr' (dsep k hk hck)]
    exact hI.src k hk (by omega)
  · have hk' : k < aregs.length := by simp [aregs]; omega
    rw [cp₄ k hk' l hl, cp₃ k hk' l hl, e16, oaddr, out₃ _ (by omega)]
    congr 1; omega

/-! ## Fewer than 48 blocks -/

theorem clmul_zero_left (b : BitVec 64) : clmul 0 b = 0 := by
  have hf : (fun acc j => if (0 : BitVec 64).getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) =
      fun (acc : BitVec 128) (_ : Nat) => acc := by
    funext acc j
    simp
  unfold clmul
  rw [hf]
  generalize List.range 64 = l
  induction l with
  | nil => rfl
  | cons j l ih => exact ih

/-- The products of zero add nothing. -/
theorem Prod.acc_zero_left (p : Prod) (b : BitVec 128) : p.acc 0 b = p := by
  have he : ∀ i, BitVec.extractLsb' i 64 (0 : BitVec 128) = 0 := fun i => by
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  simp only [Prod.acc, pclmul, qword, he, clmul_zero_left, StitchZH.xor_zero128]

/-- The 48 blocks whose products a body of fewer than three groups adds:
zero for the groups before `g₀`, then the blocks `B`, with `Y` (`yl`) added
to the first four. -/
def padX (g₀ : Nat) (B yl : Nat → Block) (i : Nat) : Block :=
  if i < 16 * g₀ then 0 else (if i - 16 * g₀ < 4 then yl (i - 16 * g₀) else 0) ^^^ B (i - 16 * g₀)

/-- The blocks before group `g₀` add nothing. -/
theorem acc48_pad (g₀ : Nat) (B yl : Nat → Block) (T : Nat → Nat → Nat → Block) {l : Nat} (hl : l < 4) :
    ∀ n, n ≤ 2 * g₀ → acc48 (padX g₀ B yl) T (fun _ => 0) l n = Prod.zero
  | 0, _ => rfl
  | n + 1, h => by
    have hp : pa n ≤ 2 := by simp only [pa]; omega
    have z : ∀ k, k ≤ 3 → inp48 (padX g₀ B yl) (fun _ => 0) (n / 2) k l = 0 := fun k hk => by
      simp only [inp48, ite_self, zero_xor_b, padX]
      rw [ite_t (by omega)]
    rw [acc48_succ, acc48_pad g₀ B yl T hl n (by omega), z _ (by omega), z _ (by omega), Prod.acc_zero_left,
      Prod.acc_zero_left]

/-- Group `g = g₀ + t` of the 48 blocks: the blocks of output group
`e - 1 + t`, with `Y` added to the first four of the first group. -/
theorem padX_grp {s₀ : State} {g₀ t g e : Nat} (hg : g = g₀ + t) (h1 : 1 ≤ e) (yl : Nat → Block)
    (first : Bool) (hf : first = true ↔ t = 0) :
    ∀ k < 4, ∀ l < 4, padX g₀ (fun i => ctb s₀ (16 * (e - 1) + i)) yl (16 * g + 4 * k + l) =
      (if first = true ∧ k = 0 then yl l else 0) ^^^ ctb s₀ (16 * (e + t) - 16 + (4 * k + l)) := by
  intro k hk l hl
  subst hg
  have e1 : 16 * (g₀ + t) + 4 * k + l - 16 * g₀ = 16 * t + 4 * k + l := by omega
  have e2 : 16 * (e - 1) + (16 * t + 4 * k + l) = 16 * (e + t) - 16 + (4 * k + l) := by omega
  simp only [padX]
  rw [ite_f (by omega), e1, e2]
  by_cases h : t = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_t (by omega), ite_t ⟨hf.mpr rfl, rfl⟩]
    congr 2
    omega
  · rw [ite_f (by omega), ite_f (fun h' => h ⟨hf.mp h'.1, h'.2⟩)]

theorem ghash_appendN (h y : Block) (f : Nat → Block) (a n : Nat) :
    ghashFrom h y ((List.range (a + n)).map f) =
      ghashFrom h (ghashFrom h y ((List.range a).map f)) ((List.range n).map fun i => f (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

theorem ghash_zeros (H : Block) (f : Nat → Block) : ∀ n, (∀ i < n, f i = 0) →
    ghashFrom H 0 ((List.range n).map f) = 0
  | 0, _ => rfl
  | n + 1, h => by
    have ih := ghash_zeros H f n (fun i hi => h i (by omega))
    simp only [ghashFrom] at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, h n (by omega), zero_xor_b]
    exact VG.Proof.Gcm.mul_zero_left H

/-- `GHASH` over the 48 blocks of `padX` is `GHASH` from `Y` over the blocks
after the zeros. -/
theorem ghash_pad (H : Block) {g₀ : Nat} (hg : g₀ ≤ 2) (B yl : Nat → Block)
    (hy : ∀ l, 1 ≤ l → l < 4 → yl l = 0) :
    ghashFrom H 0 ((List.range 48).map (padX g₀ B yl)) =
      ghashFrom H (yl 0) ((List.range (48 - 16 * g₀)).map B) := by
  obtain ⟨n, hn⟩ : ∃ n, 48 - 16 * g₀ = n + 1 := ⟨47 - 16 * g₀, by omega⟩
  have h48 : (48 : Nat) = 16 * g₀ + (n + 1) := by omega
  rw [hn, show List.range 48 = List.range (16 * g₀ + (n + 1)) from congrArg List.range h48, ghash_appendN,
    ghash_zeros H _ _ (fun i hi => by simp only [padX]; rw [ite_t hi])]
  have hx : ∀ i, padX g₀ B yl (16 * g₀ + i) = (if i < 4 then yl i else 0) ^^^ B i := fun i => by
    simp only [padX]
    rw [ite_f (by omega), show 16 * g₀ + i - 16 * g₀ = i by omega]
  simp only [hx, ghashFrom]
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons, List.map_map,
    List.map_map, ite_t (by decide), zero_xor_b]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  by_cases h4 : i + 1 < 4
  · rw [ite_t h4, hy _ (by omega) h4, zero_xor_b]
  · rw [ite_f h4, zero_xor_b]

/-! ## The invariant, and a group -/

theorem CEnv.of_eq {s₀ : State} {T : Nat → Nat → Nat → Block} {s s' : State} (h : CEnv s₀ T s)
    (hg : s'.gpr .r11 = s.gpr .r11) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    CEnv s₀ T s' :=
  ⟨by rw [hg]; exact h.r11, fun g hg k hk l hl => by rw [hm]; exact h.pv g hg k hk l hl,
    fun l hl => by rw [hm]; exact h.pm l hl, fun o ho => by rw [hrd, hwr]; exact h.inp o ho⟩

/-- `e` groups encrypted, the first `e - 1` of the output hashed and group
`e - 1` in the copies (`StitchZ.EInvM`, with the increment in the working
space, and the powers of 48 blocks and the reduction constant there). -/
structure CInv (ix : Bool) (s₀ : State) (T : Nat → Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : CA ix s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  r8 : ix = true → s.gpr .r8 = dp s₀ - Stitch.op s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  env : CEnv s₀ T s
  cp : ∀ k < 4, ∀ l < 4, s.zlane (creg k) l = ctb s₀ (16 * (e - 1) + 4 * k + l)
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem gqC_keeps (first last : Bool) (g j : Nat) : (gqC first last g j).all Instr.keepsH = true := by
  unfold gqC
  split
  · cases first <;> rfl
  · split
    · rfl
    · split <;> rfl

/-- A group of a body, group `g` of three: blocks `c`–`c + 15` encrypted
and copied, and the group before, in the copies, hashed between the rounds. -/
theorem stepC {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block} {X : Nat → Block}
    {yl : Nat → Block} {first last : Bool} {g : Nat} (hg : g < 3) (hlast : last = true → g = 2)
    {c j : Nat} (hc : c + 16 ≤ nb s₀)
    (hX : ∀ k < 4, ∀ l < 4, X (16 * g + 4 * k + l) =
      (if first = true ∧ k = 0 then yl l else 0) ^^^ ctb s₀ (c - 16 + (4 * k + l)))
    (hfirst : first = true → ∀ l < 4, acc48 X T (fun _ => 0) l (2 * g) = Prod.zero)
    {s : State} (hA : CA ix s₀ c s) (hE : CEnv s₀ T s)
    (hcp : ∀ k < 4, ∀ l < 4, s.zlane (creg k) l = ctb s₀ (c - 16 + (4 * k + l)))
    (hacc : first = false → ∀ l < 4, prod (s.zproj l) = acc48 X T (fun _ => 0) l (2 * g))
    (hy : first = true → ∀ l < 4, s.zlane .xmm2 l = yl l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hr8 : ix = true → s.gpr .r8 = dp s₀ - Stitch.op s₀)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (Stitch.wp ix s₀).toNat + 16 * c) :
    WP isa (grpC j (gqC first last g) ix) s fun s' =>
      CA ix s₀ (c + 16) s' ∧ CEnv s₀ T s' ∧ s'.gpr = s.gpr ∧
      (∀ k < 4, ∀ l < 4, s'.zlane (creg k) l = ctb s₀ (c + 4 * k + l)) ∧
      (if last = true then
        s'.zlane .xmm2 0 = yNew48 X T (fun _ => 0) ∧ ∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0
       else ∀ l < 4, prod (s'.zproj l) = acc48 X T (fun _ => 0) l (2 * g + 2)) ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  refine WP.mono (grpM_ok hp (gqC first last g) gRegs48 (by decide)
      (QC s₀ T X (fun n => ctb s₀ (c - 16 + n)) yl first last g)
      (fun t => CEnv s₀ T t ∧ (if last = true then
        t.zlane .xmm2 0 = yNew48 X T (fun _ => 0) ∧ ∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0
       else ∀ l < 4, prod (t.zproj l) = acc48 X T (fun _ => 0) l (2 * g + 2)))
      (gqC_ok hg hX hfirst hlast) (fun _ _ _ h f => h.zframe f (by decide)) ?_ hc hA hCache
      (gqC_keeps first last g) hr8 hrdx ?_)
    fun s' ⟨hA', ⟨hE', hacc'⟩, hg', hcp', hK'⟩ => ⟨hA', hE', hg', hcp', hacc', hK'⟩
  · -- The output written and the copies made keep the products, or `Y`.
    rintro t t' ⟨hE', _, _, h2⟩ hgpr hrd hwr hl hf
    refine ⟨⟨by rw [hgpr]; exact hE'.r11,
      fun g' hg' k hk l hl' => by
        rw [keepWM hp hc hf (by simp only [tab]; omega)]; exact hE'.pv g' hg' k hk l hl',
      fun l hl' => by rw [keepWM hp hc hf (by omega)]; exact hE'.pm l hl',
      fun o ho => by rw [hrd, hwr]; exact hE'.inp o ho⟩, ?_⟩
    cases last
    · rw [ite_f (by decide)] at h2 ⊢
      intro l hl'
      have kp : prod (t'.zproj l) = prod (t.zproj l) := by
        simp only [prod, State.zproj_xmm, hl .xmm8 (by decide) (by decide) (by decide) l hl',
          hl .xmm9 (by decide) (by decide) (by decide) l hl', hl .xmm10 (by decide) (by decide) (by decide) l hl']
      rw [kp]
      exact h2.1 (Or.inr (by decide)) l hl'
    · rw [ite_t (by decide)] at h2
      rw [ite_t rfl]
      exact ⟨by rw [hl .xmm2 (by decide) (by decide) (by decide) 0 (by decide)]; exact h2.1,
        fun l h1 h4 => by rw [hl .xmm2 (by decide) (by decide) (by decide) l h4]; exact h2.2.1 l h1 h4⟩
  · refine ⟨hE, fun _ k hk l hl => hcp k (by omega) l hl, fun _ k hk l hl => hcp (2 + k) (by omega) l hl, ?_⟩
    rw [ite_f (by omega)]
    exact ⟨fun h l hl => hacc (h.resolve_right (by decide)) l hl, fun hf _ => hy hf⟩

/-! ## The bodies -/

/-- The end of a body of two groups: `add rdx, 512`, `sub r9, 32`. -/
theorem adv2_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 512), .alu .sub .r9 (.imm 32)]) s fun s' =>
      s'.gpr .rdx = s.gpr .rdx + 512 ∧ s'.gpr .r9 = s.gpr .r9 - 32 ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e512 : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e512, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a body of `m` groups, the last of which left `t`: the
invariant, `m` groups on, once `rdx` and `r9` are advanced. -/
theorem seg_fin {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e m : Nat} (hm : 1 ≤ m) (hm3 : m ≤ 3) (he : 16 * (e + m) ≤ nb s₀)
    {s t s' : State} (hI : CInv ix s₀ T e s) (hA : CA ix s₀ (16 * (e + m)) t) (hE : CEnv s₀ T t)
    (hg : t.gpr = s.gpr)
    (hcp : ∀ k < 4, ∀ l < 4, t.zlane (creg k) l = ctb s₀ (16 * (e + m - 1) + 4 * k + l))
    (hy : t.zlane .xmm2 0 =
      yNew48 (padX (3 - m) (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l)) T (fun _ => 0))
    (hy1 : ∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0)
    (frdx : s'.gpr .rdx = t.gpr .rdx + BitVec.ofNat 64 (256 * m))
    (fr9 : s'.gpr .r9 = t.gpr .r9 - BitVec.ofNat 64 (16 * m))
    (fg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = t.gpr r) (fl : ∀ r l, s'.zlane r l = t.zlane r l)
    (fm : s'.mem = t.mem) (frd : s'.rd = t.rd) (fwr : s'.wr = t.wr) :
    CInv ix s₀ T (e + m) s' := by
  have hw := hp.wrap_w
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have ha := hI.rdx
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg]
  refine ⟨hA.gpr2 fg fl fm frd fwr, by omega, ?_, ?_, by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    hE.of_eq (fg _ (by decide) (by decide)) fm frd fwr,
    fun k hk l hl => by rw [fl]; exact hcp k hk l hl, ?_, fun l h1 h4 => by rw [fl]; exact hy1 l h1 h4⟩
  · rw [frdx, hg, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 256 * m) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [fr9, hg, hI.r9, ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  · rw [fl, hy, hT _ (fun _ => 0) (fun _ _ _ => rfl), ghash_pad (hk s₀) (by omega) _ _ hI.y1, hI.y,
      show 48 - 16 * (3 - m) = 16 * m by omega, ← ghash_appendN]
    congr 3
    omega

/-- Three groups: the group in the copies and the first two encrypted are
hashed, the third left in the copies. -/
theorem body48C_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 3) ≤ nb s₀) {s : State} (hI : CInv ix s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (body48C ix) s fun s' => CInv ix s₀ T (e + 3) s' ∧
      s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 64)) ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have ha := hI.rdx
  refine WP.seq (WP.mono (stepC hp (X := padX 0 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := true) (last := false) (g := 0) (by decide)
      (fun h => absurd h (by decide)) (c := 16 * (e + 0)) (j := 4) (by omega)
      (padX_grp (g₀ := 0) (t := 0) rfl h1e _ true (by simp))
      (fun _ l hl => acc48_pad 0 _ _ T hl 0 (by omega))
      hI.a hI.env (fun k hk l hl => by rw [hI.cp k hk l hl]; congr 1; omega)
      (fun h => absurd h (by decide)) (fun _ _ _ => rfl) hCache hI.r8 (by omega))
    fun s₁ ⟨hA₁, hE₁, hg₁, hcp₁, hacc₁, hK₁⟩ => ?_)
  rw [ite_f (by decide)] at hacc₁
  refine WP.seq (WP.mono (stepC hp (X := padX 0 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := false) (last := false) (g := 1) (by decide)
      (fun h => absurd h (by decide)) (c := 16 * (e + 1)) (j := 8) (by omega)
      (padX_grp (g₀ := 0) (t := 1) rfl h1e _ false (by simp))
      (fun h => absurd h (by decide))
      hA₁ hE₁ (fun k hk l hl => by rw [hcp₁ k hk l hl]; congr 1; omega)
      (fun _ => hacc₁) (fun h => absurd h (by decide)) hK₁ (fun hi => by rw [hg₁]; exact hI.r8 hi)
      (by rw [hg₁]; omega))
    fun s₂ ⟨hA₂, hE₂, hg₂, hcp₂, hacc₂, hK₂⟩ => ?_)
  rw [ite_f (by decide)] at hacc₂
  refine WP.seq (WP.mono (stepC hp (X := padX 0 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := false) (last := true) (g := 2) (by decide)
      (fun _ => rfl) (c := 16 * (e + 2)) (j := 12) (by omega)
      (padX_grp (g₀ := 0) (t := 2) rfl h1e _ false (by simp))
      (fun h => absurd h (by decide))
      hA₂ hE₂ (fun k hk l hl => by rw [hcp₂ k hk l hl]; congr 1; omega)
      (fun _ => hacc₂) (fun h => absurd h (by decide)) hK₂ (fun hi => by rw [hg₂, hg₁]; exact hI.r8 hi)
      (by rw [hg₂, hg₁]; omega))
    fun s₃ ⟨hA₃, hE₃, hg₃, hcp₃, hacc₃, hK₃⟩ => ?_)
  rw [ite_t rfl] at hacc₃
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  refine WP.mono (WP.hkeep (by decide) (next48_ok s₃ 64 64 (by decide)))
    fun s' ⟨⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩, hh⟩ => ?_
  have hI' : CInv ix s₀ T (e + 3) s' := seg_fin hp hT (m := 3) (by decide) (by decide) he hI hA₃ hE₃ g₃
    hcp₃ hacc₃.1 hacc₃.2 frdx fr9 fg fl fm frd fwr
  refine ⟨hI', ?_, hK₃.keep hh (hI'.a.keys hp)⟩
  have hr9 : s₃.gpr .r9 - 48 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 2)) := by
    rw [g₃, hI.r9, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  rw [fcf, hr9, toNat_ofNat_lt (by omega)]
  rfl

/-- Two groups: the group in the copies and the first encrypted are hashed,
the second left in the copies. -/
theorem body32C_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 2) ≤ nb s₀) {s : State} (hI : CInv ix s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (body32C ix) s fun s' => CInv ix s₀ T (e + 2) s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have h1e := hI.one
  have ha := hI.rdx
  refine WP.seq (WP.mono (stepC hp (X := padX 1 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := true) (last := false) (g := 1) (by decide)
      (fun h => absurd h (by decide)) (c := 16 * (e + 0)) (j := 4) (by omega)
      (padX_grp (g₀ := 1) (t := 0) rfl h1e _ true (by simp))
      (fun _ l hl => acc48_pad 1 _ _ T hl 2 (by omega))
      hI.a hI.env (fun k hk l hl => by rw [hI.cp k hk l hl]; congr 1; omega)
      (fun h => absurd h (by decide)) (fun _ _ _ => rfl) hCache hI.r8 (by omega))
    fun s₁ ⟨hA₁, hE₁, hg₁, hcp₁, hacc₁, hK₁⟩ => ?_)
  rw [ite_f (by decide)] at hacc₁
  refine WP.seq (WP.mono (stepC hp (X := padX 1 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := false) (last := true) (g := 2) (by decide)
      (fun _ => rfl) (c := 16 * (e + 1)) (j := 8) (by omega)
      (padX_grp (g₀ := 1) (t := 1) rfl h1e _ false (by simp))
      (fun h => absurd h (by decide))
      hA₁ hE₁ (fun k hk l hl => by rw [hcp₁ k hk l hl]; congr 1; omega)
      (fun _ => hacc₁) (fun h => absurd h (by decide)) hK₁ (fun hi => by rw [hg₁]; exact hI.r8 hi)
      (by rw [hg₁]; omega))
    fun s₂ ⟨hA₂, hE₂, hg₂, hcp₂, hacc₂, hK₂⟩ => ?_)
  rw [ite_t rfl] at hacc₂
  refine WP.mono (WP.hkeep (by decide) (adv2_ok s₂)) fun s' ⟨⟨frdx, fr9, fg, fl, fm, frd, fwr⟩, hh⟩ => ?_
  have hI' : CInv ix s₀ T (e + 2) s' := seg_fin hp hT (m := 2) (by decide) (by decide) he hI hA₂ hE₂
    (by rw [hg₂, hg₁]) hcp₂ hacc₂.1 hacc₂.2 frdx fr9 fg fl fm frd fwr
  exact ⟨hI', hK₂.keep hh (hI'.a.keys hp)⟩

/-- One group: the group in the copies is hashed, the one encrypted left in
them. -/
theorem body16C_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : CInv ix s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (body16C ix) s fun s' => CInv ix s₀ T (e + 1) s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have h1e := hI.one
  have ha := hI.rdx
  refine WP.seq (WP.mono (stepC hp (X := padX 2 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l))
      (yl := fun l => s.zlane .xmm2 l) (first := true) (last := true) (g := 2) (by decide)
      (fun _ => rfl) (c := 16 * (e + 0)) (j := 4) (by omega)
      (padX_grp (g₀ := 2) (t := 0) rfl h1e _ true (by simp))
      (fun _ l hl => acc48_pad 2 _ _ T hl 4 (by omega))
      hI.a hI.env (fun k hk l hl => by rw [hI.cp k hk l hl]; congr 1; omega)
      (fun h => absurd h (by decide)) (fun _ _ _ => rfl) hCache hI.r8 (by omega))
    fun s₁ ⟨hA₁, hE₁, hg₁, hcp₁, hacc₁, hK₁⟩ => ?_)
  rw [ite_t rfl] at hacc₁
  refine WP.mono (WP.hkeep (by decide) (adv_ok s₁)) fun s' ⟨⟨frdx, fr9, fg, fl, fm, frd, fwr⟩, hh⟩ => ?_
  have hI' : CInv ix s₀ T (e + 1) s' := seg_fin hp hT (m := 1) (by decide) (by decide) he hI hA₁ hE₁
    hg₁ hcp₁ hacc₁.1 hacc₁.2 frdx fr9 fg fl fm frd fwr
  exact ⟨hI', hK₁.keep hh (hI'.a.keys hp)⟩

/-- The loop of three groups: it stops with fewer than 64 blocks from the
group in the copies. -/
theorem loop48C_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e₀ : Nat} {s : State} (hI : CInv ix s₀ T e₀ s) (h64 : 16 * (e₀ + 3) ≤ nb s₀)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.loop (body48C ix) .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 64 ∧ CInv ix s₀ T e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 3) ≤ nb s₀ ∧ CInv ix s₀ T e s ∧
    VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
  have hstep : ∀ m s, I m s → WP isa (body48C ix) s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 64 ∧ CInv ix s₀ T e s' ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI, hCI⟩
    refine WP.mono (body48C_ok hp hT he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 2) < 64
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, by omega, hI', hCI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega, e + 3, rfl, by omega, hI', hCI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e₀) s ⟨e₀, rfl, h64, hI, hCache⟩

/-! ## Into the copies and out of them -/

theorem CInv.of_eq {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block} {e : Nat} {s s' : State}
    (h : CInv ix s₀ T e s) (hg : s'.gpr = s.gpr) (hl : ∀ r l, s'.zlane r l = s.zlane r l) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CInv ix s₀ T e s' :=
  ⟨h.a.gpr2 (fun r _ _ => by rw [hg]) hl hm hrd hwr, h.one, by rw [hg]; exact h.rdx, by rw [hg]; exact h.r9,
    by rw [hg]; exact h.rax, fun hi => by rw [hg]; exact h.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [hg]; exact h.gpr r h1 h2 h3 h4 h5,
    h.env.of_eq (by rw [hg]) hm hrd hwr, fun k hk l hl' => by rw [hl]; exact h.cp k hk l hl',
    by rw [hl]; exact h.y, fun l h1 h4 => by rw [hl]; exact h.y1 l h1 h4⟩

/-- `cmp r9, n`. -/
theorem cmpC_ok {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block} {e : Nat} {s : State}
    (hI : CInv ix s₀ T e s) (i : BitVec 32) (n : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r9 (.imm i)]) s fun s' =>
      CInv ix s₀ T e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < n)) := by
  have hnb : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.mono (cmp_ok s i n hi) fun s' ⟨hcf, g, l, m, rd, wr⟩ => ⟨hI.of_eq g l m rd wr, ?_⟩
  rw [hcf, hI.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt hn]

/-- The SSE block of the lanes of `enter`'s byte reversals. -/
def revCSse : List Instr :=
  [.xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pshufb .xmm1 .xmm0),
   .xop (.bin .pshufb .xmm12 .xmm0), .xop (.bin .pshufb .xmm15 .xmm0)]

theorem revCSse_ok (u : State) :
    WP isa (.block revCSse) u fun u' =>
      u'.xmm .xmm7 = XBinOp.eval .pshufb (u.xmm .xmm7) (u.xmm .xmm0) ∧
      u'.xmm .xmm1 = XBinOp.eval .pshufb (u.xmm .xmm1) (u.xmm .xmm0) ∧
      u'.xmm .xmm12 = XBinOp.eval .pshufb (u.xmm .xmm12) (u.xmm .xmm0) ∧
      u'.xmm .xmm15 = XBinOp.eval .pshufb (u.xmm .xmm15) (u.xmm .xmm0) ∧
      VG.Proof.Gcm.X86_64.Pclmul.Only [.xmm7, .xmm1, .xmm12, .xmm15] u u' := by
  apply WP.of_runBlock
  simp only [revCSse, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa,
    State.setXmm, Option.some.injEq, exists_eq_left', true_and]
  refine ⟨fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `enter`: the increment in the working space, and output group `e - 1`
in the copies. -/
theorem enter_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block} {e : Nat}
    (h1 : 1 ≤ e) {s : State} (hA : AInvM ix s₀ (16 * e) s)
    (hrdx : (s.gpr .rdx).toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1)) (hr11 : s.gpr .r11 = pp s₀)
    (hv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :
    WP isa (.block enter) s fun s' => CA ix s₀ (16 * e) s' ∧ CEnv s₀ T s' ∧
      (∀ k < 4, ∀ l < 4, s'.zlane (creg k) l = ctb s₀ (16 * (e - 1) + 4 * k + l)) ∧ s'.gpr = s.gpr ∧
      (∀ l < 4, s'.zlane .xmm2 l = s.zlane .xmm2 l) := by
  have hw := hp.wrap_w
  have hwp := hp.wrap_p
  have hle := hA.le
  have e896 : s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int) = pp s₀ + BitVec.ofNat 64 896 := by
    rw [hr11, BitVec.ofInt_natCast]
  have hin896 : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)) 64 := by
    rw [hA.wr, e896]; exact in_sub hp.p_in (by decide)
  have hinD : ∀ o : Nat, o + 64 ≤ 256 →
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (o : Int)) 64 := fun o ho => by
    rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
      show s.gpr .rdx + BitVec.ofNat 64 o = Stitch.wp ix s₀ + BitVec.ofNat 64 (256 * (e - 1) + o) from
        addr_eq (by omega)]
    exact in_rdwr (in_sub hp.w_in (by omega))
  let s₁ := s.setMem (s.mem.writeW (pp s₀ + BitVec.ofNat 64 896) (s.zmm .xmm15))
  let t₁ := StitchZ.ldZ s₁ .xmm7 (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int))
  let t₂ := StitchZ.ldZ t₁ .xmm1 (s.gpr .rdx + BitVec.ofInt 64 ((64 : Nat) : Int))
  let t₃ := StitchZ.ldZ t₂ .xmm12 (s.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int))
  let t₄ := StitchZ.ldZ t₃ .xmm15 (s.gpr .rdx + BitVec.ofInt 64 ((192 : Nat) : Int))
  rw [enter, WP.block_cons_iff]
  refine ⟨s₁, by simp only [incAt, isa, exec, State.store512_eq, ea_at, hin896, ite_true]; rw [e896], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, s₁, State.setMem_gpr, State.setMem_rd, State.setMem_wr,
    hinD 0 (by decide), ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, ea_at, t₁, s₁, StitchZ.ldZ, State.setZ_gpr, State.setZ_rd,
    State.setZ_wr, State.setMem_gpr, State.setMem_rd, State.setMem_wr, hinD 64 (by decide), ite_true,
    Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₃, by simp only [isa, exec, State.load512, ea_at, t₂, t₁, s₁, StitchZ.ldZ, State.setZ_gpr, State.setZ_rd,
    State.setZ_wr, State.setMem_gpr, State.setMem_rd, State.setMem_wr, hinD 128 (by decide), ite_true,
    Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₄, by simp only [isa, exec, State.load512, ea_at, t₃, t₂, t₁, s₁, StitchZ.ldZ, State.setZ_gpr,
    State.setZ_rd, State.setZ_wr, State.setMem_gpr, State.setMem_rd, State.setMem_wr, hinD 192 (by decide), ite_true,
    Option.map_some]; rfl, ?_⟩
  -- What the store and the loads leave.
  have e₄ : t₄.gpr = s.gpr ∧ t₄.mem = s₁.mem ∧ t₄.rd = s.rd ∧ t₄.wr = s.wr := by
    simp only [t₄, t₃, t₂, t₁, s₁, StitchZ.ldZ, State.setZ_gpr, State.setZ_mem, State.setZ_rd, State.setZ_wr,
      State.setMem_gpr, State.setMem_rd, State.setMem_wr, and_self]
  have keep : ∀ r, r ∉ ([.xmm7, .xmm1, .xmm12, .xmm15] : List XReg) → ∀ l < 4, t₄.zlane r l = s.zlane r l :=
    fun r hr l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [t₄, t₃, t₂, t₁]
      rw [StitchZ.ldZ_zlane_ne _ _ hr.2.2.2 hl, StitchZ.ldZ_zlane_ne _ _ hr.2.2.1 hl,
        StitchZ.ldZ_zlane_ne _ _ hr.2.1 hl, StitchZ.ldZ_zlane_ne _ _ hr.1 hl]
      rfl
  have ld : ∀ k < 4, ∀ l < 4, t₄.zlane (creg k) l =
      s₁.mem.readW (s.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun k hk l hl => by
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simp only [t₄, t₃, t₂]
        rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl, StitchZ.ldZ_zlane_ne _ _ (by decide) hl,
          StitchZ.ldZ_zlane_ne _ _ (by decide) hl]
        exact StitchZ.ldZ_zlane s₁ _ _ hl
      · simp only [t₄, t₃]
        rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl, StitchZ.ldZ_zlane_ne _ _ (by decide) hl]
        exact StitchZ.ldZ_zlane t₁ _ _ hl
      · simp only [t₄]
        rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl]
        exact StitchZ.ldZ_zlane t₂ _ _ hl
      · exact StitchZ.ldZ_zlane t₃ _ _ hl
  -- The working space but for the increment, and the data, are as they were.
  have F₁ : Frame [⟨pp s₀ + BitVec.ofNat 64 896, 64⟩] s.mem s₁.mem :=
    (Frame.refl _ s.mem).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have kpw : ∀ o, o + 16 ≤ 896 →
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho =>
    Mem.readW_writeW_sep (Offset.sep (pp s₀) (d := o) (n := 128 / 8) (e := 896) (k := 512 / 8) (by omega) (by omega)
      (by omega)) (by decide)
  have sepW : ∀ k < nb s₀, ∀ r ∈ [(⟨pp s₀ + BitVec.ofNat 64 896, 64⟩ : Region)],
      Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.w_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
  have sepD : ∀ k < nb s₀, ∀ r ∈ [(⟨pp s₀ + BitVec.ofNat 64 896, 64⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.d_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
  refine WP.mono (WP.zlanes (vs := [.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0), .zop (.zbin .vpshufb .xmm1 .xmm1 .xmm0),
      .zop (.zbin .vpshufb .xmm12 .xmm12 .xmm0), .zop (.zbin .vpshufb .xmm15 .xmm15 .xmm0)]) (ss := revCSse) rfl
      fun l _ => revCSse_ok (t₄.zproj l)) fun s' ⟨k', q⟩ => ?_
  have gs : s'.gpr = s.gpr := k'.gpr.trans e₄.1
  have ms : s'.mem = s₁.mem := k'.mem.trans e₄.2.1
  have keep' : ∀ r, r ∉ ([.xmm7, .xmm1, .xmm12, .xmm15] : List XReg) → ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => by
      have := (q l hl).2.2.2.2.xmm r hr
      simp only [State.zproj_xmm] at this
      rw [this, keep r hr l hl]
  refine ⟨⟨hle, fun l hl => by rw [keep' _ (by decide) l hl]; exact hA.ctr l hl,
    fun l hl => by rw [keep' _ (by decide) l hl]; exact hA.msk l hl, fun l hl => ?_, by rw [gs]; exact hr11,
    by rw [gs]; exact hA.rdi, by rw [gs]; exact hA.rsi, by rw [gs]; exact hA.r10, ?_,
    fun k hk => by rw [ms, blockAt_frame F₁ (sepW k (by omega))]; exact hA.out k hk,
    fun k hk hc => by rw [ms, blockAt_frame F₁ (sepD k hk)]; exact hA.src k hk hc,
    by rw [k'.rd, e₄.2.2.1]; exact hA.rd, by rw [k'.wr, e₄.2.2.2]; exact hA.wr⟩,
    ⟨by rw [gs]; exact hr11,
      fun g hg k hk l hl => by rw [ms, kpw _ (by simp only [tab]; omega)]; exact hv g hg k hk l hl,
      fun l hl => by rw [ms, kpw _ (by omega)]; exact hm l hl,
      fun o ho => by
        rw [k'.rd, k'.wr, e₄.2.2.1, e₄.2.2.2, hA.rd, hA.wr]; exact in_rdwr (in_sub_int hp.p_in ho)⟩,
    fun k hk l hl => ?_, gs, fun l hl => keep' _ (by decide) l hl⟩
  · -- The increment, stored.
    rw [ms, show pp s₀ + BitVec.ofNat 64 (896 + 16 * l) = pp s₀ + BitVec.ofNat 64 896 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    show (s.mem.writeW _ _).readW _ 128 = _
    rw [StitchZ.readW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl]
    exact hA.inc l hl
  · rw [ms]
    exact hA.frame.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _
      (Offset.contains_base _ (by decide) (by decide))
  · -- The copies.
    obtain ⟨c0, c1, c2, c3, _⟩ := q l hl
    have h0 : t₄.zlane .xmm0 l = revMask := by rw [keep _ (by decide) l hl]; exact hA.msk l hl
    simp only [State.zproj_xmm, h0] at c0 c1 c2 c3
    have adr : s.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
        Stitch.wAddr ix s₀ (16 * (e - 1) + 4 * k + l) := by
      rw [StitchZ.ofInt_add_ofNat]; exact addr_eq (by omega)
    have fin : XBinOp.eval .pshufb (t₄.zlane (creg k) l) revMask = ctb s₀ (16 * (e - 1) + 4 * k + l) := by
      rw [ld k hk l hl, ← VG.Proof.Gcm.X86_64.blockAt_eq, adr, blockAt_frame F₁ (sepW _ (by omega))]
      exact hA.out _ (by omega)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact c0.trans fin
    · exact c1.trans fin
    · exact c2.trans fin
    · exact c3.trans fin

/-- `leave`: the reduction constant and the increment in their registers. -/
theorem leave_ok {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block}
    {P : Nat → Nat → Block} (hT2 : ∀ k l, T 2 k l = P k l) {e : Nat} {s : State} (hI : CInv ix s₀ T e s) :
    WP isa (.block leave) s fun s' => EInvM ix s₀ P e s' := by
  let q₁ := s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)
  let q₂ := s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)
  let t₁ := StitchZ.ldZ s .xmm1 q₁
  let t₂ := StitchZ.ldZ t₁ .xmm15 q₂
  have hin₁ : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [hI.env.r11]; exact hI.env.inp 832 (by decide)
  have hin₂ : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)) 64 := by
    rw [hI.env.r11]; exact hI.env.inp 896 (by decide)
  rw [leave, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hin₁, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [incAt, isa, exec, State.load512, ea_at, t₁, StitchZ.ldZ, State.setZ_gpr, State.setZ_rd,
    State.setZ_wr, hin₂, ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  have keep : ∀ r, r ≠ .xmm1 → r ≠ .xmm15 → ∀ l < 4, t₂.zlane r l = s.zlane r l := fun r h1 h15 l hl => by
    simp only [t₂, t₁]
    rw [StitchZ.ldZ_zlane_ne _ _ h15 hl, StitchZ.ldZ_zlane_ne _ _ h1 hl]
  have hA := hI.a
  refine ⟨⟨hA.le, fun l hl => by rw [keep _ (by decide) (by decide) l hl]; exact hA.ctr l hl,
    fun l hl => by rw [keep _ (by decide) (by decide) l hl]; exact hA.msk l hl, fun l hl => ?_,
    hA.rdi, hA.rsi, hA.r10, hA.frame, hA.out, hA.src, hA.rd, hA.wr⟩, hI.one, hI.rdx, hI.r9, hI.rax, hI.r8, hI.gpr,
    fun k hk l hl => ?_, fun l hl => ?_, by rw [keep _ (by decide) (by decide) 0 (by decide)]; exact hI.y,
    fun l h1 h4 => by rw [keep _ (by decide) (by decide) l h4]; exact hI.y1 l h1 h4⟩
  · show (StitchZ.ldZ t₁ .xmm15 q₂).zlane .xmm15 l = _
    rw [StitchZ.ldZ_zlane _ _ _ hl, StitchZ.ofInt_add_ofNat, hI.env.r11]
    exact hA.im l hl
  · have := hI.env.pv 2 (by decide) k hk l hl
    rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega] at this
    exact this.trans (hT2 k l)
  · show (StitchZ.ldZ t₁ .xmm15 q₂).zlane .xmm1 l = _
    rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl, StitchZ.ldZ_zlane _ _ _ hl, StitchZ.ofInt_add_ofNat, hI.env.r11]
    exact hI.env.pm l hl

theorem leave_keeps : leave.all Instr.keepsH = true := rfl

/-! ## The groups after the first -/

/-- `bigRestC`, after the powers of 48 blocks are stored (`s₁`): from the
first group encrypted (`s`), every group but the last hashed. -/
theorem bigRestCM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block}
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    {s s₁ : State} (hI : EInvM ix s₀ P 1 s) (hA₁ : AInvM ix s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa (bigRestC ix) s₁ fun s' => ∃ e, EInvM ix s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  have hK : ∀ {e : Nat} {t : State}, CInv ix s₀ T e t → Keys (nr s₀) (sch s₀) t := fun h => h.a.keys hp
  unfold bigRestC
  -- The copies, and whether there are three more groups.
  have hent : WP isa (.block (enter ++ ([.alu .cmp .r9 (.imm 64)] : List Instr))) s₁ fun s' =>
      CInv ix s₀ T 1 s' ∧ s'.cf = some (decide (nb s₀ - 16 * (1 - 1) < 64)) := by
    rw [WP.block_append_iff]
    refine WP.mono (enter_ok hp (T := T) (Nat.le_refl 1) hA₁ (by rw [hg₁]; exact hI.rdx)
      (by rw [hg₁]; exact hr11) hv₁ hm₁) fun s₂ ⟨hA₂, hE₂, hcp₂, hg₂, hl₂⟩ => ?_
    have g₂ : s₂.gpr = s.gpr := hg₂.trans hg₁
    exact cmpC_ok ⟨hA₂, Nat.le_refl 1, by rw [g₂]; exact hI.rdx, by rw [g₂]; exact hI.r9,
      by rw [g₂]; exact hI.rax, fun hi => by rw [g₂]; exact hI.r8 hi,
      fun r h1 h2 h3 h4 h5 => by rw [g₂]; exact hI.gpr r h1 h2 h3 h4 h5, hE₂, hcp₂,
      by rw [hl₂ 0 (by decide), hl₁ 0 (by decide)]; exact hI.y,
      fun l h1 h4 => by rw [hl₂ l h4, hl₁ l h4]; exact hI.y1 l h1 h4⟩ 64 64 (by decide) (by decide)
  refine WP.seq (WP.mono (WP.hkeep (by decide) hent) fun s₃ ⟨⟨hC₃, hcf₃⟩, hh₃⟩ => ?_)
  have hK₃ := hCache.keep hh₃ (hK hC₃)
  -- Three groups at a time.
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 64 ∧ CInv ix s₀ T e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (1 - 1) < 64))
    (by simp only [eval, hcf₃]) (fun h => WP.block_nil ⟨1, by simpa using h, hC₃, hK₃⟩)
    (fun h => loop48C_ok hp hT hC₃ (by simp at h; omega) hK₃)) fun s₄ ⟨e, hex, hC₄, hK₄⟩ => ?_)
  have h1e := hC₄.one
  have hle := hC₄.a.le
  -- Two groups, or one.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmpC_ok hC₄ 48 48 (by decide) (by decide)))
    fun s₅ ⟨⟨hC₅, hcf₅⟩, hh₅⟩ => ?_)
  have hK₅ := hK₄.keep hh₅ (hK hC₅)
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 48 ∧ CInv ix s₀ T e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (e - 1) < 48))
    (by simp only [eval, hcf₅]) (fun h => WP.block_nil ⟨e, by simpa using h, hC₅, hK₅⟩)
    (fun h => WP.mono (body32C_ok hp hT (by simp at h; omega) hC₅ hK₅)
      fun _ ⟨hC, hKK⟩ => ⟨e + 2, by omega, hC, hKK⟩)) fun s₆ ⟨e', hex', hC₆, hK₆⟩ => ?_)
  have h1e' := hC₆.one
  have hle' := hC₆.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmpC_ok hC₆ 32 32 (by decide) (by decide)))
    fun s₇ ⟨⟨hC₇, hcf₇⟩, hh₇⟩ => ?_)
  have hK₇ := hK₆.keep hh₇ (hK hC₇)
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, CInv ix s₀ T e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (e' - 1) < 32))
    (by simp only [eval, hcf₇]) (fun _ => WP.block_nil ⟨e', hC₇, hK₇⟩)
    (fun h => WP.mono (body16C_ok hp hT (by simp at h; omega) hC₇ hK₇)
      fun _ ⟨hC, hKK⟩ => ⟨e' + 1, hC, hKK⟩)) fun s₈ ⟨e'', hC₈, hK₈⟩ => ?_)
  -- The registers as the tail takes them.
  exact WP.mono (WP.hkeep leave_keeps (leave_ok hT2 hC₈))
    fun t ⟨hI', hh⟩ => ⟨e'', hI', hK₈.keep hh (hI'.a.keys hp)⟩

end VG.Proof.Gcm.X86_64.StitchZC
