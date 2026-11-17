module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes

/-! ### `Dsa.Arm.Gen.KSStore`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on ARMv7: numbers out of the key working space

`storeBE L j o n` (`storeBE_vp`): the claim at byte `o` of `scratch` := the
low `n` bytes of array `j`, big-endian.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw wp_dp wp_mul op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {σ : State} {c : Cfg} {s : State}

/-- The pointer to array `j`, from a state of the search. -/
theorem SS.ptr_ok (h : SS G σ c s) {r : Reg} (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = G.KB + BitVec.ofNat 32 (arr G.w j) → Rest [r] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  exact ptr_regs_ok r7 r8 hj h.r7 h.r8 k

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeBE_vp {L j o n : Nat} (cert : Cert7 (storeBE L j o n)) (hL : L = G.pLen) (hj : j ∈ c.live)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (hoK : o + n ≤ sK G.pLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (St G c X) (storeBE L j o n)
      (St G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n) :: cl' } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  have hjN := h.liveOk j hj
  have fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega_using [l]
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega_using [fa, hS])
  have e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have as : State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := gi.saddr (by omega_using [hn0, hoK, big])
  have va := h.arrs.get hj
  unfold storeBE
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok (r := .r1) (j := j) (by decide) (by simp only [nArrs] at hjN; omega_using [hjN]) fun s₁ p₁ R₁ m₁ => ?_)
  refine wp_movw fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have r8₃ : s₃.gpr .r8 = G.KB := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r0) (o := o) r8₃ rfl l (by omega_using [hoK]) fun s₄ v₄ R₄ M₄ => ?_
  refine wp_movw fun s₅ u₅ => WP.block_nil ?_
  have R₅ : Rest [.r0, .r1, .r2, .r12, .lr] s s₅ := (R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((R₄.mono (by simp)).trans (u₅.rest (by simp)))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, M₄, u₃.mem, u₂.mem, m₁]
  have wr₅ : s₅.wr = s.wr := R₅.wr
  have srcFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [big, fit, kb, fa, hS]), BitVec.toNat_ofNat]; omega_using [hnw, big, fit, kb, fa, hS]
  have dstFit : (G.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [hoK, kb]), BitVec.toNat_ofNat]; omega_using [hoK, kb]
  refine WP.mono (VG.Proof.Bignum.Arm.reverseBuffer_ok s₅ (src := G.KB + BitVec.ofNat 32 (arr G.w j)) (dst := G.scr + BitVec.ofNat 32 o)
    (n := n) hn0 srcFit dstFit (by omega_using [hoK, kb])
    ⟨G.rScr, List.mem_append_right _ (by rw [wr₅]; exact inS), by
      rw [ad, e]; exact Offset.contains_base _ (by omega_using [hnw, big, fa, hS]) (by omega_using [big, fit, fa])⟩
    ⟨G.rScr, by rw [wr₅]; exact inS, by rw [as]; exact Offset.contains_base _ (by omega_using [hoK, big]) (by omega_using [hoK, big, fit])⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inr (by omega_using [hoK])) (by omega_using [hnw, big, fa, hS]) (by omega_using [hoK, big]))
    (by rw [u₅.other _ (by decide), v₄])
    (by rw [u₅.other _ (by decide), R₄.gpr _ (by decide), u₃.gpr, dpVal, u₂.gpr, u₂.other _ (by decide), p₁,
      setWidth_ofNat16 (by omega_using [hnw, w96])])
    (by rw [u₅.gpr, setWidth_ofNat16 (by omega_using [hnw, w96])])) ?_
  rintro t ⟨bt, ft, _, rt⟩
  rw [as, ad, m₅, VG.Proof.Rsa.Arm.CrtValues.read_low _ _ (n := G.w) hnw,
    show val32 s.mem (State.addr G.KB) (arr G.w j) G.w = num s.mem G.KB G.w j from rfl, va] at bt
  rw [as, m₅] at ft
  refine ⟨h.of_scr (R₅.trans (rt.mono (by simp))) (o := o) (n := n) hoK (ft.mono (by simp)) fun y hy => ?_, x⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bt, by rw [VG.Proof.Rsa.i2osp_length]; exact hoK⟩
  · exact .inl (hcl y hy)

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.KSSetup`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: the key working space set up

`ksSetup` (`ksSetup_vp`): the count `w` into the division's header (word
16), every array zeroed, and `[aOne] := 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Bignum.Arm (zero_ok ZeroInv)
open VG.Impl.Rsa.Arm.Keys (hdr setOne)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_mul op2_imm op2_reg op2_lsr dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem ksSetup_vp :
    VP (St G c X) ksSetup (St G { c with A := A0, live := allArrs, KV := KU c.KV 16 G.w, kls := [16] } X) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) ksSetup, by kernel_rfl⟩
    (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have l := h.lens
  have nw := hw.nowrap
  have wl : G.w ≤ 96 := by simp only [GP.w]; omega_using [l]
  have w1 : 1 ≤ G.w := by simp only [GP.w]; omega_using [l]
  have fits : hdr + 4 * (nArrs * (G.w + 2)) ≤ kz G.pLen := by
    simp only [hdr, nArrs, kz, GP.w]; omega_using [l]
  refine h.ksWP rfl (P := fun t => Arrs t.mem G.KB G.w A0 allArrs ∧ slot t.mem G.KB 16 = G.w ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs (G.ksState s) t) ?_
    fun t ⟨a, sl, R⟩ hr hw' f => ⟨?_, x⟩
  swap
  · have R' : Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := ⟨R.gpr, hr, hw', R.sp⟩
    have hk : ∀ d ∈ [16], slot t.mem G.KB d = KU c.KV 16 G.w d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd
      rw [KU, VG.Proof.Rsa.Arm.Keys.upd_self]; exact sl
    have hko : ∀ d ∈ [16], KlsOk d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd; decide
    exact h.of_ks R' f a allArrs_lt hk hko
  -- The count, the pointer and the number of words.
  unfold ksSetup
  refine WP.seq (wp_strSlot hw (d := 16) (by decide) fun s₁ u₁ => ?_)
  have hw₁ := hw.of_mupd u₁
  have o₁ := writeW32_outside (G.ksState s).mem (State.addr G.KB) (d := 16) ((G.ksState s).gpr .r9) (by decide)
  rw [← u₁.mem] at o₁
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_mul fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have R₆ : Rest [.r0, .lr, .r3] s₁ s₆ := (u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))
  have m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hw₆ := hw₁.rest R₆
  have p0 : s₆.gpr .r0 = G.KB + BitVec.ofNat 32 hdr := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      dpVal, hw₁.r8]
  have plr : s₆.gpr .lr = BitVec.ofNat 32 (nArrs * (G.w + 2)) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), hw₁.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArrs, S]
    rw [Nat.mod_eq_of_lt (a := 15) (by decide), Nat.mod_eq_of_lt (a := 4 * (G.w + 2)) (by omega_using [wl]),
      Nat.mod_eq_of_lt (a := 15 * (4 * (G.w + 2))) (by omega_using [wl]), Nat.mod_eq_of_lt (a := 15 * (G.w + 2)) (by omega_using [wl])]
    omega_using []
  have p3 : s₆.gpr .r3 = 0 := u₆.gpr
  -- Zero, then 1.
  refine WP.seq (WP.mono (zero_ok s₆ (base := G.KB) (size := kz G.pLen) (o := hdr) (n := nArrs * (G.w + 2))
    ⟨nw, fits, ⟨G.rK, by rw [R₆.wr, u₁.wr]; exact List.mem_singleton_self _, Region.contains_self _ _⟩⟩
    (by simp only [nArrs]; omega_using []) p0 plr p3) fun s₇ z => ?_)
  have hw₇ := hw₆.rest z.rest
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok hw₇ (j := aOne) (by decide) (by decide) fun t w₈ k₈ v₈ R₈ => WP.block_nil ?_
  have zv : ∀ j < nArrs, num s₇.mem G.KB G.w j = 0 := fun j hj => by
    have := VG.Proof.Rsa.KeyWorkspace.val32_zero_part z.value (a := j * (G.w + 2)) (c := G.w) (by
      have := Nat.mul_le_mul_right (G.w + 2) (show j + 1 ≤ nArrs by omega_using [hj])
      rw [Nat.succ_mul] at this; omega_using [this])
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · show num t.mem G.KB G.w j = KU (fun _ => 0) aOne 1 j
    simp only [KU]
    by_cases e : j = aOne
    · subst e; rw [VG.Proof.Rsa.Arm.Keys.upd_self, v₈, zv _ (by decide)]
    · rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ e, k₈.num (by simpa using Ne.symm e) (by simp)
        (hw₇.fit64 (allArrs_lt j hj)), zv _ (allArrs_lt j hj)]
  · rw [k₈.slot (by decide) (by simp)]
    show w32 s₇.mem _ 16 = G.w
    rw [z.outside.w32 (d := 16) (by simp only [hdr]; omega_using []) (by decide), m₆]
    show (s₁.mem.readW (off (State.addr G.KB) 16) 32).toNat = G.w
    rw [u₁.mem, Mem.readW_writeW_self32, show (G.ksState s).gpr .r9 = s.gpr .r9 from rfl, h.r9,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_using [wl])
  · exact (u₁.rest ..).trans (R₆.mono (by simp) |>.trans ((z.rest.mono (by simp)).trans (R₈.mono (by simp))))

end

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: p and `(p − 1) / q`

`pArith` (`pArith_vp`): from X and q in claims, by the division of X by q
in the key working space: `p − 1 = X − X mod 2q` (`pm1_eq`) in array `aPm1`,
`p` in `aP` and big-endian at `sPBE`, `(p − 1) / q` in `aE`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- `X − X mod q`, less `q` for an odd quotient, is `X − X mod 2q`. -/
theorem pm1_eq (x q : Nat) :
    x - x % q - (if x / q % 2 = 0 then 0 else q) = 2 * q * (x / (2 * q)) := by
  have h1 := Nat.mod_add_div x q
  have h2 : x / (2 * q) = x / q / 2 := by rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
  have h3 := Nat.mod_add_div (x / q) 2
  rw [h2]
  generalize x / q / 2 = a at h3 ⊢
  generalize x / q = b at h1 h3 ⊢
  have e : x - x % q = q * b := by omega_arith
  rw [e]
  have e2 : 2 * q * a = 2 * (q * a) := by rw [Nat.mul_assoc]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · simp only [h, ↓reduceIte]
    have : b = 2 * a := by omega_arith
    rw [this, Nat.mul_left_comm, e2]; omega_arith
  · simp only [show ¬ b % 2 = 0 by omega_arith, ↓reduceIte]
    have : b = 2 * a + 1 := by omega_arith
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, e2]; omega_arith

/-- The certificates of `pArith`'s pieces that depend on the geometry. -/
structure PArithCerts (L Lq : Nat) : Prop where
  st : Cert7 (storeBE L aP sPBE L)

theorem pArithCerts_128 : PArithCerts 128 20 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 128 aP sPBE 128), by kernel_rfl⟩⟩

theorem pArithCerts_256 : PArithCerts 256 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 256 aP sPBE 256), by kernel_rfl⟩⟩

theorem pArithCerts_384 : PArithCerts 384 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 384 aP sPBE 384), by kernel_rfl⟩⟩

/-- The candidate p from X and q. -/
abbrev pVal (x q : Nat) : Nat := x + 1 - x % (2 * q)

/-- The arrays after `pArith`. -/
abbrev pA (x q : Nat) : Nat → Nat :=
  KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (pVal x q - 1)) aE ((pVal x q - 1) / q)) aP (pVal x q)

/-- The stage after `pArith`. -/
abbrev pOut (c : Cfg) (G : GP) (x q : Nat) (rest : Claims) : Cfg :=
  { c with
    cl := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest
    A := pA x q
    live := [aP, aE, aPm1, aOne]
    kls := [] }

/-- Simplifies the arrays' values of a stage. -/
macro "arr_simp" : tactic => `(tactic| simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, divCfg, A0, aQt, aRm, aDv, aDt,
  aX, aT, aS, aPm1, aP, aE, aH, aOne, aG, aZero, aTmp, slOdd, Nat.reduceEqDiff, ↓reduceIte])

/-- The arrays after the loads, the division and `p − 1`. -/
abbrev aL (x q : Nat) : Nat → Nat := KU (KU (KU A0 aQt x) aX x) aDv q
abbrev aD (x q : Nat) : Nat → Nat := KU (KU (aL x q) aQt (x / q)) aRm (x % q)
abbrev aM (x q : Nat) : Nat → Nat :=
  KU (KU (KU (fun _ => 0) aOne 1) aQt (x / q)) aPm1 (x - x % q - (if x / q % 2 = 0 then 0 else q))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The stages after the loads, the division and `p − 1`. -/
abbrev cL (c : Cfg) (G : GP) (x q : Nat) : Cfg :=
  { c with A := aL x q, live := [aDv, aX, aQt, aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] }
abbrev cD (c : Cfg) (G : GP) (x q : Nat) : Cfg :=
  { c with A := aD x q, live := [aQt, aRm, aDv, aX, aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] }
abbrev cM (c : Cfg) (x q : Nat) : Cfg := { c with A := aM x q, live := [aPm1, aQt, aOne], kls := [] }

theorem pLoads_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen) :
    VP (St G c X) (VG.Impl.Rsa.Arm.Keys.seqs [ksSetup, loadS G.pLen aQt sX G.pLen, loadS G.pLen aX sX G.pLen,
        loadS G.pLen aDv sQ G.qLen])
      (fun σ s => St G (cL c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb)) X σ s ∧ Top G s.mem aDv) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  refine VP.seq (G := St G { c with A := A0, live := [aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] } X)
    ((ksSetup_vp (G := G) (c := c) (X := X)).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ =>
      ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; rcases hj with rfl | rfl <;> decide, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), x⟩) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aQt), by kernel_rfl⟩ rfl (by decide) (by exact hx) hxl (by omega_arith) (by omega_arith)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aX), by kernel_rfl⟩ rfl (by decide) (by exact hx) hxl (by omega_arith) (by omega_arith)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  exact loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aDv), by kernel_rfl⟩ rfl (by decide) (by exact hqc) hql (by omega_arith) (by omega_arith)

theorem pDivide_vp {x q : Nat} (hpos : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    VP (fun σ s => St G (cL c G x q) X σ s ∧ Top G s.mem aDv)
      (VG.Impl.Rsa.Arm.Keys.seqs [.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt), VG.Impl.Rsa.Arm.Div.code,
        .block (wRegs G.pLen)])
      (St G (cD c G x q) X) := by
  refine VP.seq (divHdr_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt)), by kernel_rfl⟩ (by decide) (by decide) (by decide)
    (by decide) (by simp) (by arr_simp) (by simp)) ?_
  refine VP.seq (div_vp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp; decide) (by arr_simp; exact hpos)) ?_
  refine (wRegs_vp rfl hlq).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩)
    (fun y hy => hy) (fun j hj => ?_) (fun d hd => ⟨hd, rfl⟩), x⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by arr_simp⟩

theorem pPm1_vp {x q : Nat} :
    VP (St G (cD c G x q) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.sub3 aT aX aRm, .block (VG.Impl.Rsa.Arm.Keys.bitOf slOdd aQt),
        VG.Impl.Rsa.Arm.Keys.sel aS aZero aDv slOdd, VG.Impl.Rsa.Arm.Keys.sub3 aPm1 aT aS])
      (St G (cM c x q) X) := by
  refine VP.seq (sub3_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sub3 aT aX aRm), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.bitOf slOdd aQt)), by kernel_rfl⟩ (by simp) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sel aS aZero aDv slOdd), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sub3 aPm1 aT aS), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega_arith)).mono (fun _ _ h => h) fun σ s ⟨h, xx⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simp, by arr_simp⟩

theorem pVal_eq (x q : Nat) : pVal x q = 2 * q * (x / (2 * q)) + 1 := VG.Proof.Dsa.Generation.pReduction_quotient x q

theorem pVal_lt {x q K : Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K) : pVal x q < 2 ^ K := by
  have le : 2 * q * (x / (2 * q)) ≤ x := Nat.mul_div_le x (2 * q)
  have odd : pVal x q % 2 = 1 := VG.Proof.Dsa.Generation.pReduction_odd x q
  have ev : 2 ^ K % 2 = 0 := by
    rw [show K = K - 1 + 1 by omega_arith, Nat.pow_succ]; simp
  rw [pVal_eq] at odd ⊢
  rcases Nat.lt_or_ge (2 * q * (x / (2 * q)) + 1) (2 ^ K) with h | h
  · exact h
  · have : 2 * q * (x / (2 * q)) + 1 = 2 ^ K := by omega_arith
    rw [this] at odd; omega_arith

theorem pTail_vp {x q : Nat} (cert : Cert7 (storeBE G.pLen aP sPBE G.pLen)) (hq : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y) :
    VP (St G (cM c x q) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.copy aP aPm1, .block (VG.Impl.Rsa.Arm.Keys.orOne aP),
        VG.Impl.Rsa.Arm.Keys.copy aE aQt, .block (VG.Impl.Rsa.Arm.Keys.clrLow aE), storeBE G.pLen aP sPBE G.pLen])
      (St G (pOut c G x q rest) X) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega_arith) hx
  have hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x hq, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega_arith
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aP aPm1), by kernel_rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.orOne aP)), by kernel_rfl⟩ (by simp)) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aE aQt), by kernel_rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.clrLow aE)), by kernel_rfl⟩ (by simp)) ?_
  refine (storeBE_vp cert rfl (by simp) (by omega_arith) (by omega_arith) (by simp only [sPBE, sK, sA, wa]; omega_arith)
    (cl' := rest) fun y hy => by exact hrest y hy).mono (fun _ _ h => h) fun σ s ⟨h, xx⟩ =>
      ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine List.mem_cons.mpr (.inl ?_)
      arr_simp
      rw [hP, Nat.mod_eq_of_lt plt]
    · exact List.mem_cons_of_mem _ hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> refine ⟨by simp, ?_⟩ <;> arr_simp
    · exact hP
    · exact hE
    · exact hM

/-- p and `(p − 1) / q` from X and q. -/
theorem pArith_vp {xb qb : List Byte} (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen)
    (hpos : 0 < Spec.Dsa.decodeBE qb) {rest : Claims} (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y) :
    VP (St G c X) (pArith G.pLen G.qLen)
      (St G (pOut c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb) rest) X) := by
  have hxlt : Spec.Dsa.decodeBE xb < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt xb
    rwa [hxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact VP.seq (pLoads_vp hlq hx hxl hqc hql) (VP.seq (pDivide_vp hpos (by omega_arith))
    (VP.seq pPm1_vp (pTail_vp certs.st hpos (by omega_arith) hxlt hrest)))

end

end VG.Proof.Dsa.Arm.Gen
