module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
public import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
meta import VerifiedGarbage.Proof.Dsa.SameTrace
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.CT
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.CT
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Dsa.DomainWidths

/-! ### `Dsa.PPC64LE.PrevalidatedSign.CT`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Sign.CT.Body`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Sign.CT.Pre`, which only this module used -/

section

/-!
# DSA signing on PPC64LE: the body up to the load of `out`

The taint analysis treats memory as secret, so `out`, which `output` loads
from the header's word `hOut`, is secret to it. `spre_ok`: the body up to
that load (`spre`, the body's sequence regrouped there) runs from the state
`checkKey` (or `Prevalidated.setup`) leaves for it and loads `out` into `r12`, with `q_len` in `r6`, in
the Q space; the constant-time proof fixes those registers there.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Impl.MillerRabin.PPC64LE (sel)
open VG.Proof.Bignum (slot)

/-- `output` up to the load of `out` (and `q_len`). -/
def soutPre : Prog isa :=
  .seq (Verify.zeroArr 7) (.seq (.block [.load .d .r22 .r21 hMask]) (.seq (nonZero 6)
    (.seq (.block [.addi .r20 .r22 0]) (.seq (sel 1 9 7) (.seq (sel 2 6 7)
      (.block ([.load .d .r12 .r21 hOut] ++ getQ .r6)))))))

/-- The body up to the load of `out`. -/
def spre : Prog isa :=
  .seq (.block markValid) (.seq gk (.seq rRanges (.seq Verify.qMinus2 (.seq inverseK
    (.seq sValue soutPre)))))

theorem soutPre_ok {s : State} {L : Lay} {key nonce dig out : Addr} {b : Bool} (hL : L.Ok)
    (h : QS s L key nonce dig) (hw : word s.mem L.S hOut = out) (hm : word s.mem L.S hMask = mask b) :
    WP isa soutPre s fun t =>
      (QS t L key nonce dig ∧ QArr L s.mem t.mem ∧ t.gpr .r12 = out ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql) ∧
        Keep outputRegs s t := by
  have hZ := hL.z256
  unfold soutPre
  -- 0 into array 7.
  refine WP.seq (WP.mono (zeroArr_ok h.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (by decide)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  -- The mask into `r22`.
  have hld : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [Q1.regs.r21]; exact Q1.scr.ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega_arith)
  have hw1 : word s₁.mem L.S hMask = mask b := (Body.hMask (qa1.qbody.body hL)).trans hm
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask b ∧ u.mem = s₁.mem)
    (by prun [exec_ld (by decide) hld]; rw [Q1.regs.r21, ← hw1]) (by decide)) fun s₂ ⟨⟨a22, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  -- `r22 &=` the mask of `s ≠ 0`.
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a22)
    fun s₃ ⟨⟨b22, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (by decide)
  generalize (b && decide (arr s₂.mem L.Q 4 6 ≠ 0)) = c at b22
  refine WP.seq (WP.mono (WP.keep [.r20] (Q := fun u => u.gpr .r20 = mask c ∧ u.mem = s₃.mem)
    (by prun [b22, BitVec.add_zero]) (by decide)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (by decide)
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  -- The selections into arrays 1 and 2.
  refine WP.seq (WP.mono (sel_ok Q4.inq.env (b := c) (o := 1) (a := 9) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨_, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (by decide)
  refine WP.seq (WP.mono (sel_ok Q5.inq.env (b := c) (o := 2) (a := 6) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k5.gpr .r20 (by decide)).trans a20)) fun s₆ ⟨⟨_, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (by decide)
  have qa6 : QArr L s.mem s₆.mem := by
    refine qa1.trans ?_
    rw [← hm4]
    exact (QArr.of o5 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
      (QArr.of o6 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  -- `out` into `r12`, `q_len` into `r6`.
  rw [WP.block_append_iff]
  have hld' : InRegions (s₆.rd ++ s₆.wr) (s₆.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [Q6.regs.r21]; exact Q6.scr.ld (show hOut + 8 ≤ L.Z by simp only [hOut]; omega_arith)
  have hwo : word s₆.mem L.S hOut = out := (Body.hOut (qa6.qbody.body hL)).trans hw
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = out ∧ u.mem = s₆.mem)
    (by prun [exec_ld (by decide) hld']; rw [Q6.regs.r21]; exact hwo) (by decide)) fun s₇ ⟨⟨a12, m7⟩, k7⟩ => ?_
  refine WP.mono (getQ_ok (Q6.regs.keep k7) .r6) fun t ⟨⟨a6, m8⟩, k8⟩ => ?_
  have k78 := k7.trans k8
  exact ⟨⟨Q6.step k78 (by decide), by rw [m8, m7]; exact qa6, (k8.gpr .r12 (by decide)).trans a12, a6⟩,
    (K6.trans k78).mono (by decide)⟩

theorem spre_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hw : word s.mem L.S hOut = out) :
    WP isa spre s fun t =>
      (QS t L key nonce dig ∧ Kept L s.mem t.mem ∧ word t.mem L.S hOut = out ∧ t.gpr .r12 = out ∧
        t.gpr .r6 = BitVec.ofNat 64 L.ql) ∧ Keep bodyRegs s t := by
  unfold spre
  exact sprefix_ok hL hK hc hkp hk hn hd hdg hw fun t Qt Kt ht hm _ _ kt =>
    WP.mono (soutPre_ok hL Qt ht hm) fun u ⟨⟨Qu, qau, u12, u6⟩, ku⟩ =>
      ⟨⟨Qu, Kt.trans (Kept.ofBody hL (qau.qbody.body hL)), (Body.hOut (qau.qbody.body hL)).trans ht, u12, u6⟩,
        keep_but21 (kt.trans ku) (by decide) (by decide)⟩

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Sign.CT.Entry`, which only this module used -/

section

/-!
# DSA signing on PPC64LE: constant time of the entry

`sentry_rel`: from two states that satisfy `sContract` with the same public
data (`svdOf`: the layout, the pointers, the digest's length, the key's
public part and `out`), the entry leaks the same trace and leaves both in the
phase `S0` of the checks of the key, with `out` in the header's word `hOut`
(`SG`). The taint analysis treats `scratch`'s address, loaded from the
stack, as secret: the phase `SL1` after the load fixes it.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- Signing's public data: `out` is given. -/
def SG (v : VD) : Prop := v.out.isSome = true

/-- A call's public data. -/
def svdOf (s : State) : VD :=
  ⟨slayOf s, s.gpr .r5, s.gpr .r8, s.gpr .r10, (stackArg s 0).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (3 * (s.gpr .r7).toNat + (s.gpr .r9).toNat),
    3 * (s.gpr .r7).toNat + 2 * (s.gpr .r9).toNat, (s.gpr .r9).toNat, some (s.gpr .r3),
    3 * (s.gpr .r7).toNat + (s.gpr .r9).toNat⟩

/-- On entry. -/
def SC0 (v : VD) (s : State) : Prop := sContract.pre s ∧ svdOf s = v

/-- After the load of `scratch`'s address. -/
def SL1 (v : VD) (s : State) : Prop := s.gpr .r11 = v.L.S

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

theorem pins_SL1 : Pins SL1 [.r11] := by
  intro v s₁ s₂ a b r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [a, b]

/-- The stack's second argument is readable. -/
theorem stack1_in {s : State} (h : sContract.pre s) : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
  obtain ⟨-, hrd, -⟩ := h
  have e1 : stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 := by
    simp only [stackArgAddr]; rw [Offset.add_add]
  exact ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
    simp only [Region.Contains]; rw [e1, Mem.sub_ofNat_toNat _ (by decide)]; decide⟩

theorem sloadS_SL1 {v : VD} {s : State} (h : SC0 v s) :
    WP isa (.block [.addSp .r11 104, .load .d .r11 .r11 0]) s (SL1 v) := by
  obtain ⟨hp, rfl⟩ := h
  exact WP.mono (sloadS_ok s (stack1_in hp)) fun t ⟨⟨a11, _⟩, _⟩ => a11

/-- A buffer of the contract apart from `scratch`. -/
theorem spre_src {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (slayOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm, Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hn, hk, hi])⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega_using [hn]) i (by omega_using [hk, hi])⟩

theorem sfront_S0 {v : VD} {s : State} (h : SC0 v s) :
    WP isa (.block Sign.entry) s fun t => S0 v t ∧ SG v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := slayOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨-, hrd, -, -, -, -, -, -, dKS, dNS, dDS, -, -, -, -, -, -, -, -, hkl, -⟩ := hp
  refine WP.mono (sfront_ok hpre) fun t ⟨⟨hr, scr, r2, hw, _, out⟩, k⟩ => ?_
  have hK : ∀ {u : State} {n : Nat}, n ≤ 3 * (slayOf s).pl + 2 * (slayOf s).ql → u.rd = s.rd → u.wr = s.wr →
      Src u (slayOf s) (s.gpr .r5) n :=
    fun hn hr hw => spre_src (A := s.gpr .r5) (by rw [hrd]; simp) dKS (s.gpr .r6).isLt
      (by simp only [slayOf] at hn ⊢; omega_using [hkl, hn]) hr hw
  have Out : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem :=
    out.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega_using [hZ])
  refine ⟨⟨⟨hL, hr, scr, hK (n := 3 * (slayOf s).pl + (slayOf s).ql) (by omega_using []) k.rd k.wr,
    spre_src (A := s.gpr .r8) (k := (slayOf s).ql) (by rw [hrd]; simp) dNS (s.gpr .r9).isLt
      (Nat.le_refl _) k.rd k.wr,
    spre_src (A := s.gpr .r10) (k := min (stackArg s 0).toNat 64) (by rw [hrd]; simp) dDS (stackArg s 0).isLt
      (Nat.min_le_left _ _) k.rd k.wr,
    ((hK (n := 3 * (slayOf s).pl + (slayOf s).ql) (by omega_using []) rfl rfl).kept Out), hK (Nat.le_refl _) k.rd k.wr,
    (fun o ho => by cases ho; exact hw), (fun _ => ⟨rfl, rfl, rfl⟩), (by simp only [svdOf, slayOf]; omega_using [])⟩,
    r2, fixL_nil t, trivial⟩, rfl⟩

theorem sentry_rel : RelCT isa (Two SC0) (.block Sign.entry) (Two fun v s => S0 v s ∧ SG v) := by
  refine two_post ?_ fun _ _ h => sfront_S0 h
  unfold Sign.entry
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide))
    fun _ _ h => sloadS_SL1 h) (two_taint _ pins_SL1 (by taint_decide)))

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA signing on PPC64LE: constant time after the check of the key

`sbody_rel`: two runs of `Sign.body` from the state the checks of the key
leave (`K9`), for the same signing public data (`SG`), leak the same trace.
The body branches on nothing but the lengths, so the taint analysis checks it
in two segments: up to `output`'s load of `out` from the header's word
`hOut`, which it treats as secret, and after it, from the phase `Mid` in
which both runs hold `out` there (`spre_ok`). `zero_rel`: the same for
`zeroOut`, which loads `out` too, after a key that fails the checks.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- `out`, for signing's public data. -/
def VD.o (v : VD) : Addr := v.out.getD 0

theorem Base.hOut {v : VD} {s : State} (h : Base v s) (hg : SG v) : word s.mem v.L.S hOut = v.o := by
  unfold SG at hg
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hg
  rw [VD.o, ho]
  exact h.hdr o (by rw [ho]; rfl)

/-- The registers the body fixes after the load of `out`. -/
def midL (v : VD) : List (Reg × BitVec 64) :=
  [(.r12, v.o), (.r6, BitVec.ofNat 64 v.L.ql), (.r10, off v.L.Q (slot 4 0)), (.r29, BitVec.ofNat 64 (8 * (4 + 2)))]

/-- After the load of `out`. -/
def Mid : VD → State → Prop := Ph VD.qb fun v s => FixL (midL v) s ∧ True

theorem pins_Mid : Pins Mid (coreRegs ++ ([.r12, .r6, .r10, .r29] : List Reg)) := pins_fixL _ _ fun _ => rfl

/-- What the checks of the key leave: `checkKey_ok`'s `Checked` and `KeyOk`. -/
theorem k9_checked {v : VD} {s : State} (h : K9 v s) (h3 : 3 * v.L.pl + v.L.ql ≤ v.kn) :
    KeyOk s.mem v.L v.key ∧ Checked s s v.L v.key v.sig v.dig v.d := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, p8, q0, qtop⟩, ⟨km, hg⟩, hy⟩ := h
  have bd := km.1.bounds
  have ep : pOf s.mem v.L v.key = v.p := B.p
  have eq : qOf s.mem v.L v.key = v.q := B.q
  have eg : gOf s.mem v.L v.key = v.e (v.L.pl + v.L.ql) := B.g
  have ey : yOf s.mem v.L v.key = v.e (2 * v.L.pl + v.L.ql) := B.y h3
  refine ⟨?_, ⟨ip, B.scr, B.regs, p0.trans ep.symm, ptop, by rw [ep]; exact p8, q0.trans eq.symm, qtop, ?_⟩⟩
  · unfold KeyOk
    rw [ep, eq, eg, ey]
    exact ⟨⟨km.1.1, km.1.2.2, km.1.2.1⟩, ⟨⟨hg.1.1, hg.1.2⟩, hy.1.1, hy.1.2⟩,
      (pmod_iff (by omega_using [bd]) (by omega_using [bd])).mpr km.2, hg.2, hy.2⟩
  · have e : Spec.Dsa.bitLength (qOf s.mem v.L v.key) / 8 = v.qb := by
      rw [eq, VD.q, VG.Proof.Dsa.subgroup_scan_width (p := v.pB) (q := v.qB) km.1.1, Nat.mul_div_cancel_left _
        (by decide)]
      rfl
    rw [e]; exact r2

/-- The body up to the load of `out`, to `Mid`. -/
theorem k9_mid {v : VD} {s : State} (h : K9 v s ∧ SG v) : WP isa spre s (Mid v) := by
  obtain ⟨hk9, sg⟩ := h
  have B := hk9.1
  have r2 := hk9.2.1
  have hL := B.ok
  obtain ⟨ekl, esl, ekn⟩ := B.sgn sg
  obtain ⟨hK, hc⟩ := k9_checked hk9 (Nat.le_of_eq ekn.symm)
  have hx : Src s v.L v.key (3 * v.L.pl + 2 * v.L.ql) := by rw [← ekl]; exact B.hx
  have hn : Src s v.L v.sig v.L.ql := by rw [← esl]; exact B.hsg
  have hd : v.d < 2 ^ 16 := by have := Nat.min_le_right v.dl 64; simp only [VD.d] at this ⊢; omega_using []
  refine WP.mono (spre_ok hL hK hc (Kept.refl _ _) hx hn hd B.hdg (B.hOut sg))
    fun t ⟨⟨Qt, Kt, ht, t12, t6⟩, kt⟩ => ?_
  refine ⟨⟨hL, Qt.regs, Qt.scr, B.hk.keep kt.rd kt.wr, B.hsg.keep kt.rd kt.wr, B.hdg.keep kt.rd kt.wr,
    (B.hk.kept Kt.out).trans B.kb, B.hx.keep kt.rd kt.wr, fun o ho => ?_, B.sgn, B.kn⟩,
    (kt.gpr .r2 (by decide)).trans r2, ?_, trivial⟩
  · rw [ht]
    have := B.hdr o ho
    rw [← this, B.hOut sg]
  · simp only [FixL, midL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨t12, t6, Qt.inq.env.h10, Qt.inq.env.h29⟩

/-- The body starts in the P space the checks of the key leave. -/
theorem pins_K9 : Pins (fun v s => K9 v s ∧ SG v) (coreRegs ++ envRegs') := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (pins_fixL _ _ fun _ => rfl : Pins K9 (coreRegs ++ [])) v s₁ s₂ h₁.1 h₂.1 r
      (List.mem_append_left _ hr)
  · rw [show envRegs' = (envP v).map Prod.fst from rfl] at hr
    obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
    rw [envP_of h₁.1.2.2.2.1.1 p hm, envP_of h₂.1.2.2.2.1.1 p hm]

theorem sbody_rel : RelCT isa (Two fun v s => K9 v s ∧ SG v) Sign.body (Two End) := by
  refine rel_end ?_ (fun _ _ h => h.1.1.regs.r21) (by rw [← Code.allInstrs_eq]; decide +kernel)
  unfold Sign.body Sign.output
  iterate 12 refine RelCT.assoc ?_
  refine RelCT.seq (two_post (two_taintR _ pins_K9 (by taint_decide_rel))
    fun _ _ h => ?_) (two_taint _ pins_Mid (by taint_decide))
  iterate 11 refine WP.assoc' ?_
  exact k9_mid h

/-! ## A key that fails the checks -/

/-- `out` and its length doubled, to zero `out`. -/
def zL (v : VD) : List (Reg × BitVec 64) :=
  [(.r16, v.o), (.r17, BitVec.ofNat 64 (2 * v.L.ql)), (.r21, v.L.S)]

theorem pins_zL : Pins (fun v s => FixL (zL v) s) [.r16, .r17, .r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [show [Reg.r16, .r17, .r21] = (zL v).map Prod.fst from rfl] at hr
  obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
  rw [h₁ p hm, h₂ p hm]

theorem pins_r21 {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) : Pins Φ [.r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [(h v _ h₁).regs.r21, (h v _ h₂).regs.r21]

theorem zfront_ok {v : VD} {s : State} (h : Base v s) (sg : SG v) :
    WP isa (.block (([.load .d .r16 .r21 hOut] : List Instr) ++ getQ .r17 ++
        ([.add .r17 .r17 .r17, .li .r0 0] : List Instr))) s
      fun t => FixL (zL v) t := by
  have hZ := h.ok.z256
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [h.regs.r21]; exact h.scr.ld (show hOut + 8 ≤ v.L.Z by simp only [hOut]; omega_using [hZ])
  refine WP.mono (WP.keep [.r16] (Q := fun u => u.gpr .r16 = v.o ∧ u.mem = s.mem)
    (by prun [exec_ld (by decide) hld]; rw [h.regs.r21]; exact h.hOut sg) (by decide)) fun s₁ ⟨⟨a16, _⟩, k1⟩ => ?_
  refine WP.mono (getQ_ok (h.regs.keep k1) .r17) fun s₂ ⟨⟨a17, _⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r0, .r17] (Q := fun u => u.gpr .r16 = v.o ∧
      u.gpr .r17 = BitVec.ofNat 64 (2 * v.L.ql)) (by
      prun [a17, (k2.gpr .r16 (by decide)).trans a16]
      rw [BitVec.ofNat_add_ofNat, Nat.two_mul]) (by decide)) fun t ⟨⟨b16, b17⟩, k3⟩ => ?_
  simp only [FixL, zL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨b16, b17, (((k1.trans k2).trans k3).gpr .r21 (by decide)).trans h.regs.r21⟩

theorem zero_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s ∧ SG v) :
    RelCT isa (Two Φ) Sign.zeroOut (Two End) := by
  refine rel_end ?_ (fun v s hs => (h v s hs).1.regs.r21) (by decide)
  unfold Sign.zeroOut
  exact RelCT.seq (two_post (two_taint _ (pins_r21 fun v s hs => (h v s hs).1) (by taint_decide))
    fun v s hs => zfront_ok (h v s hs).1 (h v s hs).2) (two_taint _ pins_zL (by taint_decide))

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA prevalidated signing on PPC64LE: constant time

`psign_ct`: two runs from states that satisfy `spContract` and agree on its
public data (`sContract`'s: the arguments' registers, the stack's arguments,
the key's public part and the result) leak the same trace. The entry is
signing's (`sentry_rel`); the public data name a key whose public part
passes validation (`KV`), since the whole key passes private-key validation
(`validatePrivate_spec`). The setup of the working spaces is prevalidated
verification's (`sizes_rel`, then `setupQ` and `setupP` as in
`setupV_rel`), the signing `sbody_rel`, and the sizes' failure, which the
precondition rules out, the zeroing of `out` (`zero_rel`); each branch
depends only on the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- On entry. -/
def SP0 (v : VD) (s : State) : Prop := spContract.pre s ∧ svdOf s = v

/-- A key that passes private-key validation names public data whose key
passes public-key validation. -/
theorem kv_of_pre {s : State} (h : spContract.pre s) : KV (svdOf s) := by
  obtain ⟨hp, hval⟩ := h
  have hv := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP : PrivOk s.mem (slayOf s) (s.gpr .r5) := by
    have e := validatePrivate_spec (m := s.mem) (L := slayOf s) (key := s.gpr .r5) hv
    rw [show 3 * (slayOf s).pl + 2 * (slayOf s).ql = (s.gpr .r6).toNat from hkl.symm] at e
    exact of_decide_eq_true (e.symm.trans hval)
  refine ⟨by simp only [svdOf, slayOf], ?_⟩
  show Spec.Dsa.validatePublicKeyBytes (slayOf s).pl (slayOf s).ql
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql)) = true
  rw [validate_spec hv]
  exact decide_eq_true hP.1

theorem psentry_rel : RelCT isa (Two SP0) (.block Sign.entry) (Two fun v s => S0 v s ∧ (SG v ∧ KV v)) :=
  two_post (sentry_rel.mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ => trivial)
    fun v s h => (sfront_S0 ⟨h.1.1, h.2⟩).mono fun _ ht => ⟨ht.1, ht.2, by rw [← h.2]; exact kv_of_pre h.1⟩

theorem w_PVS {v : VD} {s : State} (h : LQ v s ∧ (SG v ∧ KV v)) :
    WP isa setupP s fun t => PP KM v t ∧ (SG v ∧ KV v) := by
  obtain ⟨⟨B, r2, -, qf⟩, g⟩ := h
  exact (w_setupP (K := KM) (fun _ h => h.1) B r2 qf (B.pk g.2).1.1).mono fun _ ht => ⟨ht, g⟩

theorem setupS_rel :
    RelCT isa (Two fun v s => S0 v s ∧ (SG v ∧ KV v)) (Prevalidated.setup Sign.body Sign.zeroOut) (Two End) := by
  unfold Prevalidated.setup
  refine sizes_rel ?_ fun _ h => zero_rel fun v s h' => ⟨(h v s h').1, (h v s h').2.1⟩
  refine RelCT.seq (two_postG (rel_pins pins_S5' tQ) fun _ _ h => w_LQ h)
    (RelCT.seq (two_post (setupP_rel (pins_and pins_LQ)
      fun _ _ ⟨⟨B, r2, _, _⟩, g⟩ => ⟨B, r2, (B.pk g.2).1.1.1.2.1⟩) fun _ _ h => w_PVS h) ?_)
  exact sbody_rel.mono (fun _ _ => two_mono fun _ s ⟨⟨B, r2, _, pf, _⟩, sg, kv⟩ =>
    ⟨⟨B, r2, fixL_nil s, pf, B.pk kv⟩, sg⟩) fun _ _ h => h

theorem psign_rel : RelCT isa (Two SP0) PrevalidatedSign.sign fun _ _ => True := by
  unfold PrevalidatedSign.sign
  exact RelCT.seq psentry_rel (RelCT.seq setupS_rel (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `svdOf`. -/
theorem svdOf_eq {s t : State} (hs : sContract.pre s) (hp : sContract.pub s t) : svdOf s = svdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, hl⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkl, -⟩ := hs
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h5, ← h6, ← h7, ← h9, Nat.min_eq_right (by omega_using [hkl])] at e
  simp only [svdOf, slayOf, ← h3, ← h5, ← h7, ← h8, ← h9, ← h10, ← a0, ← a1, ← a2, e]

theorem psign_ct : ConstantTime isa spContract.pre spContract.pub PrevalidatedSign.sign :=
  RelCT.constantTime (psign_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨svdOf s, ⟨hs, rfl⟩, ⟨ht, (svdOf_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Random.CT`, which this module and modules that import it used -/

section

/-!
# DSA sampling on PPC64LE: constant time

Two runs of the sampler with the same public data `E` (q's significant
octets, the tape's place and length, the frame), from the same count of
octets consumed and draws left, and with the same trace of
`Random.sample` from there, leak the same trace (`sample_st`). The taint
analysis checks each piece from the registers both runs agree on
(`st_taint`): the tape's length, the octets consumed and the width decide
the short test and the draw's addresses; the candidate's acceptance, which
the taint analysis sees secret, is the head of the sampling trace
(`acc_iff`), and so are the loop's decisions (`step_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

/-- Two states agree on the registers `rs`. -/
def EqRegs (s₁ s₂ : State) : List Reg → Prop
  | [] => True
  | [r] => s₁.gpr r = s₂.gpr r
  | r :: rs => s₁.gpr r = s₂.gpr r ∧ EqRegs s₁ s₂ rs

theorem EqRegs.mem {s₁ s₂ : State} : ∀ {rs : List Reg}, EqRegs s₁ s₂ rs → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  | [], _, _, hr => absurd hr List.not_mem_nil
  | [_], h, _, hr => by rw [List.mem_singleton.mp hr]; exact h
  | _ :: _ :: _, h, _, hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1
    · exact EqRegs.mem h.2 _ hr

theorem EqRegs.single {s₁ s₂ : State} {r : Reg} (h : s₁.gpr r = s₂.gpr r) : EqRegs s₁ s₂ [r] := h

/-- Code the taint analysis checks from the registers `rs`, which two
states with the same stack pointer agree on, leaks the same trace. -/
theorem st_taint {c : Prog isa} (rs : List Reg) {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (hr : EqRegs s₁ s₂ rs) {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) c hc).isSome = true) : SameTrace isa c s₁ s₂ :=
  SameTrace.of_relCT (RelCT.taint (A := taint) (P := fun a b => a = s₁ ∧ b = s₂) (ofRegs rs)
    (fun _ _ ⟨e₁, e₂⟩ => by
      subst e₁ e₂
      exact ⟨hsp, fun r hm => hr.mem r (RegSet.mem_ofList.mp hm)⟩) h) ⟨rfl, rfl⟩

/-- `RelCT` from the traces of the runs from each related pair, and what
each run satisfies. -/
theorem relCT_of {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → SameTrace isa c s₁ s₂ ∧ ∃ F₁ F₂ : State → Prop, WP isa c s₁ F₁ ∧ WP isa c s₂ F₂ ∧
      ∀ t₁ t₂, F₁ t₁ → F₂ t₂ → Q t₁ t₂) : RelCT isa P c Q := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ hp e₁ e₂
  obtain ⟨hs, F₁, F₂, ⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩, hq⟩ := h _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨hs _ _ _ _ e₁ e₂, hq _ _ g₁ g₂⟩

/-- A loop whose iterations, from related states, leak the same trace and
agree on the condition. -/
theorem st_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n s₁ s₂, I n s₁ s₂ → SameTrace isa body s₁ s₂ ∧ ∃ F₁ F₂ : State → Prop,
      WP isa body s₁ F₁ ∧ WP isa body s₂ F₂ ∧ ∀ t₁ t₂, F₁ t₁ → F₂ t₂ →
        isa.eval c t₁ = isa.eval c t₂ ∧ (isa.eval c t₁ = some true → ∃ m < n, I m t₁ t₂))
    {n : Nat} {s₁ s₂ : State} (h : I n s₁ s₂) : SameTrace isa (.loop body c) s₁ s₂ :=
  SameTrace.of_relCT (RelCT.loop (Q := fun _ _ => True) I (fun n => relCT_of fun s₁ s₂ hi => by
    obtain ⟨hs, F₁, F₂, w₁, w₂, hq⟩ := hstep n s₁ s₂ hi
    exact ⟨hs, F₁, F₂, w₁, w₂, fun t₁ t₂ f₁ f₂ => ⟨(hq t₁ t₂ f₁ f₂).1, fun _ => trivial, (hq t₁ t₂ f₁ f₂).2⟩⟩) n) h

/-- A run of `.seq c d` is one of `c`, which keeps the stack pointer. -/
theorem WP.of_seq {c d : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c d) s Q) :
    WP isa c s fun t => t.sp = s.sp := by
  obtain ⟨_, _, e, _⟩ := h
  cases e with
  | seq a _ => exact ⟨_, _, a, VG.PPC64LE.Exec.sp a⟩

/-- A draw at `u` of a tape with `W` octets left is accepted exactly when the
sampling trace from there starts with an acceptance. -/
theorem acc_iff {E : SE} {qb R : List Byte} {u d : Nat} (hQ : E.Q qb) (hR : R.length = E.rl)
    (hs : u + E.W ≤ E.rl) (hd : 1 ≤ d) :
    acc qb R u E.W ↔ (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 1 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega_using [hd]⟩
  have hs' : drawBytes (Spec.Dsa.decodeBE qb) ≤ (R.drop u).length := by
    rw [List.length_drop, hR, hQ.draw]; omega_using [hs]
  by_cases ha : acc qb R u E.W
  · have hS := Dsa.Random.sample_accept _ d' _ hQ.gt hs' (by rw [hQ.draw]; exact ha)
    rw [hS]
    exact iff_of_true ha rfl
  · have hS := Dsa.Random.sample_reject _ d' _ hQ.gt hs' (by rw [hQ.draw]; exact ha)
    rw [hS]
    exact iff_of_false ha (by simp)

/-- Two draws with the same public data, from the same octets consumed `u`
and draws left `d`, and the same sampling trace from there, leak the same
trace. -/
theorem draw_st {E : SE} {qb R₁ R₂ : List Byte} {s₁ s₂ : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a25 : s₁.gpr .r25 = BitVec.ofNat 64 u)
    (b25 : s₂.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) (a17 : s₁.gpr .r17 = BitVec.ofNat 64 d)
    (b17 : s₂.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d)
    (ht : (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace) :
    SameTrace isa draw s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := h₁.sp.trans h₂.sp.symm
  unfold draw
  refine SameTrace.seq (st_taint [.r24, .r25, .r28] hsp ⟨h₁.r24.trans h₂.r24.symm, a25.trans b25.symm,
      h₁.r28.trans h₂.r28.symm⟩ (by taint_decide)) (shortTest_ok hE h₁ a25 hu) (shortTest_ok hE h₂ b25 hu)
    fun t₁ t₂ ⟨⟨c3, m1⟩, k1⟩ ⟨⟨d3, m2⟩, k2⟩ => ?_
  have g1 : SEnv E R₁ t₁ := h₁.step hE k1 (o := 0) (n := 0) (by omega_using []) (by rw [m1]; exact Outside.refl _ _ _ _)
  have g2 : SEnv E R₂ t₂ := h₂.step hE k2 (o := 0) (n := 0) (by omega_using []) (by rw [m2]; exact Outside.refl _ _ _ _)
  have tsp : t₁.sp = t₂.sp := g1.sp.trans g2.sp.symm
  refine SameTrace.ite (by rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero, c3, d3])
    (fun _ => by exact st_taint [] tsp trivial (by taint_decide)) (fun hs => ?_)
  have hs' : ¬ E.rl - u < E.W := fun hc => by
    rw [VG.PPC64LE.eval_nonzero, c3, ite_eq_left hc] at hs
    exact absurd hs (by decide)
  have t25 : t₁.gpr .r25 = BitVec.ofNat 64 u := (k1.gpr .r25 (by decide)).trans a25
  have u25 : t₂.gpr .r25 = BitVec.ofNat 64 u := (k2.gpr .r25 (by decide)).trans b25
  refine SameTrace.seq (st_taint [.r21, .r23, .r25, .r27, .r28] tsp ⟨g1.r21.trans g2.r21.symm,
      g1.r23.trans g2.r23.symm, t25.trans u25.symm, g1.r27.trans g2.r27.symm, g1.r28.trans g2.r28.symm⟩
      (by taint_decide)) (copyRange_ok hE hQ g1 t25 (by omega_using [hu, hs'])) (copyRange_ok hE hQ g2 u25 (by omega_using [hu, hs']))
    fun x₁ x₂ ⟨⟨e1, _, _, x6, _⟩, kx1⟩ ⟨⟨e2, _, _, y6, _⟩, kx2⟩ => ?_
  have hacc : acc qb R₁ u E.W ↔ acc qb R₂ u E.W := by
    rw [acc_iff hQ h₁.R_length (by omega_using [hu, hs']) hd, acc_iff hQ h₂.R_length (by omega_using [hu, hs']) hd, ht]
  have xsp : x₁.sp = x₂.sp := e1.sp.trans e2.sp.symm
  have e17 : EqRegs x₁ x₂ [.r17] := ((kx1.gpr .r17 (by decide)).trans ((k1.gpr .r17 (by decide)).trans a17)).trans
    ((kx2.gpr .r17 (by decide)).trans ((k2.gpr .r17 (by decide)).trans b17)).symm
  unfold drawFinish
  refine SameTrace.ite (by rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero, x6, y6]; simp only [hacc])
    (fun _ => by exact st_taint [] xsp trivial (by taint_decide)) (fun _ => by exact st_taint [.r17] xsp e17 (by taint_decide))

/-- A draw and the loop's test, against `Random.sample`: it goes on, with a
draw fewer, after a rejection that leaves draws, or it ends. -/
theorem step_ok {E : SE} {qb R : List Byte} {s : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (h17 : s.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d) (hd' : d ≤ 128) (h31 : s.gpr .r31 = BitVec.ofNat 64 4) :
    WP isa (.seq draw (.block [.subi .r3 .r31 4])) s fun t =>
      SEnv E R t ∧
        ((isa.eval (.zero .d .r3) t = some true ∧ t.gpr .r17 = BitVec.ofNat 64 (d - 1) ∧
            t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧ t.gpr .r31 = BitVec.ofNat 64 4 ∧ 2 ≤ d ∧
            u + E.W ≤ E.rl ∧
            sample (Spec.Dsa.decodeBE qb) d (R.drop u) =
              rejectOf E.W (sample (Spec.Dsa.decodeBE qb) (d - 1) (R.drop (u + E.W)))) ∨
          (isa.eval (.zero .d .r3) t = some false ∧
            ((sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 0 → d = 1))) := by
  refine WP.seq (WP.mono (draw_ok hE hQ h h25 hu h17 hd hd' h31) fun t₁ ⟨h1, _, _, hc⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 4) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.step hE k2 (o := 0) (n := 0) (by omega_using []) (by rw [m2]; exact Outside.refl _ _ _ _)
  refine ⟨h2, ?_⟩
  rcases hc with ⟨b31, h2d, b17, b25, hu', hrej⟩ | ⟨b31, -, -, hh⟩
  · refine .inl ⟨?_, (k2.gpr .r17 (by decide)).trans b17, (k2.gpr .r25 (by decide)).trans b25,
      (k2.gpr .r31 (by decide)).trans b31, h2d, hu', hrej⟩
    rw [VG.PPC64LE.eval_zero, a3, b31]; rfl
  · refine .inr ⟨?_, hh⟩
    rw [VG.PPC64LE.eval_zero, a3, b31, status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) d (R.drop u)); omega_using [this])]

/-- The sampling loop's two runs, with `d` draws left. -/
def DI (E : SE) (qb R₁ R₂ : List Byte) (d : Nat) (s₁ s₂ : State) : Prop :=
  ∃ u, 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R₁ s₁ ∧ SEnv E R₂ s₂ ∧ s₁.gpr .r25 = BitVec.ofNat 64 u ∧
    s₂.gpr .r25 = BitVec.ofNat 64 u ∧ u ≤ E.rl ∧ s₁.gpr .r17 = BitVec.ofNat 64 d ∧
    s₂.gpr .r17 = BitVec.ofNat 64 d ∧ s₁.gpr .r31 = BitVec.ofNat 64 4 ∧ s₂.gpr .r31 = BitVec.ofNat 64 4 ∧
    (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace

theorem sampleLoop_st {E : SE} {qb R₁ R₂ : List Byte} (hE : E.Ok) (hQ : E.Q qb) {d : Nat} {s₁ s₂ : State}
    (h : DI E qb R₁ R₂ d s₁ s₂) :
    SameTrace isa (.loop (.seq draw (.block [.subi .r3 .r31 4])) (.zero .d .r3)) s₁ s₂ := by
  refine st_loop (DI E qb R₁ R₂) (fun n s₁ s₂ ⟨u, hd, hd', h₁, h₂, a25, b25, hu, a17, b17, a31, b31, ht⟩ => ?_) h
  refine ⟨SameTrace.seq (draw_st hE hQ h₁ h₂ a25 b25 hu a17 b17 hd ht)
    (draw_ok hE hQ h₁ a25 hu a17 hd hd' a31) (draw_ok hE hQ h₂ b25 hu b17 hd hd' b31)
    fun t₁ t₂ ⟨e₁, _⟩ ⟨e₂, _⟩ => by exact st_taint [] (e₁.sp.trans e₂.sp.symm) trivial (by taint_decide), _, _,
    step_ok hE hQ h₁ a25 hu a17 hd hd' a31, step_ok hE hQ h₂ b25 hu b17 hd hd' b31,
    fun t₁ t₂ ⟨e₁, c₁⟩ ⟨e₂, c₂⟩ => ?_⟩
  rcases c₁ with ⟨v₁, x17, x25, x31, hn, hu', hr₁⟩ | ⟨v₁, hh₁⟩ <;>
    rcases c₂ with ⟨v₂, y17, y25, y31, hn₂, -, hr₂⟩ | ⟨v₂, hh₂⟩
  · refine ⟨v₁.trans v₂.symm, fun _ => ⟨n - 1, by omega_using [hd], u + E.W, by omega_using [hn], by omega_using [hd'], e₁, e₂, x25, y25, hu',
      x17, y17, x31, y31, ?_⟩⟩
    rw [hr₁, hr₂] at ht
    exact (List.cons.inj ht).2
  · rw [hr₁] at ht
    have := hh₂ (by rw [← ht]; rfl)
    omega
  · rw [hr₂] at ht
    have := hh₁ (by rw [ht]; rfl)
    have := hd'
    omega
  · exact ⟨v₁.trans v₂.symm, fun hc => by rw [v₁] at hc; cases hc⟩

/-- `sample` from the same public data, octets consumed and sampling trace. -/
theorem sample_st {E : SE} {qb R₁ R₂ : List Byte} {s₁ s₂ : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a25 : s₁.gpr .r25 = BitVec.ofNat 64 u)
    (b25 : s₂.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (ht : (sample (Spec.Dsa.decodeBE qb) 128 (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) 128 (R₂.drop u)).trace) :
    SameTrace isa Impl.Dsa.PPC64LE.Random.sample s₁ s₂ := by
  have W : ∀ {s : State}, WP isa (.block [.li .r17 128, .li .r31 4]) s fun t =>
      (t.mem = s.mem ∧ t.gpr .r17 = BitVec.ofNat 64 128 ∧ t.gpr .r31 = BitVec.ofNat 64 4) ∧
        Keep [.r17, .r31] s t := fun {s} => WP.keep [.r17, .r31] (by prun) (by decide)
  unfold Impl.Dsa.PPC64LE.Random.sample
  refine SameTrace.seq (st_taint [] (h₁.sp.trans h₂.sp.symm) trivial (by taint_decide)) W W
    fun t₁ t₂ ⟨⟨m1, a17, a31⟩, k1⟩ ⟨⟨m2, b17, b31⟩, k2⟩ => sampleLoop_st hE hQ ⟨u, by decide, by decide,
      h₁.step hE k1 (o := 0) (n := 0) (by omega_using []) (by rw [m1]; exact Outside.refl _ _ _ _),
      h₂.step hE k2 (o := 0) (n := 0) (by omega_using []) (by rw [m2]; exact Outside.refl _ _ _ _),
      (k1.gpr _ (by decide)).trans a25, (k2.gpr _ (by decide)).trans b25, hu, a17, b17, a31, b31, ht⟩

end VG.Proof.Dsa.PPC64LE.Rnd

end

end

/-! ### `Dsa.PPC64LE.RandomSign.Fn`, which this module and modules that import it used -/

section

/-!
# Randomized DSA signing on PPC64LE: the function

`randomSign_correct`: `vg_dsa_sign_random_prevalidated` meets `rsContract`. In its frame,
the entry (`entry_ok`), the scan of q (`prepareQ_ok`), the attempts
(`attempts_ok`, or none when `q ≤ 1`) and the exit (`finish_ok`) follow one
another; the result is `randomSignBytes`'s (`rsRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

theorem attempts_ok {s₀ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) :
    ∀ a u t, AttInv s₀ a u t → WP isa attempts t (AttOut s₀) := by
  intro a u t hi
  unfold attempts
  refine WP.loop (M := isa) (fun n (t : State) => ∃ u, AttInv s₀ n u t) (fun n t ⟨u, hi⟩ =>
    WP.mono (attempt_ok h hq hi) fun t' ⟨e, ho, hc⟩ => ?_) a t ⟨u, hi⟩
  by_cases h4 : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u n = 4
  · obtain ⟨hn, hi'⟩ := hc h4
    exact .inr ⟨by rw [e, decide_eq_true h4], n - 1, by omega_using [hn], _, hi'⟩
  · exact .inl ⟨by rw [e, decide_eq_false h4], ho h4⟩

/-- The specification's result is the attempts'. -/
theorem rsRes_eq {s₀ : State} (h : rsContract.pre s₀) : rsRes s₀ = resOf s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    lv, -, hkl, -⟩ := h
  simp only [rsRes, resOf, randomSignRemaining, inpOf, randOf, Spec.Dsa.randomSignBytes, List.drop_zero]
  rw [ite_eq_right (by
    simp only [decide_eq_true lv, Bool.not_true, VG.Proof.Bignum.bytesAt_length, hkl, Bool.false_or,
      bne_self_eq_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [rlOf, RL.kl, hkl]

theorem ctx_012 : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r12] : List Reg) := by decide

theorem ctx_z : ∀ r ∈ ctxRegs, r ∉ (([.r0, .r16, .r17] : List Reg) ++ ([.r16, .r17] : List Reg)) := by decide

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  r3 : t.gpr .r3 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
    R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)
  used : t.mem.readW (rlOf s₀).used 64 = BitVec.ofNat 64 R.used
  nv : ∀ i < 18, t.gpr (nv i) = s₀.gpr (nv i)
  r2 : t.gpr .r2 = s₀.gpr .r2
  lr : t.lr = s₀.lr
  sp : t.sp = (rlOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.RandomSignResult} (h : rsContract.pre s₀)
    (hc : Ctx (rlOf s₀) s₀ t) (h25 : t.gpr .r25 = BitVec.ofNat 64 R.used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0))
    (hnone : R.status ≠ 1 → R.signature = none) :
    WP isa (finish [.add .r17 .r21 .r21]) t (Fin s₀ R) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (WP.keep (c := .block [.subi .r3 .r31 1]) [.r3] (Q := fun t₁ => t₁.mem = t.mem ∧
    t₁.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₁ ⟨⟨m1, a3⟩, k1⟩ => ?_)
  have hc₁ : Ctx (rlOf s₀) s₀ t₁ := hc.step hL k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr))
    (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (rlOf s₀) s₀ t₂ → Keep [.r0, .r3, .r16, .r17] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0) → P t₂) →
      WP isa (.ite (.zero .d .r3) (.block []) (zeroOut [.add .r17 .r21 .r21])) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [eval_zero, a3, h31, sub1_beq _ (by omega_using [hst])]) (fun hs => ?_)
      (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      refine WP.seq (WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t₂ => t₂.gpr .r0 = 0 ∧
        t₂.gpr .r16 = off (rlOf s₀).out 0 ∧ t₂.gpr .r17 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧ t₂.mem = t₁.mem)
        (by prun [hc₁.r18, hc₁.r21, ← BitVec.ofNat_add]; exact ⟨rfl, by congr 1; omega_using []⟩) (by decide))
        fun t₂ ⟨⟨b0, b16, b17, m2⟩, k2⟩ => ?_)
      have ho : Scr t₂ (rlOf s₀).out (2 * (rlOf s₀).ql) :=
        Scr.of_mem (by rw [k2.wr, hc₁.wr, hwr]; simp) hL.nwOut
      refine WP.mono (zeroLoop_ok (by omega_using [hq]) (by omega_using [hq]) ho b0 b16 b17) fun t₃ ⟨⟨z3, o3⟩, k3⟩ => ?_
      refine hP t₃ (hc₁.step hL (k2.trans k3).sp (k2.trans k3).rd (k2.trans k3).wr
        (fun r hr => (k2.trans k3).gpr r (ctx_z r hr)) ?_) ((k2.trans k3).mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 R.used := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h25)
  have c31 : t₂.gpr .r31 = BitVec.ofNat 64 R.status := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h31)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)) fun t₃ ⟨⟨_, _, o3⟩, k3⟩ => ?_
  have hc₃ : Ctx (rlOf s₀) s₀ t₃ := hc₂.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_012 r hr))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr ((rlOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [hc₃.wr, hwr, BitVec.add_zero]
    exact ⟨(rlOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hus' : InRegions t₃.wr (rlOf s₀).used 8 := by rw [← BitVec.add_zero (rlOf s₀).used]; exact hus
  refine WP.mono (WP.keep (c := .block [.store .d .r25 .r30 0, .addi .r3 .r31 0]) [.r3] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW ((rlOf s₀).used + BitVec.ofNat 64 0) (BitVec.ofNat 64 R.used) ∧
      t₄.gpr .r3 = BitVec.ofNat 64 R.status)
    (by prun [hc₃.r30, (k3.gpr _ (by decide)).trans c25, (k3.gpr _ (by decide)).trans c31, hus, hus', add0]) (by decide))
    fun t₄ ⟨⟨m4, a3⟩, k4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (rlOf s₀).usedR.Contains ((rlOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (rlOf s₀).F d) 64 = t₃.mem.readW (off (rlOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (RL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hin : ∀ i < 19, InRegions (t₄.rd ++ t₄.wr) (off (rlOf s₀).F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k4.rd, k4.wr, hc₃.rd, hc₃.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains hL rfl (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  refine WP.mono (restoreRegs_ok t₄ (k4.sp.trans hc₃.sp) hin
    (fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi])).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.lr)) fun t₅ ⟨r5, l5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, r5, ?_, l5, sp5.trans (k4.sp.trans hc₃.sp), rd5.trans (k4.rd.trans hc₃.rd),
    wr5.trans (k4.wr.trans hc₃.wr)⟩
  · rw [o5 .r3 (by decide) (by decide) (by decide)]; exact a3
  · rw [m5, m4, bytes_frame (rs := [(rlOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by omega_using [hq])]
    rw [bytes_outside (o3.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using [])) hL.dFO (by omega_using [hq])]
    exact o2
  · rw [m5, m4, BitVec.add_zero, Mem.readW_writeW_self64]
  · rw [o5 .r2 (by decide) (by decide) (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact hc₂.r2

theorem ctx_31 : ∀ r ∈ ctxRegs, r ∉ ([.r31] : List Reg) := by decide

theorem preserved_nv : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = nv i := by decide

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : rsContract.pre s₀) (hf : Fin s₀ (rsRes s₀) t)
    (m : Mem) (u : Nat → BitVec 64) (fl : Frame [(rlOf s₀).frR] t.mem m) :
    abiPreserved s₀ { freed frameBytes t with mem := m, unknowns := u } ∧
      rsContract.post s₀ { freed frameBytes t with mem := m, unknowns := u } := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hst : (rsRes s₀).status ≤ 2 := by
    rw [rsRes_eq h]; exact Dsa.randomSignLoop_status_le _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.lr⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    rcases preserved_nv r hr with rfl | ⟨i, hi, rfl⟩
    · exact hf.r2
    · exact hf.nv i hi
  · simp only [freed, hf.sp, RL.F, rlOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.r3, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · have e3 : s₀.gpr .r3 = (rlOf s₀).out := rfl
    have e4 : (s₀.gpr .r4).toNat = 2 * (rlOf s₀).ql := hol
    rw [e3, e4]
    -- The `free` loses the frame's bytes, which lie apart from the output and `used`.
    exact Eq.trans (List.map_congr_left fun i hi =>
      lost_byte fl (R := (rlOf s₀).outR) hL.dFO.symm (List.mem_range.mp hi)) hf.out
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) ((fl.readW (r := (rlOf s₀).usedR) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.dFU.symm) (by decide)).trans hf.used)

end VG.Proof.Dsa.PPC64LE.RS

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining)
open VG.Proof.Dsa.Random (sampleStatus)

theorem randomSign_correct (s₀ : State) (h : rsContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.PPC64LE.RandomSign.code s₀ tr t ∧ abiPreserved s₀ t ∧ rsContract.post s₀ t := by
  show WP isa Impl.Dsa.PPC64LE.RandomSign.code s₀ fun t => abiPreserved s₀ t ∧ rsContract.post s₀ t
  have hL := rlOf_ok h
  have hst : (resOf s₀).status ≤ 2 := Dsa.randomSignLoop_status_le _ _ _ _ _ _
  have hnone : (resOf s₀).status ≠ 1 → (resOf s₀).signature = none := fun hs => by
    have := Dsa.randomSignLoop_success (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (inpOf (rlOf s₀) s₀.mem).digest 8 ((inpOf (rlOf s₀) s₀.mem).rand.drop 0)
    cases hc : (resOf s₀).signature with
    | none => rfl
    | some _ => exact absurd (this.mpr (by simp only [resOf, randomSignRemaining] at hc ⊢; rw [hc]; rfl)) hs
  have hfin : ∀ t, Ctx (rlOf s₀) s₀ t → t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)) →
      WP isa (finish [.add .r17 .r21 .r21]) t fun t' =>
        ∀ m u, Frame [⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩] t'.mem m →
          abiPreserved s₀ { freed frameBytes t' with mem := m, unknowns := u } ∧
            rsContract.post s₀ { freed frameBytes t' with mem := m, unknowns := u } :=
    fun t hc h25 h31 hsig => WP.mono (finish_ok h hc h25 h31 hst hsig hnone) fun t' hf m u fl =>
      fin_post h (by rw [rsRes_eq h]; exact hf) m u fl
  unfold Impl.Dsa.PPC64LE.RandomSign.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.PPC64LE.RandomSign.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (prepareQ_ok h he.ctx) fun t₂ ⟨sc, h0, m2, k2⟩ => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 0 := (k2.gpr _ (by decide)).trans he.r25
  refine WP.seq (WP.ite (decide (¬ 1 < qOf s₀)) (by rw [eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_))
  · -- q ≤ 1: no attempt.
    simp only [decide_eq_true_eq] at hq
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₃ ⟨⟨m3, a31⟩, k3⟩ => ?_
    have hd : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0) = ⟨none, 0, [4]⟩ := by
      rw [draw_eq hL, show (128 : Nat) = 127 + 1 from rfl, Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega_using [hq])]
    obtain ⟨-, rst, ru⟩ := (RandomSignResultRel.refl (inpOf (rlOf s₀) s₀.mem) 0 8 :
      RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) 0 (7 + 1)).sample_none
      (show (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0).scalar = none by rw [hd])
    rw [hd] at rst ru
    refine hfin t₃ (sc.ctx.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_31 r hr))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => absurd (rst ▸ h1) (by decide)
    · rw [k3.gpr _ (by decide), c25]; congr 1; simp only [resOf] at ru ⊢; omega_using [ru]
    · rw [a31, rst]; rfl
  · -- q > 1: the attempts.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    refine WP.mono (attempts_ok h hq 8 0 t₂ ⟨sc, c25, by omega_using [], (k2.gpr _ (by decide)).trans he.r26, by decide,
      by decide, fun j hj => ?_, RandomSignResultRel.refl _ _ _⟩) fun t₃ ao => hfin t₃ ao.sc.ctx ao.r25 ao.r31 ao.out
    rw [m2]
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have := hE.Wq
    have := hL.ql
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    exact he.nonce j (by omega_using [hj, this])

end VG.Proof.Dsa.PPC64LE.RS

end

end

/-!
# Randomized DSA signing on PPC64LE: constant time

`randomSign_ct`: two runs from states that satisfy `rsContract` and agree on
its public data (the arguments, the key's public part, and the result's
status, octets consumed and trace) leak the same trace. The runs are
followed together (`SameTrace`), as the correctness proof follows each:
every piece the taint analysis checks from the registers both runs agree on
(`st_taint`), and every branch it cannot is decided by public data: q, the
sampling decisions (`sample_st`), and the success of each call of
`vg_dsa_sign_prevalidated` (`random_sign_trace_call`), whose own run is
constant time (`psign_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-! ## The public data -/

/-- The key's public octets, as the contract declassifies them. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rlOf s₀).pl (rlOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl)

theorem pre_kl {s₀ : State} (h : rsContract.pre s₀) : (rlOf s₀).kl = (s₀.gpr .r7).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hkl, -⟩ := h
  simp only [RL.kl, rlOf]; omega_using [hkl]

theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    (Spec.Rsa.bytesAt m p k).take n = Spec.Rsa.bytesAt m p n := by
  have := VG.Proof.Dsa.bytesAt_slice m p (offset := 0) (len := n) (total := k) (by omega_using [h])
  rwa [List.drop_zero, show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

/-- What the public data fix: the call's data, the key's public octets, and
the result's status and trace. -/
theorem pub_facts {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (hp : rsContract.pub s₁ s₂) :
    rlOf s₁ = rlOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧ (resOf s₁).status = (resOf s₂).status ∧
      (resOf s₁).trace = (resOf s₂).trace := by
  have k₁ := pre_kl h₁
  have k₂ := pre_kl h₂
  obtain ⟨hsp, h3, -, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, hl⟩ := hp
  have eL : rlOf s₁ = rlOf s₂ := by
    simp only [rlOf, hsp, h3, h5, h6, h8, h9, h10, a0, a1, a2, a3, a4]
  have hlen : (Spec.Dsa.publicBytesLeak (s₁.gpr .r8).toNat (s₁.gpr .r9).toNat
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used]).length =
      (Spec.Dsa.publicBytesLeak (s₂.gpr .r8).toNat (s₂.gpr .r9).toNat
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used]).length := by
    simp only [Spec.Dsa.publicBytesLeak, List.length_append, List.length_map, List.length_take,
      VG.Proof.Bignum.bytesAt_length, h7, h8, h9, List.length_cons, List.length_nil]
  obtain ⟨e1, e2⟩ := List.append_inj hl hlen
  obtain ⟨e3, e4⟩ := List.append_inj' e1 rfl
  have est := (List.cons.inj e4).1
  rw [rsRes_eq h₁, rsRes_eq h₂] at est e2
  refine ⟨eL, ?_, est, e2⟩
  simp only [keyLeak]
  rw [k₁, k₂]
  exact e3

/-- q's octets are within the key's public part. -/
theorem qb_eq {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂) :
    qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem := by
  have hL := rlOf_ok h₁
  have hq := hL.ql
  simp only [keyLeak, Spec.Dsa.publicBytesLeak, ← eL] at ek
  have e := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp ek
  rw [bytesAt_take _ _ (by simp only [RL.kl]; omega_using []), bytesAt_take _ _ (by simp only [RL.kl]; omega_using [])] at e
  have := VG.Proof.Dsa.bytesAt_slice s₁.mem (rlOf s₁).key (offset := (rlOf s₁).pl) (len := (rlOf s₁).ql)
    (total := 3 * (rlOf s₁).pl + (rlOf s₁).ql) (by omega_using [])
  rw [e, VG.Proof.Dsa.bytesAt_slice s₂.mem (rlOf s₁).key (by omega_using [])] at this
  exact this.symm

/-! ## The frame and the scan of q -/

theorem st_alloc {n : Nat} {body : Prog isa} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : SameTrace isa body (allocated n s₁) (allocated n s₂)) :
    SameTrace isa (.frame (.alloc n) body (.free n)) s₁ s₂ :=
  SameTrace.of_relCT (RelCT.alloc (P := fun a b => a = s₁ ∧ b = s₂) (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact hsp)
    (h.to_relCT.mono (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by subst e₁ e₂; exact ⟨ea, eb⟩) fun _ _ h => h))
    ⟨rfl, rfl⟩

/-- Two states of the body with the same call's data agree on its registers. -/
theorem ctx_eq {s₁ s₂ t₁ t₂ : State} (eL : rlOf s₁ = rlOf s₂) (c₁ : Ctx (rlOf s₁) s₁ t₁)
    (c₂ : Ctx (rlOf s₂) s₂ t₂) :
    t₁.sp = t₂.sp ∧ EqRegs t₁ t₂ [.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r30] :=
  ⟨by rw [c₁.sp, c₂.sp, eL], by rw [c₁.r18, c₂.r18, eL], by rw [c₁.r19, c₂.r19, eL], by rw [c₁.r20, c₂.r20, eL],
    by rw [c₁.r21, c₂.r21, eL], by rw [c₁.r22, c₂.r22, eL], by rw [c₁.r23, c₂.r23, eL], by rw [c₁.r24, c₂.r24, eL],
    EqRegs.single (by rw [c₁.r30, c₂.r30, eL])⟩

theorem EqRegs.sub {s₁ s₂ : State} {rs : List Reg} (h : EqRegs s₁ s₂ rs) {rs' : List Reg}
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : EqRegs s₁ s₂ rs' := by
  induction rs' with
  | nil => trivial
  | cons r rs' ih =>
    cases rs' with
    | nil => exact h.mem r (hs r (List.mem_singleton_self r))
    | cons r' rs'' =>
      exact ⟨h.mem r (hs r (List.mem_cons_self ..)), ih fun x hx => hs x (List.mem_cons_of_mem _ hx)⟩

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (.block [.add .r12 .r19 .r20, .addi .r6 .r21 0]) t fun t₁ =>
      (t₁.gpr .r12 = off (rlOf s₀).key (rlOf s₀).pl ∧ t₁.gpr .r6 = BitVec.ofNat 64 (rlOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.r6, .r12] t t₁ :=
  WP.keep [.r6, .r12] (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide)

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    ∀ i ≤ (rlOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (rlOf s₀).key (rlOf s₀).pl) i) 1 := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(rlOf s₀).keyR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega_using [hp, ekl, hi]) (by omega_using [hq, hp, hi])⟩

/-- The significant octets of q, which `sigLen` counts. -/
theorem sig_eq {s₀ t u : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) (hm : u.mem = t.mem) :
    Spec.Rsa.bytesAt u.mem (off (rlOf s₀).key (rlOf s₀).pl) (rlOf s₀).ql = qbOf (rlOf s₀) s₀.mem := by
  rw [hm]; exact hc.qb (rlOf_ok h)

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem)
    (c₁ : Ctx (rlOf s₁) s₁ t₁) (c₂ : Ctx (rlOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (rlOf_ok h₁).ql
  have hq₂ := (rlOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.r19, .r20, .r21] hsp (EqRegs.sub hr) (by taint_decide)) (qargs_ok c₁)
    (qargs_ok c₂) fun u₁ u₂ ⟨⟨a12, a6, m1⟩, k1⟩ ⟨⟨b12, b6, m2⟩, k2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [k1.sp, k2.sp, hsp]
  have e12 : u₁.gpr .r12 = u₂.gpr .r12 := by rw [a12, b12, eL]
  have e6 : u₁.gpr .r6 = u₂.gpr .r6 := by rw [a6, b6, eL]
  refine SameTrace.seq (st_taint [.r12, .r6] usp ⟨e12, e6⟩ (by taint_decide))
    (sigLen_ok a12 a6 (by omega_using [hq₁]) (by omega_using [hq₁]) fun i hi => by rw [k1.rd, k1.wr]; exact q_in h₁ c₁ i (by omega_using [hi]))
    (sigLen_ok b12 b6 (by omega_using [hq₂]) (by omega_using [hq₂]) fun i hi => by rw [k2.rd, k2.wr]; exact q_in h₂ c₂ i (by omega_using [hi]))
    fun v₁ v₂ ⟨⟨x16, n1⟩, kv1⟩ ⟨⟨y16, n2⟩, kv2⟩ => ?_
  rw [sig_eq h₁ c₁ m1] at x16
  rw [sig_eq h₂ c₂ m2, ← eL, ← eq] at y16
  exact st_taint [.r12, .r6, .r16] (by rw [kv1.sp, kv2.sp, usp])
    ⟨by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e12], by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e6],
      EqRegs.single (by rw [x16, y16])⟩ (by taint_decide)

/-! ## A call of `vg_dsa_sign_prevalidated` -/

/-- The state `vg_dsa_sign_prevalidated` is entered in, after `callArgs`. -/
theorem narrow_vals {s₀ w : State} (A : Args (rlOf s₀) s₀ w) (rd wr : List Region) :
    (w.callEntry.withRegions rd wr).sp = (rlOf s₀).F ∧
      (w.callEntry.withRegions rd wr).gpr .r3 = (rlOf s₀).out ∧
      (w.callEntry.withRegions rd wr).gpr .r4 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧
      (w.callEntry.withRegions rd wr).gpr .r5 = (rlOf s₀).key ∧
      (w.callEntry.withRegions rd wr).gpr .r6 = BitVec.ofNat 64 (rlOf s₀).kl ∧
      (w.callEntry.withRegions rd wr).gpr .r7 = BitVec.ofNat 64 (rlOf s₀).pl ∧
      (w.callEntry.withRegions rd wr).gpr .r8 = off (rlOf s₀).F oNonce ∧
      (w.callEntry.withRegions rd wr).gpr .r9 = BitVec.ofNat 64 (rlOf s₀).ql ∧
      (w.callEntry.withRegions rd wr).gpr .r10 = (rlOf s₀).dig ∧
      stackArg (w.callEntry.withRegions rd wr) 0 = BitVec.ofNat 64 (rlOf s₀).dl ∧
      stackArg (w.callEntry.withRegions rd wr) 1 = (rlOf s₀).scr ∧
      stackArg (w.callEntry.withRegions rd wr) 2 = BitVec.ofNat 64 (rlOf s₀).sl := by
  have hc := A.ctx
  refine ⟨hc.sp, (entry_gpr w rd wr (by decide)).trans A.r3, (entry_gpr w rd wr (by decide)).trans A.r4,
    (entry_gpr w rd wr (by decide)).trans A.r5, (entry_gpr w rd wr (by decide)).trans A.r6,
    (entry_gpr w rd wr (by decide)).trans A.r7, (entry_gpr w rd wr (by decide)).trans A.r8,
    (entry_gpr w rd wr (by decide)).trans A.r9, (entry_gpr w rd wr (by decide)).trans A.r10, ?_, ?_, ?_⟩
  · rw [entry_stackArg, hc.sp]; exact hc.a0
  · rw [entry_stackArg, hc.sp]; exact hc.a1
  · rw [entry_stackArg, hc.sp]; exact hc.a2

/-- What a call declassifies: the key's public octets and the call's success. -/
theorem leak_eq {s₀ w : State} (h : rsContract.pre s₀) (A : Args (rlOf s₀) s₀ w) :
    Spec.Dsa.publicBytesLeak ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r7).toNat
        ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r9).toNat
        (Spec.Rsa.bytesAt (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).mem
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r5)
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r6).toNat) ++
      [Spec.Dsa.signStatus (sRes (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))))] =
    keyLeak s₀ ++ [Spec.Dsa.signStatus (sresOf (rlOf s₀) w.mem)] := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨-, -, -, g5, g6, g7, -, g9, -⟩ := narrow_vals A (signRd (rlOf s₀)) (signWr (rlOf s₀))
  rw [sres_eq h A, g5, g6, g7, g9, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq])]
  show Spec.Dsa.publicBytesLeak _ _ (Spec.Rsa.bytesAt w.mem _ _) ++ _ = _
  rw [A.ctx.key]

theorem call_st {s₁ s₂ w₁ w₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (eL : rlOf s₁ = rlOf s₂)
    (ek : keyLeak s₁ = keyLeak s₂) (A₁ : Args (rlOf s₁) s₁ w₁) (A₂ : Args (rlOf s₂) s₂ w₂)
    (hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem)) :
    SameTrace isa (.call "vg_dsa_sign_prevalidated" Impl.Dsa.PPC64LE.PrevalidatedSign.sign) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := spContract) psign_correct psign_ct
    (P := fun a b => a = w₁ ∧ b = w₂) fun _ _ ⟨e₁, e₂⟩ => ?_) ⟨rfl, rfl⟩
  subst e₁ e₂
  obtain ⟨c₁, cw₁⟩ := sign_cov h₁ A₁.ctx
  obtain ⟨c₂, cw₂⟩ := sign_cov h₂ A₂.ctx
  refine ⟨_, _, _, _, sign_pre h₁ A₁, sign_pre h₂ A₂, ?_, c₁, cw₁, c₂, cw₂⟩
  obtain ⟨p0, p3, p4, p5, p6, p7, p8, p9, p10, q0, q1, q2⟩ := narrow_vals A₁ (signRd (rlOf s₁)) (signWr (rlOf s₁))
  obtain ⟨r0, r3, r4, r5, r6, r7, r8, r9, r10, u0, u1, u2⟩ := narrow_vals A₂ (signRd (rlOf s₂)) (signWr (rlOf s₂))
  refine ⟨by rw [p0, r0, eL], by rw [p3, r3, eL], by rw [p4, r4, eL], by rw [p5, r5, eL], by rw [p6, r6, eL],
    by rw [p7, r7, eL], by rw [p8, r8, eL], by rw [p9, r9, eL], by rw [p10, r10, eL], by rw [q0, u0, eL],
    by rw [q1, u1, eL], by rw [q2, u2, eL], ?_⟩
  rw [leak_eq h₁ A₁, leak_eq h₂ A₂, ek, hs]

/-- After the call: the status, from the result's low word, and the attempts left. -/
theorem callFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (h26 : v₁.gpr .r26 = v₂.gpr .r26)
    (h3 : ((v₁.gpr .r3).setWidth 32 == 0) = ((v₂.gpr .r3).setWidth 32 == 0)) : SameTrace isa callFinish v₁ v₂ := by
  unfold callFinish
  exact SameTrace.ite (by rw [eval_zero_w, eval_zero_w, h3])
    (fun _ => by exact st_taint [.r26] hsp h26 (by taint_decide))
    (fun _ => by exact st_taint [] hsp trivial (by taint_decide))

/-! ## The attempts -/

/-- The sampler's data and q agree. -/
theorem same_q {s₁ s₂ : State} (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem) :
    qOf s₂ = qOf s₁ ∧ eOf s₂ = eOf s₁ := by
  refine ⟨?_, ?_⟩
  · show Spec.Dsa.decodeBE (qbOf (rlOf s₂) s₂.mem) = Spec.Dsa.decodeBE (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]
  · show seOf (rlOf s₂) (qbOf (rlOf s₂) s₂.mem) = seOf (rlOf s₁) (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]

/-- `Ctx` after code that writes only `r3`. -/
theorem ctx_r3_step {s₀ t t' : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) (k : Keep [.r3] t t')
    (hm : t'.mem = t.mem) : Ctx (rlOf s₀) s₀ t' :=
  hc.step (rlOf_ok h) k.sp k.rd k.wr (fun r hr => k.gpr r (ctx_r3 r hr)) (by rw [hm]; exact Frame.refl _ _)

/-- The signature a call computes, from an accepted draw `k` in the nonce. -/
theorem sres_draw {s₀ t w : State} (hc : Ctx (rlOf s₀) s₀ t) (hw : w.mem = t.mem)
    {k : Nat} (hn : Spec.Rsa.bytesAt t.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k) :
    sresOf (rlOf s₀) w.mem = Spec.Dsa.signBytes (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (inpOf (rlOf s₀) s₀.mem).qLen k)
      (inpOf (rlOf s₀) s₀.mem).digest := by
  simp only [sresOf, inpOf]
  rw [hw, hc.key, hc.dig, hn]

theorem attempt_st {s₁ s₂ x₁ x₂ : State} {a u : Nat} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂) (hq : 1 < qOf s₁) (A₁ : AttInv s₁ a u x₁)
    (A₂ : AttInv s₂ a u x₂)
    (ht : (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u a).trace =
      (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u a).trace) :
    SameTrace isa attempt x₁ x₂ := by
  have eq := qb_eq h₁ eL ek
  have hL₁ := rlOf_ok h₁
  have hL₂ := rlOf_ok h₂
  obtain ⟨eQ, eE⟩ := same_q eL eq
  have hq₂ : 1 < qOf s₂ := eQ ▸ hq
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hq
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have hQ₁ := seOf_Q (L := rlOf s₁) s₁.mem hq
  have hQ₂ := seOf_Q (L := rlOf s₂) s₂.mem hq₂
  have env₁ := A₁.sc.env h₁ hq
  have env₂ := A₂.sc.env h₂ hq₂
  have env₂' : SEnv (eOf s₁) (randOf (rlOf s₂) s₂.mem) x₂ := eE ▸ env₂
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := A₁.ha1; omega_using [this]⟩
  have tD : (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).trace = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).trace := by
    rw [← VG.Proof.Dsa.random_sign_trace_draw _ u a', ← VG.Proof.Dsa.random_sign_trace_draw _ u a', ht]
  have dq₁ : Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₁) s₁.mem) u := (draw_eq hL₁ s₁.mem u).symm
  have dq₂ : Spec.Dsa.Random.sample (qOf s₂) 128 ((randOf (rlOf s₂) s₂.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₂) s₂.mem) u := (draw_eq hL₂ s₂.mem u).symm
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₂) s₂.mem).drop u)).trace := by
    rw [dq₁, ← eQ, dq₂]; exact tD
  have eSt : sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) =
      sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) := by
    have := (VG.Proof.Dsa.Random.sample_trace_agree tS).2.2
    rwa [dq₁, ← eQ, dq₂] at this
  have xsp : x₁.sp = x₂.sp := by rw [A₁.sc.ctx.sp, A₂.sc.ctx.sp, eL]
  unfold attempt
  refine SameTrace.seq (sample_st hE₁ hQ₁ env₁ env₂' A₁.r25 A₂.r25 A₁.hu tS) (sample_ok hE₁ hQ₁ env₁ A₁.r25 A₁.hu)
    (sample_ok hE₂ hQ₂ env₂ A₂.r25 A₂.hu) fun y₁ y₂ so₁ so₂ => ?_
  rw [dq₁] at so₁
  rw [dq₂] at so₂
  obtain ⟨sc₁, nz₁⟩ := sampled h₁ A₁.sc A₁.zero so₁ hq
  obtain ⟨sc₂, nz₂⟩ := sampled h₂ A₂.sc A₂.zero so₂ hq₂
  have ysp : y₁.sp = y₂.sp := by rw [sc₁.ctx.sp, sc₂.ctx.sp, eL]
  have W : ∀ {y : State}, WP isa (.block [.subi .r3 .r31 1]) y fun z =>
      (z.mem = y.mem ∧ z.gpr .r3 = y.gpr .r31 - BitVec.ofNat 64 1) ∧ Keep [.r3] y z :=
    fun {_} => WP.keep [.r3] (by prun) (by decide)
  refine SameTrace.seq (st_taint [] ysp trivial (by taint_decide)) W W fun z₁ z₂ ⟨⟨m1, a3⟩, k1⟩ ⟨⟨m2, b3⟩, k2⟩ => ?_
  have zsp : z₁.sp = z₂.sp := by rw [k1.sp, k2.sp, ysp]
  have hst₁ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u)
  have hst₂ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u)
  have ev₁ : isa.eval (.zero .d .r3) z₁ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) = 1)) := by
    rw [VG.PPC64LE.eval_zero, a3, so₁.r31, sub1_beq _ (by omega_using [hst₁])]
  have ev₂ : isa.eval (.zero .d .r3) z₂ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) = 1)) := by
    rw [VG.PPC64LE.eval_zero, b3, so₂.r31, sub1_beq _ (by omega_using [hst₂])]
  refine SameTrace.ite (by rw [ev₁, ev₂, eSt]) (fun hc => ?_) (fun _ => by exact st_taint [] zsp trivial (by taint_decide))
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨k₁, hk₁⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hc)
  obtain ⟨k₂, hk₂⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp (eSt ▸ hc))
  have cz₁ := ctx_r3_step h₁ sc₁.ctx k1 m1
  have cz₂ := ctx_r3_step h₂ sc₂.ctx k2 m2
  have nn₁ : Spec.Rsa.bytesAt z₁.mem (off (rlOf s₁).F oNonce) (rlOf s₁).ql = Spec.Dsa.encodeBE (rlOf s₁).ql k₁ := by
    rw [m1]; exact nonce_eq (W := (eOf s₁).W) hE₁.Wq nz₁ (so₁.cand k₁ hk₁)
  have nn₂ : Spec.Rsa.bytesAt z₂.mem (off (rlOf s₂).F oNonce) (rlOf s₂).ql = Spec.Dsa.encodeBE (rlOf s₂).ql k₂ := by
    rw [m2]; exact nonce_eq (W := (eOf s₂).W) hE₂.Wq nz₂ (so₂.cand k₂ hk₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.r18, .r19, .r20, .r21, .r22] zsp (EqRegs.sub hr) (by taint_decide))
    (callArgs_ok hL₁ cz₁) (callArgs_ok hL₂ cz₂) fun w₁ w₂ ⟨A₁', mw₁, kw₁⟩ ⟨A₂', mw₂, kw₂⟩ => ?_
  have hsi := VG.Proof.Dsa.random_sign_trace_call ht hk₁ hk₂
  have hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem) := by
    rw [sres_draw cz₁ mw₁ nn₁, sres_draw cz₂ mw₂ nn₂]
    simp only [Spec.Dsa.signStatus, hsi]
  have w26 : ∀ {s₀ x y z w : State} {S : Spec.Dsa.Random.Sample}, AttInv s₀ (a' + 1) u x →
      SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S x y → Keep [.r3] y z → Keep argRegs' z w →
      w.gpr .r26 = BitVec.ofNat 64 (a' + 1) := fun A so k kw =>
    (kw.gpr _ (by decide)).trans ((k.gpr _ (by decide)).trans ((so.keep.gpr _ (by decide)).trans A.r26))
  refine SameTrace.seq (call_st h₁ h₂ eL ek A₁' A₂' hs) (sign_ok h₁ A₁') (sign_ok h₂ A₂') fun v₁ v₂ S₁ S₂ => ?_
  refine callFinish_st (by rw [S₁.ctx.sp, S₂.ctx.sp, eL])
    (by rw [S₁.pres _ (by decide), S₂.pres _ (by decide), w26 A₁ so₁ k1 kw₁, w26 A₂ so₂ k2 kw₂]) ?_
  rw [setWidth_beq_zero S₁.r3, setWidth_beq_zero S₂.r3, hs]

/-- The attempts' loop: both runs with the same attempts left, octets
consumed and trace from there. -/
def AI (s₁ s₂ : State) (n : Nat) (x₁ x₂ : State) : Prop :=
  ∃ u, AttInv s₁ n u x₁ ∧ AttInv s₂ n u x₂ ∧
    (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u n).trace = (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u n).trace

/-- Two draws with the same trace consume as much, and agree on acceptance and status. -/
theorem draw_agree {s₁ s₂ : State} {u fuel : Nat} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂)
    (ht : (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u (fuel + 1)).trace =
      (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u (fuel + 1)).trace) :
    (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).used = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).used ∧
      (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).scalar.isSome =
        (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).scalar.isSome ∧
      sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) =
        sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) := by
  obtain ⟨eQ, -⟩ := same_q eL (qb_eq h₁ eL ek)
  have tD : (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).trace = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).trace := by
    rw [← VG.Proof.Dsa.random_sign_trace_draw _ u fuel, ← VG.Proof.Dsa.random_sign_trace_draw _ u fuel, ht]
  have dq₁ : Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₁) s₁.mem) u := (draw_eq (rlOf_ok h₁) s₁.mem u).symm
  have dq₂ : Spec.Dsa.Random.sample (qOf s₂) 128 ((randOf (rlOf s₂) s₂.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₂) s₂.mem) u := (draw_eq (rlOf_ok h₂) s₂.mem u).symm
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₂) s₂.mem).drop u)).trace := by
    rw [dq₁, ← eQ, dq₂]; exact tD
  have := VG.Proof.Dsa.Random.sample_trace_agree tS
  rwa [dq₁, ← eQ, dq₂] at this

theorem attempts_st {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (eL : rlOf s₁ = rlOf s₂)
    (ek : keyLeak s₁ = keyLeak s₂) (hq : 1 < qOf s₁) {n : Nat} {x₁ x₂ : State} (hi : AI s₁ s₂ n x₁ x₂) :
    SameTrace isa attempts x₁ x₂ := by
  have hq₂ : 1 < qOf s₂ := (same_q eL (qb_eq h₁ eL ek)).1 ▸ hq
  unfold attempts
  refine st_loop (AI s₁ s₂) (fun n x₁ x₂ ⟨u, A₁, A₂, ht⟩ => ?_) hi
  have xsp : x₁.sp = x₂.sp := by rw [A₁.sc.ctx.sp, A₂.sc.ctx.sp, eL]
  refine ⟨SameTrace.seq (attempt_st h₁ h₂ eL ek hq A₁ A₂ ht) (WP.of_seq (attempt_ok h₁ hq A₁))
    (WP.of_seq (attempt_ok h₂ hq₂ A₂)) fun y₁ y₂ e₁ e₂ => by
      exact st_taint [] (by rw [e₁, e₂, xsp]) trivial (by taint_decide), _, _, attempt_ok h₁ hq A₁,
    attempt_ok h₂ hq₂ A₂, fun t₁ t₂ ⟨ev₁, _, c₁⟩ ⟨ev₂, _, c₂⟩ => ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := A₁.ha1; omega_using [this]⟩
  obtain ⟨eU, eS, eSt⟩ := draw_agree h₁ h₂ eL ek ht
  have hst := VG.Proof.Dsa.random_sign_attempt_status_agree ht eS eSt
  refine ⟨by rw [ev₁, ev₂, hst], fun hc => ?_⟩
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨hn, i₁⟩ := c₁ hc
  obtain ⟨-, i₂⟩ := c₂ (hst ▸ hc)
  rw [Nat.add_sub_cancel] at i₁ i₂
  refine ⟨n', by omega_using [], _, i₁, eU ▸ i₂, ?_⟩
  have := VG.Proof.Dsa.random_sign_attempt_next_trace ht hc (hst ▸ hc)
  rw [← eU] at this
  exact this

/-! ## The function -/

theorem beq_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · simp [h.mpr hp, hp]
  · rw [decide_eq_false hp]
    exact beq_eq_false_iff_ne.mpr fun e => hp (h.mp e)

/-- The attempts' first state. -/
theorem att_init {s₀ t₁ t₂ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) (he : Entered (rlOf s₀) s₀ t₁)
    (sc : Scanned (rlOf s₀) s₀ t₂) (m2 : t₂.mem = t₁.mem)
    (k2 : Keep (([.r6, .r12] : List Reg) ++ prepRegs) t₁ t₂) :
    AttInv s₀ 8 0 t₂ := by
  have hL := rlOf_ok h
  refine ⟨sc, (k2.gpr _ (by decide)).trans he.r25, by omega_using [], (k2.gpr _ (by decide)).trans he.r26, by decide,
    by decide, fun j hj => ?_, VG.Proof.Dsa.RandomSignResultRel.refl _ _ _⟩
  rw [m2]
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have := hE.Wq
  have := hL.ql
  have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
  exact he.nonce j (by omega_using [hj, this])

theorem randomSign_ct : ConstantTime isa rsContract.pre rsContract.pub Impl.Dsa.PPC64LE.RandomSign.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ek, est, etr⟩ := pub_facts h₁ h₂ hp
  have eq := qb_eq h₁ eL ek
  obtain ⟨eQ, -⟩ := same_q eL eq
  obtain ⟨hsp, e3, -, e5, e6, -, e8, e9, e10, -⟩ := hp
  unfold Impl.Dsa.PPC64LE.RandomSign.code
  refine st_alloc hsp ?_
  unfold Impl.Dsa.PPC64LE.RandomSign.body
  refine SameTrace.seq (st_taint [.r3, .r5, .r6, .r8, .r9, .r10] (by simp only [allocated, hsp])
    ⟨e3, e5, e6, e8, e9, e10⟩ (by taint_decide)) (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  refine SameTrace.seq (prepareQ_st h₁ h₂ eL eq E₁.ctx E₂.ctx) (prepareQ_ok h₁ E₁.ctx) (prepareQ_ok h₂ E₂.ctx)
    fun u₁ u₂ ⟨sc₁, z₁, m₁, k₁⟩ ⟨sc₂, z₂, m₂, k₂⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have hr := (ctx_eq eL sc₁.ctx sc₂.ctx).2
  have z₂' : u₂.gpr .r0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.seq_ite (by rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, beq_of_iff z₁, beq_of_iff z₂'])
    (fun _ => by exact st_taint [.r18, .r21, .r30] usp (EqRegs.sub hr) (by taint_decide)) (fun hc => ?_)
  rw [VG.PPC64LE.eval_zero, beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
  have hq₂ : 1 < qOf s₂ := eQ ▸ hc
  have i₁ := att_init h₁ hc E₁ sc₁ m₁ k₁
  have i₂ := att_init h₂ hq₂ E₂ sc₂ m₂ k₂
  refine SameTrace.seq (attempts_st h₁ h₂ eL ek hc ⟨0, i₁, i₂, etr⟩) (attempts_ok h₁ hc 8 0 u₁ i₁)
    (attempts_ok h₂ hq₂ 8 0 u₂ i₂) fun x₁ x₂ o₁ o₂ => ?_
  have xr := (ctx_eq eL o₁.sc.ctx o₂.sc.ctx).2
  exact st_taint [.r18, .r21, .r30, .r31] (ctx_eq eL o₁.sc.ctx o₂.sc.ctx).1
    ⟨xr.mem _ (by decide), xr.mem _ (by decide), xr.mem _ (by decide), EqRegs.single (by rw [o₁.r31, o₂.r31, est])⟩
    (by taint_decide)

end VG.Proof.Dsa.PPC64LE.RS
