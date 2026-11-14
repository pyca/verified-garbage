module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSSetup
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PX
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Generation.Search

/-! ### `Dsa.PPC64LE.Gen.PAttempt`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.PArith`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.KSDiv`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: the division in the key working space

`div_vp`: `[q] := [q] / [d]` and `[r] := [q] mod [d]` (`div_ok`), for a
divisor whose top word is zero (`TopAll`), the temporary `t` lost.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws stepRegs div_ok)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `w + 1` digits below `2^(32 w)` are `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : val32 m B (arr w j) (w + 1) < 2 ^ (32 * w)) :
    num m B w j = val32 m B (arr w j) (w + 1) := by
  have e := val32_append m B (arr w j) w 1
  rw [e] at h ⊢
  have : val32 m B (arr w j + 4 * w) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (arr w j + 4 * w) 1) with z | z
    · exact z
    · have := Nat.mul_le_mul_left (2 ^ (32 * w)) z; omega_using [h, this]
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t` lost. -/
theorem div_vp {q r d t : Nat} (cert : CertK (VG.Impl.Rsa.PPC64LE.Div.div q r d t))
    (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) (hd1 : d ≠ aOne)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div q r d t)
      (KSt G (divCfg c q r d) X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hqL
  have vd := h.arrs.get hdL
  refine h.ksWP rfl (div_ok hw hq hr hd ht (by decide) hqr hqd hqt hrd hrt hdt (top d hd hd1))
    fun u ⟨_, k, R, v⟩ hr' hw' f => ?_
  have R' : Keep stepRegs s u := ⟨R.gpr, hr', hw'⟩
  simp only [GP.ksState, State.withRegions_mem] at v k
  rw [vd] at v
  obtain ⟨vq, vr⟩ := v hpos
  rw [va] at vq vr
  have dl : c.A d < 2 ^ (32 * G.w) := vd ▸ val32_lt _ _ _ _
  have vr1 : val32 u.mem G.KB (arr G.w r) (G.w + 1) = c.A q % c.A d := vr
  have vr' : num u.mem G.KB G.w r = c.A q % c.A d := by
    have := Nat.mod_lt (c.A q) hpos
    rw [num_of_num1 (by rw [vr1]; omega_using [dl, this])]
    exact vr1
  refine ⟨⟨h.of_ks R' R.sp f (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk, x⟩, kr.of_keep R'⟩
  · show num u.mem G.KB G.w j = VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A q
      (c.A q / c.A d)) r (c.A q % c.A d) j
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vr'
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vq
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejq]
    have jl : j ∈ c.live := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejq
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejr
      · exact hj
    have ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega_arith)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    · exact h.liveOk j hj
  · rw [k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: p and `(p − 1) / q`

`pArith` (`pArith_vp`): from X and q in claims, by the division of X by q
in the key working space: `p − 1 = X − X mod 2q` (`pm1_eq`) in array `aPm1`,
`p` in `aP` and big-endian at `sPBE`, `(p − 1) / q` in `aE` and big-endian
at `sE`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Impl.Rsa.PPC64LE.Keys (sub3 sel copy bitOf orOne clrLow)
open VG.Impl.Dsa.PPC64LE.Generation

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

/-- The candidate p from X and q. -/
abbrev pVal (x q : Nat) : Nat := x + 1 - x % (2 * q)

/-- The arrays after `pArith`. -/
abbrev pA (x q : Nat) : Nat → Nat :=
  KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (pVal x q - 1)) aE ((pVal x q - 1) / q)) aP (pVal x q)

/-- The stage after `pArith`. -/
abbrev pOut (c : Cfg) (G : GP) (x q : Nat) (rest : Claims) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((pVal x q - 1) / q) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest
    A := pA x q
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

/-- Simplifies the arrays' values of a stage. -/
macro "arr_simp" : tactic => `(tactic| simp only [KU, VG.Proof.Rsa.KeyWorkspace.upd, divCfg, A0, aQt, aRm, aDv,
  aDt, aX, aT, aS, aPm1, aP, aE, aH, aOne, aZero, aTmp, slOdd, Nat.reduceEqDiff, ↓reduceIte])

/-- The arrays after the loads, the division and `p − 1`. -/
abbrev aL (x q : Nat) : Nat → Nat := KU (KU (KU A0 aQt x) aX x) aDv q
abbrev aD (x q : Nat) : Nat → Nat := KU (KU (aL x q) aQt (x / q)) aRm (x % q)
abbrev aM (x q : Nat) : Nat → Nat :=
  KU (KU (KU (fun _ => 0) aOne 1) aQt (x / q)) aPm1 (x - x % q - (if x / q % 2 = 0 then 0 else q))

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

/-- `(p − 1) / q` fits its `eBytes` octets. -/
theorem e_lt {x q P Q : Nat} (hx : x < 2 ^ (8 * P)) (hq : 2 ^ (8 * Q - 1) ≤ q) (hQ : 1 ≤ Q) (hQP : Q ≤ P) :
    (pVal x q - 1) / q < 2 ^ (8 * eBytes P Q) := by
  have hp := pVal_lt (q := q) (by omega_arith) hx
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul q0).mpr ?_) (Nat.pow_le_pow_right (by decide)
    (show 8 * P - 8 * Q + 1 ≤ 8 * eBytes P Q by simp only [eBytes]; omega_arith))
  calc pVal x q - 1 < 2 ^ (8 * P) := by omega_arith
    _ = 2 ^ (8 * P - 8 * Q + 1) * 2 ^ (8 * Q - 1) := by rw [← Nat.pow_add]; congr 1; omega_arith
    _ ≤ 2 ^ (8 * P - 8 * Q + 1) * q := Nat.mul_le_mul_left _ hq

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The stages after the loads, the division and `p − 1`. -/
abbrev cL (c : Cfg) (x q : Nat) : Cfg := { c with A := aL x q, live := [aDv, aX, aQt, aOne, aZero] }
abbrev cD (c : Cfg) (x q : Nat) : Cfg :=
  { c with A := aD x q, live := [aQt, aRm, aDv, aX, aOne, aZero] }
abbrev cM (c : Cfg) (x q : Nat) : Cfg := { c with A := aM x q, live := [aPm1, aQt, aOne, aZero], kls := [] }

theorem pLoads_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen) :
    VP (St G c X) (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (ksRegs G.pLen), ksSetup, loadS aQt sX G.pLen,
        loadS aX sX G.pLen, loadS aDv sQ G.qLen])
      (fun σ s => KSt G (cL c (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb)) X σ s ∧ TopAll G s.mem) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  refine VP.seq ksEnter_vp (VP.seq ksSetup_vp ?_)
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aQt), by kernel_rfl⟩ (by decide) (by simp [aQt]) rfl (by exact hx) hxl (by omega_arith) (by omega_arith)
    (by decide) (by omega_arith)) ?_
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aX), by kernel_rfl⟩ (by decide) (by simp [aX]) rfl (by exact hx) hxl (by omega_arith) (by omega_arith)
    (by decide) (by omega_arith)) ?_
  refine (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aDv), by kernel_rfl⟩ (by decide) (by simp [aDv]) rfl (by exact hqc) hql (by omega_arith)
    (by omega_arith) (by decide) (by omega_arith)).mono (fun _ _ h => h) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ⟨⟨⟨h.mono
      (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨?_, rfl⟩) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩, top⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [aDv, aX, aQt, aOne, aZero]

theorem pDivide_vp {x q : Nat} (hpos : 0 < q) :
    VP (fun σ s => KSt G (cL c x q) X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt)
      (KSt G (cD c x q) X) := by
  refine (div_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt), by kernel_rfl⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
    (by simp [aDt, aDv, aX, aQt, aOne, aZero]) (by arr_simp; exact hpos)).mono (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, kr⟩ => ⟨⟨h.mono
    (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ?_) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [aQt, aRm, aDv, aX, aOne, aZero], by arr_simp⟩

theorem pPm1_vp {x q : Nat} :
    VP (KSt G (cD c x q) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd,
        sub3 aPm1 aT aS])
      (KSt G (cM c x q) X) := by
  refine VP.seq (sub3_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sub3 aT aX aRm), by kernel_rfl⟩ (by decide) (by simp [aX]) (by simp [aRm]) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (bitOf slOdd aQt)), by kernel_rfl⟩ (by simp [aQt]) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sel aS aZero aDv slOdd), by kernel_rfl⟩ (by decide) (by simp [aZero]) (by simp [aDv]) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sub3 aPm1 aT aS), by kernel_rfl⟩ (by decide) (by simp [aT]) (by simp [aS]) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega_arith)).mono (fun _ _ h => h) fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by simp [aPm1, aQt, aOne, aZero], by arr_simp⟩

theorem pTail_vp {x q : Nat} (hq : 2 ^ (8 * G.qLen - 1) ≤ q)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (KSt G (cM c x q) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [copy aP aPm1, .block (orOne aP), copy aE aQt, .block (clrLow aE),
        storeS aP sPBE G.pLen, storeS aE sE (eBytes G.pLen G.qLen)])
      (KSt G (pOut c G x q rest) X) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega_arith) hx
  have elt := e_lt (P := G.pLen) (Q := G.qLen) hx hq (by omega_arith) (by omega_arith)
  have hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x q0, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega_arith
  have nE : sE = 1440 := rfl
  have nP : sPBE = 1056 := rfl
  have nH : hEnd = 352 := rfl
  have hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega_arith
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aP aPm1), by kernel_rfl⟩ (by decide) (by simp [aPm1]) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (orOne aP)), by kernel_rfl⟩ (by simp [aP])) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aE aQt), by kernel_rfl⟩ (by decide) (by simp [aQt]) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (clrLow aE)), by kernel_rfl⟩ (by simp [aE])) ?_
  refine VP.seq (storeS_vp (o := sPBE) (n := G.pLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aP), by kernel_rfl⟩
    (by simp [aP]) (by omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := rest) fun y hy => ⟨(hrest y hy).1, (hrest y hy).2.1⟩) ?_
  refine (storeS_vp (o := sE) (n := eBytes G.pLen G.qLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aE), by kernel_rfl⟩
    (by simp [aE]) (by simp only [eBytes]; omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest) fun y hy => ?_).mono (fun _ _ h => h)
    fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_)
      (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨List.mem_cons.mpr (.inl ?_), ?_⟩
      · arr_simp
        rw [hP, Nat.mod_eq_of_lt plt]
      · simp only [Apart, VG.Proof.Rsa.i2osp_length]; omega_arith
    · exact ⟨List.mem_cons_of_mem _ hy, (hrest y hy).2.2⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine List.mem_cons.mpr (.inl ?_)
      arr_simp
      rw [hE, Nat.mod_eq_of_lt elt]
    · exact List.mem_cons_of_mem _ hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by simp [aE, aP, aPm1, aOne, aQt, aZero], ?_⟩ <;> arr_simp
    · exact hE
    · exact hP
    · exact hM

/-- p and `(p − 1) / q` from X and q. -/
theorem pArith_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen)
    (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE qb) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (St G c X) (pArith G.pLen G.qLen)
      (KSt G (pOut c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb) rest) X) := by
  have hxlt : Spec.Dsa.decodeBE xb < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt xb
    rwa [hxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have hpos : 0 < Spec.Dsa.decodeBE qb := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  exact VP.seq (pLoads_vp hlq hx hxl hqc hql) (VP.seq (pDivide_vp hpos)
    (VP.seq pPm1_vp (pTail_vp hqlo hlq hxlt hrest)))

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: one candidate p

`pAttempt` (`pAttempt_vp`): X, p from it, and unless p is below
`2^(L − 1)` (`topBit_vp`) its probable-prime test: `fP` := 0 if the
witnesses ran out, 1 if p is a probable prime, else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

theorem top_bit (b : BitVec 8) : (b.setWidth 64 >>> 7 == 0) = decide (b.toNat < 128) := by
  revert b; decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `r0 = 0` iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {pv : Nat} (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7])
      (fun σ t => St G c X σ t ∧ isa.eval (.zero .d .r0) t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28]) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have l := h.lens
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  have hp0 : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have nP : sPBE = 1056 := rfl
  have hkB : sPBE + G.pLen ≤ kB G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by decide) (by rw [gi.r28]) (gi.inRdWr (by omega_using [big, kb, l, hkB])) fun s₁ u₁ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun t u sp _ => WP.block_nil fun sp' => ⟨⟨h.of_keep
    (ws := [.r0]) ⟨fun r hr => by rw [u.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
      by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩ (by rw [u.mem, u₁.mem]) sp', x⟩, ?_⟩
  -- The byte: p's first.
  have b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  have byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, hp0]
  rw [eval_zero, u.gpr, u₁.gpr, byte, top_bit]
  congr 1
  rw [← VG.Proof.Dsa.encodeBE_i2osp]
  exact decide_eq_decide.mpr (VG.Proof.Dsa.Generation.candidate_firstByte hp0 hpv)

theorem varOk_fP : VarOk G fP := varOk_of (by decide)

/-- The stage after a test's result recorded in `fP`. -/
def pRes (c0 : Cfg) (wl : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => (testCfg c0 c0.cl wl none).setV fP (BitVec.ofNat 64 0)
  | some (true, r) => (testCfg c0 c0.cl wl (some (true, r))).setV fP (BitVec.ofNat 64 1)
  | some (false, r) => testCfg c0 c0.cl wl (some (false, r))

theorem testCfg_fRes (c0 : Cfg) (cl : Claims) (wl : Nat) (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    fRes ∈ (testCfg c0 cl wl res).LS ∧
      (testCfg c0 cl wl res).V fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
  rcases res with _ | ⟨b, r⟩
  · exact ⟨List.mem_cons_self, by simp [testCfg, Proof.Dsa.ProbablePrime.status]⟩
  · refine ⟨List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [testCfg, Cfg.setV]
    rw [upd_ne _ _ (by decide), upd_self]
    cases b <;> rfl

/-- `fP` := 0 if the witnesses ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 0), .ite (.zero .d .r0) (.block (stImm fP 0))
        (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 1), .ite (.zero .d .r0) (.block (stImm fP 1))
          (.block [])])])
      (St G (pRes c0 wl res) X) := by
  obtain ⟨fl, fv⟩ := testCfg_fRes c0 c0.cl wl res
  have vres : ∀ σ s, St G (testCfg c0 c0.cl wl res) X σ s →
      fw s.mem G fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := fun σ s h => by
    rw [h.1.gi.slotV fl, fv]
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (by decide) vres
    fun σ s t h h' _ e => (⟨⟨h', h.2⟩, e⟩ : St G (testCfg c0 c0.cl wl res) X σ t ∧ _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · rcases res with _ | ⟨b, r⟩
    · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl none) (fun σ s h => h.1.1.1) (by decide) varOk_fP
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z
      unfold Proof.Dsa.ProbablePrime.status at z
      cases b <;> simp at z <;> contradiction
  · rcases res with _ | ⟨b, r⟩
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
        rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
    refine VP.seq (cmpF_vp (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => vres σ s h.1.1) fun σ s t h h' _ e => (⟨⟨h', h.1.1.2⟩, e⟩ :
        St G (testCfg c0 c0.cl wl (some (b, r))) X σ t ∧ _)) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · cases b
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
      · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl (some (true, r))) (fun σ s h => h.1.1.1) (by decide)
          varOk_fP fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · cases b
      · exact VP.block_nil fun σ s h => h.1.1
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction

/-- The claims kept through a candidate p: the padding and q. -/
abbrev pRest {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The stage after a candidate p from X (`xv`) and q (`qv`), tested with the
witnesses from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.witLen (Spec.Dsa.probablePrime (pVal xv qv) (G.witB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (hLb : Lp.bits = 8 * G.pLen) (hLc : Lp.candidate = g.pCand) (hsize : Lp.size ≤ 8 * wWords G.pLen)
    (hL : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : Lp.candidate + Lp.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + Lp.candidate < 2 ^ 15)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    {k off u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  have hq56 : G.qLen < 56 := by omega_arith
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hc : (cnt G + 1) * G.qLen ≤ G.pLen + 32 ∧ G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have xl : (xBytes HO G k off).length = G.pLen := by
    rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
      rw [← List.length_pos_iff, List.length_drop, accB_length HO hHl]; omega_arith), List.length_drop,
      accB_length HO hHl]; omega_arith
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by
    rw [← hH, HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  have qlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
  have nX : sX = 672 := rfl
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nP : sPBE = 1056 := rfl
  have nE : sE = 1440 := rfl
  have hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega_using [hlq]
  unfold Geo.pAttempt
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hp, hq]
  refine VP.seq (pX_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega_arith) ?_
  refine VP.seq ((pArith_vp hlq (by simp) xl (by simp) ql qlo (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega_arith, by simp only [Apart, pl]; omega_arith⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega_arith, by simp only [Apart, ql]; omega_arith⟩).mono
      (fun _ _ h => h) fun _ _ h => h.1) ?_
  have xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega_arith) xlt
  have plt' : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) < 256 ^ G.pLen := by
    rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  refine VP.seq (topBit_vp (by simp) plt') ?_
  generalize hpv : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) = pv at plt plt'
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · refine VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => ?_
      unfold pAttCfg
      rw [hpv]
      simp only [hcnd, ↓reduceIte]
      exact h
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
    have pb : Spec.Dsa.decodeBE (Spec.Rsa.i2osp pv G.pLen) = pv := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt plt']
    have podd : pv % 2 = 1 := hpv ▸ VG.Proof.Dsa.Generation.pReduction_odd _ _
    have pbl : Spec.Dsa.bitLength pv = 8 * G.pLen :=
      (VG.Proof.Dsa.bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, plt⟩
    unfold pAttCfg
    rw [hpv]
    simp only [hcnd, ↓reduceIte]
    generalize hc0 : pOut c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
      (pRest HO.md G k) = c0
    have cl0 : c0.cl = (sE, Spec.Rsa.i2osp ((pv - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
        (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hc0, ← hpv]
    have eLS : c0.LS = c.LS := by rw [← hc0]
    have eV : c0.V = c.V := by rw [← hc0]
    have small : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ kB G.pLen := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [pl]; omega_arith
      · simp only [ql]; omega_arith
    have pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    have := test_vp (X := X) (c := c0) (cb := Spec.Rsa.i2osp pv G.pLen) (src := sPBE) (cl' := c0.cl)
      (name := g.pName) okp hu (by rw [eLS]; exact hU) (by rw [eV]; exact hUv) hwl hsize hL hcand hcand15 pin
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length, hLb]; omega_arith)
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith)
      (by decide) (by rw [pb]; exact podd) (by rw [pb, hLb, pbl]) (by rw [eLS]; exact hU') (by rw [eLS]; exact hU88)
      fun y hy => ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by
        have := small y hy; simp only [Apart, decide_eq_true_eq]; omega_arith⟩),
        fun r _ => .inl (by have := small y hy; omega_arith)⟩
    rw [VG.Proof.Rsa.i2osp_length, hLc] at this
    refine VP.seq (this.mono (fun σ s h => h.1.1) fun _ _ h => h) ?_
    rw [tRes, pb]
    exact pDecide_vp _

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: the search for p

`pAdvance_vp`: the next counter; `pCont_vp` and `pExit_vp`: the code after a
candidate (`pTail`), which goes on to the next counter, or ends the search;
the definitions of the search's stages, as `Spec.Dsa.primeFromSeed` searches
the counters (`pSpec`, `pCount`, `pU`, `pFin`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

section
variable {G : GP} {X : State → Prop}

/-- `r := r + i`, for a register both runs know. -/
theorem addi_vp {P : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → St G (c σ) X σ s) {r : Reg}
    (hr : r ≠ .r0) (h28 : r ≠ .r28) {v i : Nat} (hi : i < 2 ^ 15) :
    VP (fun σ s => P σ s ∧ s.gpr r = BitVec.ofNat 64 v) (.block [.addi r r i])
      (fun σ s => St G (c σ) X σ s ∧ s.gpr r = BitVec.ofNat 64 (v + i)) := by
  refine VP.pub (SS.pub (c := c) fun σ s h => (hF σ s h.1).1) [r] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, r]) (.block [.addi r r i]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨h, e⟩ => ?_
  have h' := hF σ s h
  refine WP.wr (exec_addi hr hi) fun t u sp _ => WP.block_nil ⟨⟨h'.1.of_upd u sp h28, h'.2⟩, ?_⟩
  rw [u.gpr, e, BitVec.ofNat_add]

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and `r0 = 0` when the
counter reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 64 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off)
    (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (.block [ld .r3 fCounter, .addi .r3 .r3 1, st .r3 fCounter, ld .r4 fOffset,
        .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * G.pLen)])
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
        isa.eval (.zero .d .r0) s = some (decide (j + 1 = 32 * G.pLen))) := by
  show VP _ (.block ([ld .r3 fCounter] ++ ([.addi .r3 .r3 1] ++ ([st .r3 fCounter] ++ ([ld .r4 fOffset] ++
    ([.addi .r4 .r4 C] ++ ([st .r4 fOffset] ++ [.subi .r0 .r3 (32 * G.pLen)]))))))) _
  -- The counter.
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hCt).trans hCv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (addi_vp (c := fun _ => d) (fun σ s h => h) (by decide) (by decide) (by decide)) ?_
  have d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 64 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.block_append (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' K => ⟨⟨r3 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The offset.
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.1.gi.slotV d1O).trans (by
        show upd d.V fCounter (BitVec.ofNat 64 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' u => ⟨⟨⟨h', x⟩, by rw [u.other _ (by decide), r3]⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 (off + C))
    (VP.pub (SS.pub (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) fun σ s h => h.1.1.1) [.r4]
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r4]) (.block [.addi .r4 .r4 C]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨⟨h, x⟩, r3⟩, r4⟩ =>
        WP.wr (exec_addi (by decide) hC) fun t u sp _ => WP.block_nil
          ⟨⟨⟨h.of_upd u sp (by decide), x⟩, by rw [u.other _ (by decide), r3]⟩, by
            rw [u.gpr, r4, BitVec.ofNat_add]⟩) ?_
  refine VP.block_append (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1.1)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r3⟩, r4⟩ h' K => ⟨⟨r4 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The end of the counters.
  refine VP.pub (SS.pub (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) fun σ s h => h.1.1) [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3]) (.block [.subi .r0 .r3 (32 * G.pLen)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  have l := h.lens
  have h15 : 32 * G.pLen ≤ 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.wr (exec_subi (by decide) h15) fun t u sp _ => WP.block_nil ⟨⟨h.of_upd u sp (by decide), x⟩, ?_⟩
  rw [eval_zero, u.gpr, r3, sub_beq_zero]
  congr 1
  by_cases e : j + 1 = 32 * G.pLen
  · simp [e]
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [hj, l, this]

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite (.zero .d .r0) (.seq (.block [ld .r3 fCounter, .addi .r3 .r3 1,
      st .r3 fCounter, ld .r4 fOffset, .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * L)])
    (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block []))) (.block [])) (.block (cmpF fP 4)))

theorem ofNat64_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [ha, hb, this]

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hP : fP ∈ d.LS)
    (hPv : d.V fP = BitVec.ofNat 64 4) (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 64 j)
    (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))).setV fP
            (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
          isa.eval (.zero .d .r0) s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some true)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
              (BitVec.ofNat 64 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X σ s ∧ isa.eval (.zero .d .r0) s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 64 (j + 1))) fOffset (BitVec.ofNat 64 (off + C)) fP = _
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false) := by
  have ne : (BitVec.ofNat 64 v == BitVec.ofNat 64 4) = false := by
    rw [ofNat64_beq (by omega_using [hv]) (by decide)]; simp; omega_using [hv]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t h h' _ e => ⟨⟨h', h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The witnesses read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.witLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega_using [this]
    · split <;> omega_arith

/-- The search's header words at counter `j`, with `u` witnesses read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 64 u)).setV fCounter (BitVec.ofNat 64 j)).setV fOffset
    (BitVec.ofNat 64 (1 + j * (cnt G + 1)))).setV fP (BitVec.ofNat 64 4)

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.witB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((p - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) =>
    ((pFound c HO G k p).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))).setV fP (BitVec.ofNat 64 1)
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 64 (G.witLen - r.length))).setV fP (BitVec.ofNat 64 2)
  | none => (pNone c HO G).setV fP (BitVec.ofNat 64 0)

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.witLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = BitVec.ofNat 64 4) (vO : V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 64 j) (vU : V fUsed = BitVec.ofNat 64 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
