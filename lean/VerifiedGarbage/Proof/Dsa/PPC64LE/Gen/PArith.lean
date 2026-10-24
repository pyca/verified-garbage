module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSDiv
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega

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
  have e : x - x % q = q * b := by omega
  rw [e]
  have e2 : 2 * q * a = 2 * (q * a) := by rw [Nat.mul_assoc]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · simp only [h, ↓reduceIte]
    have : b = 2 * a := by omega
    rw [this, Nat.mul_left_comm, e2]; omega
  · simp only [show ¬ b % 2 = 0 by omega, ↓reduceIte]
    have : b = 2 * a + 1 := by omega
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, e2]; omega

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
    rw [show K = K - 1 + 1 by omega, Nat.pow_succ]; simp
  rw [pVal_eq] at odd ⊢
  rcases Nat.lt_or_ge (2 * q * (x / (2 * q)) + 1) (2 ^ K) with h | h
  · exact h
  · have : 2 * q * (x / (2 * q)) + 1 = 2 ^ K := by omega
    rw [this] at odd; omega

/-- `(p − 1) / q` fits its `eBytes` octets. -/
theorem e_lt {x q P Q : Nat} (hx : x < 2 ^ (8 * P)) (hq : 2 ^ (8 * Q - 1) ≤ q) (hQ : 1 ≤ Q) (hQP : Q ≤ P) :
    (pVal x q - 1) / q < 2 ^ (8 * eBytes P Q) := by
  have hp := pVal_lt (q := q) (by omega) hx
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul q0).mpr ?_) (Nat.pow_le_pow_right (by decide)
    (show 8 * P - 8 * Q + 1 ≤ 8 * eBytes P Q by simp only [eBytes]; omega))
  calc pVal x q - 1 < 2 ^ (8 * P) := by omega
    _ = 2 ^ (8 * P - 8 * Q + 1) * 2 ^ (8 * Q - 1) := by rw [← Nat.pow_add]; congr 1; omega
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
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega
  refine VP.seq ksEnter_vp (VP.seq ksSetup_vp ?_)
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aQt), rfl⟩ (by decide) (by simp [aQt]) rfl (by exact hx) hxl (by omega) (by omega)
    (by decide) (by omega)) ?_
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aX), rfl⟩ (by decide) (by simp [aX]) rfl (by exact hx) hxl (by omega) (by omega)
    (by decide) (by omega)) ?_
  refine (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aDv), rfl⟩ (by decide) (by simp [aDv]) rfl (by exact hqc) hql (by omega)
    (by omega) (by decide) (by omega)).mono (fun _ _ h => h) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ⟨⟨⟨h.mono
      (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨?_, rfl⟩) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩, top⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [aDv, aX, aQt, aOne, aZero]

theorem pDivide_vp {x q : Nat} (hpos : 0 < q) :
    VP (fun σ s => KSt G (cL c x q) X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt)
      (KSt G (cD c x q) X) := by
  refine (div_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt), rfl⟩ (by decide) (by decide) (by decide) (by decide)
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
    (sub3 aT aX aRm), rfl⟩ (by decide) (by simp [aX]) (by simp [aRm]) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (bitOf slOdd aQt)), rfl⟩ (by simp [aQt]) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sel aS aZero aDv slOdd), rfl⟩ (by decide) (by simp [aZero]) (by simp [aDv]) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sub3 aPm1 aT aS), rfl⟩ (by decide) (by simp [aT]) (by simp [aS]) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega)).mono (fun _ _ h => h) fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩)
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
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega) hx
  have elt := e_lt (P := G.pLen) (Q := G.qLen) hx hq (by omega) (by omega)
  have hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x q0, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega
  have nE : sE = 1440 := rfl
  have nP : sPBE = 1056 := rfl
  have nH : hEnd = 296 := rfl
  have hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aP aPm1), rfl⟩ (by decide) (by simp [aPm1]) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (orOne aP)), rfl⟩ (by simp [aP])) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aE aQt), rfl⟩ (by decide) (by simp [aQt]) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (clrLow aE)), rfl⟩ (by simp [aE])) ?_
  refine VP.seq (storeS_vp (o := sPBE) (n := G.pLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aP), rfl⟩
    (by simp [aP]) (by omega) (by omega) (by decide) (by omega)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega)
    (cl' := rest) fun y hy => ⟨(hrest y hy).1, (hrest y hy).2.1⟩) ?_
  refine (storeS_vp (o := sE) (n := eBytes G.pLen G.qLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aE), rfl⟩
    (by simp [aE]) (by simp only [eBytes]; omega) (by omega) (by decide) (by omega)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega)
    (cl' := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest) fun y hy => ?_).mono (fun _ _ h => h)
    fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_)
      (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨List.mem_cons.mpr (.inl ?_), ?_⟩
      · arr_simp
        rw [hP, Nat.mod_eq_of_lt plt]
      · simp only [Apart, VG.Proof.Rsa.i2osp_length]; omega
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
