module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSStore
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSSetup
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Omega

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

/-- The certificates of `pArith`'s pieces that depend on the geometry. -/
structure PArithCerts (L Lq : Nat) : Prop where
  st : Cert7 (storeBE L aP sPBE L)

theorem pArithCerts_128 : PArithCerts 128 20 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 128 aP sPBE 128), rfl⟩⟩

theorem pArithCerts_256 : PArithCerts 256 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 256 aP sPBE 256), rfl⟩⟩

theorem pArithCerts_384 : PArithCerts 384 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 384 aP sPBE 384), rfl⟩⟩

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
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega
  refine VP.seq (G := St G { c with A := A0, live := [aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] } X)
    ((ksSetup_vp (G := G) (c := c) (X := X)).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ =>
      ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; rcases hj with rfl | rfl <;> decide, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), x⟩) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aQt), rfl⟩ rfl (by decide) (by exact hx) hxl (by omega) (by omega)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aX), rfl⟩ rfl (by decide) (by exact hx) hxl (by omega) (by omega)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  exact loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aDv), rfl⟩ rfl (by decide) (by exact hqc) hql (by omega) (by omega)

theorem pDivide_vp {x q : Nat} (hpos : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    VP (fun σ s => St G (cL c G x q) X σ s ∧ Top G s.mem aDv)
      (VG.Impl.Rsa.Arm.Keys.seqs [.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt), VG.Impl.Rsa.Arm.Div.code,
        .block (wRegs G.pLen)])
      (St G (cD c G x q) X) := by
  refine VP.seq (divHdr_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt)), rfl⟩ (by decide) (by decide) (by decide)
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
    (VG.Impl.Rsa.Arm.Keys.sub3 aT aX aRm), rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.bitOf slOdd aQt)), rfl⟩ (by simp) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sel aS aZero aDv slOdd), rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sub3 aPm1 aT aS), rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega)).mono (fun _ _ h => h) fun σ s ⟨h, xx⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simp, by arr_simp⟩

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

theorem pTail_vp {x q : Nat} (cert : Cert7 (storeBE G.pLen aP sPBE G.pLen)) (hq : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y) :
    VP (St G (cM c x q) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.copy aP aPm1, .block (VG.Impl.Rsa.Arm.Keys.orOne aP),
        VG.Impl.Rsa.Arm.Keys.copy aE aQt, .block (VG.Impl.Rsa.Arm.Keys.clrLow aE), storeBE G.pLen aP sPBE G.pLen])
      (St G (pOut c G x q rest) X) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega) hx
  have hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x hq, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aP aPm1), rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.orOne aP)), rfl⟩ (by simp)) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aE aQt), rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.clrLow aE)), rfl⟩ (by simp)) ?_
  refine (storeBE_vp cert rfl (by simp) (by omega) (by omega) (by simp only [sPBE, sK, sA, wa]; omega)
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
  exact VP.seq (pLoads_vp hlq hx hxl hqc hql) (VP.seq (pDivide_vp hpos (by omega))
    (VP.seq pPm1_vp (pTail_vp certs.st hpos (by omega) hxlt hrest)))

end

end VG.Proof.Dsa.Arm.Gen
