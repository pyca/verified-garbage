module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 on PPC64LE: the two sides of the verification equation

With `pk`, the signature and the challenge in `r29`–`r31` (`VCtx`), `A` and
`R` decoded into the tables at 7776 and 7904: `[S] B` into the table at 8032
(`verifyLhs_ok`), then `[k] A + R` and its comparison with `[S] B`
(`verifyRhs_ok`, `pointEqual_ok`), the result in `r17`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

/-- **The comparison** of the points in slots 0–3 and 4–7, into `r17`. -/
theorem pointEqual_ok {s : State} (hc : Ctx8 b s) :
    WP isa Impl.Ed25519.PPC64LE.pointEqual s fun t => DKeep b s t ∧
      t.gpr .r17 = if Spec.Ed25519.pointEqual (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7)
        then 1 else 0 := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx) fun s1 ⟨k1, e1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (fieldEqual_ok hc1.ctx 8 9) fun s2 ⟨k2, e2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  have x8 : env s1.mem b 8 = env s.mem b 0 * env s.mem b 6 := by rw [e1]; rfl
  have x9 : env s1.mem b 9 = env s.mem b 4 * env s.mem b 2 := by rw [e1]; rfl
  have x10 : env s2.mem b 10 = env s.mem b 1 * env s.mem b 6 := by rw [e2, e1]; rfl
  have x11 : env s2.mem b 11 = env s.mem b 5 * env s.mem b 2 := by rw [e2, e1]; rfl
  rw [x8, x9] at h2
  have hk2 : DKeep b s s2 := DKeep.of_keep (k1.trans k2)
  unfold Spec.Ed25519.pointEqual
  simp only [point]
  refine WP.ite (s2.gpr .r5 == 0) (eval_zero s2 .r5) (fun h => ?_) (fun h => ?_)
  · have ha := h2.mp (beq_iff_eq.mp h)
    refine WP.seq (WP.mono (fieldEqual_ok hc2.ctx 10 11) fun s3 ⟨k3, _, h3⟩ => ?_)
    rw [x10, x11] at h3
    have hk3 : DKeep b s s3 := hk2.trans (DKeep.of_keep k3)
    refine WP.ite (s3.gpr .r5 == 0) (eval_zero s3 .r5) (fun h' => ?_) (fun h' => ?_)
    · refine wp_li (by decide) fun t u => WP.block_nil
        ⟨hk3.trans ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, ?_⟩
      rw [u.gpr]
      simp [ha, h3.mp (beq_iff_eq.mp h')]
    · have hb : ¬ env s.mem b 1 * env s.mem b 6 = env s.mem b 5 * env s.mem b 2 :=
        fun he => absurd (beq_iff_eq.mpr (h3.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok s3) fun t ⟨kt, _, dt⟩ => ⟨hk3.trans kt, ?_⟩
      rw [show t.gpr .r17 = 0 from dt]
      simp [ha, hb]
  · have hb : ¬ env s.mem b 0 * env s.mem b 6 = env s.mem b 4 * env s.mem b 2 :=
      fun he => absurd (beq_iff_eq.mpr (h2.mpr he)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk2.trans kt, ?_⟩
    rw [show t.gpr .r17 = 0 from dt]
    simp [hb]

end

/-- The verification's inputs: `pk`, the signature and the challenge, readable at `r29`–`r31`,
outside the working space at `r6`. -/
structure VCtx (b pk sig ch : Addr) (s : State) : Prop where
  ctx : Ctx8 b s
  r29 : s.gpr .r29 = pk
  r30 : s.gpr .r30 = sig
  r31 : s.gpr .r31 = ch
  pkR : (⟨pk, 32⟩ : Region) ∈ s.rd
  sigR : (⟨sig, 64⟩ : Region) ∈ s.rd
  chR : (⟨ch, 64⟩ : Region) ∈ s.rd
  pkD : (⟨pk, 32⟩ : Region).Disjoint ⟨b, 8192⟩
  sigD : (⟨sig, 64⟩ : Region).Disjoint ⟨b, 8192⟩
  chD : (⟨ch, 64⟩ : Region).Disjoint ⟨b, 8192⟩

section
variable {b pk sig ch : Addr}

theorem VCtx.of_rest {s t : State} {R : List Reg} (h : VCtx b pk sig ch s) (hr : Rest R s t)
    (hw : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) : VCtx b pk sig ch t where
  ctx := h.ctx.of_rest hr (hw _ (by simp))
  r29 := by rw [hr.gpr _ (hw _ (by simp)), h.r29]
  r30 := by rw [hr.gpr _ (hw _ (by simp)), h.r30]
  r31 := by rw [hr.gpr _ (hw _ (by simp)), h.r31]
  pkR := by rw [hr.rd]; exact h.pkR
  sigR := by rw [hr.rd]; exact h.sigR
  chR := by rw [hr.rd]; exact h.chR
  pkD := h.pkD
  sigD := h.sigD
  chD := h.chD

/-- Bytes outside the working space, through a frame within it. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : n ≤ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
  intro i hi
  exact bytes_ws hf hs hd hn (List.mem_range.mp hi)

theorem table_sub {o : Nat} (ho : o + 128 ≤ 8192) : Region.Sub ⟨b + BitVec.ofNat 64 o, 128⟩ ⟨b, 8192⟩ :=
  Offset.sub_base b ho

/-- What `[S] P` writes, with a table entry. -/
abbrev sideW (b : Addr) (o : Nat) : List Region := ⟨b + BitVec.ofNat 64 o, 128⟩ :: mulW b

theorem sideW_sub {o : Nat} (ho : o + 128 ≤ 8192) : ∀ r ∈ sideW b o, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact table_sub ho
  · exact mulW_sub r hr

/-- The registers `[S] P` writes. -/
abbrev sideR : List Reg := .r19 :: .r7 :: batchR

/-- **`[S] B`**, for `S` the signature's second half, into the table at 8032. -/
theorem verifyLhs_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa verifyLhs s fun t =>
      Rest sideR s t ∧ Frame (sideW b 8032) s.mem t.mem ∧
      tableAt t.mem b 8032 = Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32))
        Spec.Ed25519.basePoint := by
  unfold verifyLhs
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have e14 : s1.gpr .r14 = sig + BitVec.ofNat 64 32 := by rw [u1.gpr, h.r30]
  have h1 : VCtx b pk sig ch s1 := h.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  unfold constPoint
  refine WP.seq (WP.mono (fieldCode_ok _ h1.ctx.ctx) fun s2 ⟨k2, e2⟩ => ?_)
  have p2 := (env_constPoint (env s1.mem b) Spec.Ed25519.basePoint).1
  rw [← e2] at p2
  have h2 : VCtx b pk sig ch s2 := h1.of_rest k2.rest (by decide)
  have hpd : (⟨sig + BitVec.ofNat 64 32, 2 * 16⟩ : Region).Disjoint ⟨b, 8192⟩ :=
    h.sigD.sub_left (Offset.sub_base sig (by decide))
  refine WP.seq (WP.mono (pointFromScalar_ok h2.ctx (count := 16) (by decide) (by decide)
    (p := sig + BitVec.ofNat 64 32) (by rw [k2.rest.gpr _ (by decide), e14])
    (fun i hi => by
      rw [Offset.add_add]
      exact in_base (List.mem_append_left _ h2.sigR) (by omega_arith) (by omega_arith)) hpd)
    fun s3 ⟨r3, f3, p3, _⟩ => ?_)
  have hb2 : bytesAt s2.mem (sig + BitVec.ofNat 64 32) (2 * 16) = bytesAt s.mem (sig + BitVec.ofNat 64 32) 32 := by
    rw [← u1.mem]
    exact bytesAt_ws k2.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith))
      hpd (by decide)
  rw [hb2, p2] at p3
  have hc3 : Ctx8 b s3 := h2.ctx.of_rest r3 (by decide)
  unfold pointTableWrite scratchAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s4 u4 => ?_
  refine WP.mono (pointToTable_ok (hc3.of_rest (u4.rest (ws := [.r14]) (by decide)) (by decide)) (o := 8032)
    (by rw [u4.gpr, hc3.r6]) (by decide) (by decide)) fun t ⟨rt, ft, tt⟩ => ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((k2.rest.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (rt.mono (by decide)))))
  · rw [← u1.mem]
    have ft' : Frame [⟨b + BitVec.ofNat 64 8032, 128⟩] s3.mem t.mem := by rw [← u4.mem]; exact ft
    exact (k2.frame.mono (by simp)).trans ((f3.mono (by simp)).trans (ft'.mono (by simp)))
  · rw [tt, u4.mem, p3]

/-- What `verifyRhs` runs before the comparison. -/
def verifyRhsPre : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ ([.addi .r14 .r31 0] : List Instr))) (.seq (pointFromScalar 32) verifyCombine)

/-- **`[k] A + R`** into slots 4–7 and `[S] B` into slots 0–3, from the tables at 7776, 7904 and 8032. -/
theorem verifyRhsPre_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa verifyRhsPre s fun t => Rest sideR s t ∧ Frame (sideW b 8032) s.mem t.mem ∧ Ctx8 b t ∧
      point (env t.mem b) 0 1 2 3 = tableAt s.mem b 8032 ∧
      point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tableAt s.mem b 7904)
        (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem ch 64)) (tableAt s.mem b 7776)) := by
  unfold verifyRhsPre pointTableRead scratchAddr
  simp only [List.singleton_append]
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => ?_)
  have hc1 : Ctx8 b s1 := h.ctx.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.append (pointFromTable_ok hc1 (o := 7776) (by rw [u1.gpr, h.ctx.r6]) (by decide) (by decide))
    fun s2 ⟨r2, f2, p2, _⟩ => ?_
  refine wp_addi (by decide) (by decide) fun s3 u3 => WP.block_nil ?_
  have r13 : Rest [.r7, .r14] s s3 := (u1.rest (by decide)).trans ((r2.mono (by decide)).trans (u3.rest (by decide)))
  have h3 : VCtx b pk sig ch s3 := h.of_rest r13 (by decide)
  have m3 : s3.mem = s2.mem := u3.mem
  have hF3 : Frame [FA b] s.mem s3.mem := by
    rw [m3, ← u1.mem]; exact f2.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩
  have hk3 : ∀ o, 1024 ≤ o → o + 128 ≤ 8192 → tableAt s3.mem b o = tableAt s.mem b o := fun o ho ho' => by
    rw [← u1.mem, m3]
    exact tableAt_keep f2 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have hpd : (⟨ch, 2 * 32⟩ : Region).Disjoint ⟨b, 8192⟩ := h.chD
  refine WP.seq (WP.mono (pointFromScalar_ok h3.ctx (count := 32) (by decide) (by decide) (p := ch)
    (by rw [u3.gpr, BitVec.add_zero, r2.gpr _ (by decide), u1.other _ (by decide), h.r31])
    (fun i hi => in_base (List.mem_append_left _ h3.chR) (by omega_arith) (by omega_arith)) hpd)
    fun s4 ⟨r4, f4, p4, d4⟩ => ?_)
  have hb3 : bytesAt s3.mem ch (2 * 32) = bytesAt s.mem ch 64 :=
    bytesAt_ws hF3 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)) hpd (by decide)
  rw [hb3, m3, p2, u1.mem] at p4
  have hc4 : Ctx8 b s4 := h3.ctx.of_rest r4 (by decide)
  have hT4 : ∀ o, 7776 ≤ o → o + 128 ≤ 8192 → tableAt s4.mem b o = tableAt s.mem b o := fun o ho ho' => by
    rw [← hk3 o (by omega_arith) ho']
    exact tableAt_keep f4 fun r hr => by
      have hB : BITSB = 32 := rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  -- `[k] A` to slots 4–7, `R` to 0–3, their sum, then it to 4–7 and `[S] B` to 0–3.
  unfold verifyCombine copyPointToQ
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc4.ctx) fun s5 ⟨k5, e5⟩ => ?_)
  obtain ⟨q4, _, qk⟩ := env_copyPointToQ (env s4.mem b)
  rw [← e5] at q4 qk
  have hc5 : Ctx8 b s5 := hc4.of_keep k5
  refine WP.seq ?_
  unfold pointTableRead scratchAddr
  simp only [List.singleton_append]
  refine wp_addi (by decide) (by decide) fun s6 u6 => ?_
  have hc6 : Ctx8 b s6 := hc5.of_rest (u6.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.mono (pointFromTable_ok hc6 (o := 7904) (by rw [u6.gpr, hc5.r6]) (by decide) (by decide))
    fun s7 ⟨r7, f7, p7, k7⟩ => ?_
  rw [u6.mem, tableAt_keep k5.frame (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
    hT4 7904 (by decide) (by decide)] at p7
  have hc7 : Ctx8 b s7 := hc6.of_rest r7 (by decide)
  have hd7 : env s7.mem b 16 = Spec.Ed25519.d := by rw [k7 16 (by decide), u6.mem, qk 16 (by decide), d4]
  have hq7 : point (env s7.mem b) 4 5 6 7 = point (env s4.mem b) 0 1 2 3 := by
    simp only [point, k7 4 (by decide), k7 5 (by decide), k7 6 (by decide), k7 7 (by decide), u6.mem]
    exact q4
  refine WP.seq (WP.mono (addCall_ok hc7 hd7) fun s8 ⟨k8, p8, _⟩ => ?_)
  rw [p7, hq7, p4] at p8
  have hc8 : Ctx8 b s8 := hc7.of_keep k8
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc8.ctx) fun s9 ⟨k9, e9⟩ => ?_)
  obtain ⟨q9, _, _⟩ := env_copyPointToQ (env s8.mem b)
  rw [← e9, p8] at q9
  have hc9 : Ctx8 b s9 := hc8.of_keep k9
  refine wp_addi (by decide) (by decide) fun s10 u10 => ?_
  have hc10 : Ctx8 b s10 := hc9.of_rest (u10.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.mono (pointFromTable_ok hc10 (o := 8032) (by rw [u10.gpr, hc9.r6]) (by decide) (by decide))
    fun s11 ⟨r11, f11, p11, k11⟩ => ?_
  have hFA : Frame [FA b] s7.mem s9.mem := k8.frame.trans k9.frame
  have hT9 : tableAt s9.mem b 8032 = tableAt s.mem b 8032 := by
    rw [tableAt_keep hFA (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
      tableAt_keep f7 (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
      u6.mem, tableAt_keep k5.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
      hT4 8032 (by decide) (by decide)]
  rw [u10.mem, hT9] at p11
  have hq11 : point (env s11.mem b) 4 5 6 7 = point (env s9.mem b) 4 5 6 7 := by
    simp only [point, k11 4 (by decide), k11 5 (by decide), k11 6 (by decide), k11 7 (by decide), u10.mem]
  have hc11 : Ctx8 b s11 := hc10.of_rest r11 (by decide)
  refine ⟨?_, ?_, hc11, p11, by rw [hq11, q9]⟩
  · exact (r13.mono (by decide)).trans ((r4.mono (by decide)).trans ((k5.rest.mono (by decide)).trans
      ((u6.rest (by decide)).trans ((r7.mono (by decide)).trans ((k8.rest.mono (by decide)).trans
        ((k9.rest.mono (by decide)).trans ((u10.rest (by decide)).trans (r11.mono (by decide)))))))))
  · have fs : ∀ r ∈ [FA b], r ∈ sideW b 8032 := by simp
    have fs' : ∀ r ∈ [(⟨b + BitVec.ofNat 64 64, 128⟩ : Region)], ∃ r' ∈ sideW b 8032, Region.Sub r r' :=
      fun r hr => ⟨FA b, by simp, by rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩
    have fa : Frame (sideW b 8032) s.mem s4.mem := (hF3.mono fs).trans (f4.mono (by simp))
    have fb : Frame (sideW b 8032) s4.mem s6.mem := by rw [u6.mem]; exact k5.frame.mono fs
    have fc : Frame (sideW b 8032) s6.mem s9.mem := (f7.sub fs').trans (hFA.mono fs)
    have fd : Frame (sideW b 8032) s9.mem s11.mem := by rw [← u10.mem]; exact f11.sub fs'
    exact fa.trans (fb.trans (fc.trans fd))

theorem verifyRhsPre_ok' {s : State} (h : VCtx b pk sig ch s) :
    WP isa (.seq (.seq (.block (pointTableRead 7776 ++ ([.addi .r14 .r31 0] : List Instr))) (pointFromScalar 32)) verifyCombine) s
      fun t => Rest sideR s t ∧ Frame (sideW b 8032) s.mem t.mem ∧ Ctx8 b t ∧
        point (env t.mem b) 0 1 2 3 = tableAt s.mem b 8032 ∧
        point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tableAt s.mem b 7904)
          (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem ch 64)) (tableAt s.mem b 7776)) := by
  have e := verifyRhsPre_ok h
  unfold verifyRhsPre at e
  exact WP.assoc' e

/-- **`[k] A + R`** and its comparison with `[S] B`, from the tables at 7776, 7904 and 8032. -/
theorem verifyRhs_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa verifyRhs s fun t => Rest (.r17 :: sideR) s t ∧
      Frame (sideW b 8032) s.mem t.mem ∧
      t.gpr .r17 = if Spec.Ed25519.pointEqual (tableAt s.mem b 8032)
        (Spec.Ed25519.pointAdd (tableAt s.mem b 7904)
          (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem ch 64)) (tableAt s.mem b 7776))) then 1 else 0 := by
  unfold verifyRhs
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (verifyRhsPre_ok h)) fun u ⟨ru, fu, cu, pu, qu⟩ =>
    WP.mono (pointEqual_ok cu) fun t ⟨kt, rt⟩ => ⟨(ru.mono (by decide)).trans (kt.rest.mono (by decide)),
      fu.trans (kt.frame.mono (by simp)), by rw [rt, pu, qu]⟩)))

end

end VG.Proof.Ed25519.PPC64LE
