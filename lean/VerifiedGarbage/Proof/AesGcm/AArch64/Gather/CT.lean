import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the entry, the loads of
the call's arguments and of the return address are at the stack pointer;
the gathering loads the descriptors from where they are, and copies each
slice from and to the addresses they give, with branches on the number of
slices and their lengths (`gather_rel`, by the taint analysis from the
registers the correctness proof pins to the same values in both runs); and
the call is constant time by its callee's contract, whose public arguments
agree (`sealGather_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_ite ct_of eval_zero eval_nonzero)

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 64 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 16 hi; omega)

section
variable {e₁ e₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, e₁.mem (Src + BitVec.ofNat 64 j) = e₂.mem (Src + BitVec.ofNat 64 j))
include hd

theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 64 e₁.mem Src i = gatheredLen 64 e₂.mem Src i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 64 .u8 Src i (desc_agree hd hi)]

theorem desc_word {d : Nat} (h : d + 8 ≤ cnt * 16) :
    e₁.mem.readW (Src + BitVec.ofNat 64 d) 64 = e₂.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega)

theorem sb_agree {i : Nat} (hi : i < cnt) : sb e₁.mem Src i = sb e₂.mem Src i := desc_word hd (by omega)

theorem sl_agree {i : Nat} (hi : i < cnt) : sl e₁.mem Src i = sl e₂.mem Src i := by
  simp only [sl, Offset.add_ofNat_add_ofNat]
  rw [desc_word hd (by omega)]

variable (h₁ : GatherPre e₁ Src Dst cnt L) (h₂ : GatherPre e₂ Src Dst cnt L) (hsp : e₁.sp = e₂.sp)
include h₁ h₂ hsp

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subImm .x .x7 .x7 1])))
      (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt (i + 1) ∧ GInv e₂ u₂ Src Dst cnt (i + 1)) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subImm .x .x7 .x7 1]))) TT := by
    intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨g₁, g₂⟩ x₁ x₂
    refine rel_seq (rel_taint [.x6, .x7, .x11] (by rw [g₁.keep.sp, g₂.keep.sp, hsp])
      (by agree_tac [g₁.x6, g₂.x6, g₁.x7, g₂.x7, g₁.x11, g₂.x11, gl_agree hd (Nat.le_of_lt hi)])
      ⟨_, by taint_decide⟩) (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_)
      σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨rfl, rfl⟩ x₁ x₂
    exact rel_taint [.x6, .x7, .x11, .x12, .x13] (by rw [n₁.keep.sp, n₂.keep.sp, hsp])
      (by agree_tac [n₁.x6, n₂.x6, n₁.x7, n₂.x7, n₁.x11, n₂.x11, gl_agree hd (Nat.le_of_lt hi), n₁.x12, n₂.x12,
        sb_agree hd hi, n₁.x13, n₂.x13, sl_agree hd hi]) ⟨_, by taint_decide⟩
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ =>
    ⟨WP.seq (WP.mono (next_wp h₁ hi g₁) fun _ n => rest_wp h₁ hi n),
      WP.seq (WP.mono (next_wp h₂ hi g₂) fun _ n => rest_wp h₂ hi n)⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `gather`, in two runs. -/
theorem gather_rel : RelCT isa (Eq2 e₁ e₂) gather TT := by
  have hc := h₁.hcnt
  refine rel_ite (eval_zero h₁.x7 h₁.hcnt) (eval_zero h₂.x7 h₂.hcnt)
    (fun _ => by exact rel_taint [] hsp (by agree_tac []) ⟨_, by taint_decide⟩) (fun hf => ?_)
  have hpos : cnt ≠ 0 := by simpa using hf
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hsp hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨g₁, g₂⟩
    have ev₁ := eval_nonzero (r := .x7) (a := cnt - (i + 1)) g₁.x7 (by omega)
    have ev₂ := eval_nonzero (r := .x7) (a := cnt - (i + 1)) g₂.x7 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.fn) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, a1, a2, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 16 σ₁) (allocated 16 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (by rw [allocated_sp h₁, allocated_sp h₂, hB]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q6, ← q7, ← a0, ← a1] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega)
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q6, ← q7]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hB])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [] (by rw [hg₁.sp, hg₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, NL, Ad, AL, q0, q2, q3, q4, q5, hB]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁⟩ := hc₁.callGpr
  obtain ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r0₁, r1₁, r2₁, r3₁, r4₁, r5₁,
        r6₁, r7₁, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂, hc₁.sp, hc₂.sp, hB, hc₁.stackArg0 h₁,
        hc₂.stackArg0 h₂, q0, q1, q2, q3, q4, q5, Dst, Tg, a0, a1, a2, and_self])
    (called_wp F h₁ hc₁) (called_wp F h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64.Gather
