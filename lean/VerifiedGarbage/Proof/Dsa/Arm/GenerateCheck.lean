module

public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCompute
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Proof.Dsa.Arm.Session
public import VerifiedGarbage.Proof.Dsa.Arm.Shape

/-!
# DSA domain checks on 32-bit ARM: correctness

`genDispatch_ok` follows the public widths to their code, as the signer's
dispatch does; `check_correct`: from `checkArm`'s precondition,
`vg_dsa_check_parameters` returns whether `Spec.Dsa.checkParametersBytes`
accepts the domain, and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest eval_eq wp_mov op2_imm)

theorem genDispatch_ok (sized : Nat → Nat → Prog isa) (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Ws s base size) (hz : 120 ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp : (hdr base s 100).toNat = pLen) (hq : (hdr base s 104).toNat = qLen)
    (body : ∀ t, Rest [.r4, .r5] s t → t.mem = s.mem → WP isa (sized pLen qLen) t Q) :
    WP isa (Generate.dispatch sized widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold Generate.dispatch
    refine WP.seq (WP.mono (widthMatch_ok hs hz hp hq B.1 B.2) fun t ⟨Z, R, M⟩ => ?_)
    refine WP.ite t.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (Z ▸ ht)
      rw [← Both.1, ← Both.2]
      exact body t R M
    · have Both : ¬ (pLen = wp ∧ qLen = wq) := of_decide_eq_false (Z ▸ hf)
      refine ih (hs.of_rest R (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M]; exact hp) (by simp only [hdr, M]; exact hq)
        fun u Ru Mu => body u (R.trans Ru) (Mu.trans M)

theorem genWidths_mem {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ Generate.widths := widths_mem h

/-- A domain p||q||g, by its components. -/
theorem paramsBytes_at (mem : Mem) (ptr : Addr) {pLen qLen total : Nat} (h : 2 * pLen + qLen ≤ total) :
    Spec.Dsa.paramsBytes pLen qLen (Spec.Rsa.bytesAt mem ptr total) =
      ⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem ptr pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩ := by
  have h0 := VG.Proof.Dsa.bytesAt_slice mem ptr (offset := 0) (len := pLen) (by omega : 0 + pLen ≤ total)
  simp only [List.drop_zero, BitVec.add_zero] at h0
  rw [VG.Proof.Dsa.paramsBytes_eq, h0, VG.Proof.Dsa.bytesAt_slice mem ptr (by omega : pLen + qLen ≤ total),
    VG.Proof.Dsa.bytesAt_slice mem ptr (by omega : (pLen + qLen) + pLen ≤ total)]

/-- The domain check, by the checks the code makes. -/
theorem checkParametersBytes_iff {pLen qLen : Nat} {params : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) :
    Spec.Dsa.checkParametersBytes pLen qLen params = true ↔
      shapeValid (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q ∧
      domainChecks (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q
        (Spec.Dsa.paramsBytes pLen qLen params).g := by
  rw [VG.Proof.Dsa.checkParametersBytes_eq hl hpl]
  simp only [VG.Proof.Dsa.powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, shapeValid,
    domainChecks]
  exact ⟨fun ⟨⟨a, b, c⟩, d, e, f, _⟩ => ⟨⟨a, c, b⟩, ⟨f, e⟩, d⟩, fun ⟨⟨a, c, b⟩, ⟨f, e⟩, d⟩ => ⟨⟨a, b, c⟩, d, e, f, f⟩⟩

/-- The domain's components, at a state with the environment of the check. -/
theorem checkIn {s t : State} {base : Addr} {size : Nat} (h : checkPre s) (hb : State.addr (arg s 0) = base)
    (hsz : (arg s 1).toNat * 8 = size) (E : Env s base size (checkFields s) t) :
    Input t base size (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, dPS, _, fP, _, hv, hr1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have pr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (s.gpr .r2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp))
    pr fP (by omega) (.inr rfl) dPS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ pr fP (by omega)
      (.inl (by omega)) dPS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ pr fP (by omega)
      (.inl (by omega)) dPS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans (cg (xs := [s.gpr .r2]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))

theorem check_correct {s : State} (h : checkPre s) :
    WP isa Generate.checkParameters s fun t => abiPreserved s t ∧ checkArm.post s t := by
  obtain ⟨hsp, hrd, hwr, dPS, dSA, fP, fS, hv, hr1, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Generate.checkParameters, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (checkEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega)
  have fok := checkFields_ok s
  refine WP.seq (genDispatch_ok Generate.checkSized _ E₀.ws (by omega) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by omega
  obtain ⟨Ip₁, Iq₁, Ig₁⟩ := checkIn h rfl rfl E₁
  -- The specification's components.
  have hpl : (checkParams s).length = 2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat := by
    simp only [checkParams, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1
  have PB := paramsBytes_at s.mem (State.addr (s.gpr .r0)) (pLen := (s.gpr .r2).toNat) (qLen := (s.gpr .r3).toNat)
    (total := (s.gpr .r1).toNat) (by omega)
  have spec := checkParametersBytes_iff hv hpl
  simp only [checkParams] at spec
  rw [PB] at spec
  dsimp only at spec
  unfold Generate.checkSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    have nv := of_decide_eq_true (Z ▸ ht)
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 _ => ⟨A, ?_⟩
    have : checkRes s = false := by
      by_contra hc
      exact nv (spec.mp (Bool.not_eq_false _ ▸ hc)).1
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if checkRes s = true then 1 else 0
    rw [this, BitVec.setWidth_append_eq_right, r0, v₃.gpr]
    rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig⟩ := checkIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have hm : maskW (State.addr (arg s 0)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · contradiction
    refine WP.seq (WP.mono (parameters_ok ⟨E₂.ws, by omega, wp, wq, qp, q32⟩ Ip Iq Ig hP hPo hQ hQo)
      fun t₃ ⟨F₃, Rn₃⟩ => ?_)
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega)
    rw [hm, BitVec.allOnes_and] at F₃
    refine WP.mono (result_ok E₃.ws (by omega) _ F₃) fun t₄ ⟨r0₄, R₄, M₄⟩ => ?_
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega) (fun i hi => by rw [M₄]; exact E₃.saved i hi)
      (R₄.sp.trans E₃.sp) fun u A r0 _ => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if checkRes s = true then 1 else 0
    rw [status_toNat (r0.trans r0₄)]
    by_cases hc : checkRes s = true
    · have d := (spec.mp hc).2
      rw [ite_eq_left hc]
      split
      · rfl
      · contradiction
    · have d : ¬ domainChecks _ _ _ := fun d => hc (spec.mpr ⟨valid, d⟩)
      rw [ite_eq_right hc]
      split
      · contradiction
      · rfl

end VG.Proof.Dsa.Arm
