module

import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateWrite
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Zeroize.Common
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCompute
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
public import VerifiedGarbage.Proof.Dsa.Arm.Session
import Mathlib.Basic.Logic.Basic
import Mathlib.Logic.Function.Basic

/-!
# DSA key derivation on 32-bit ARM: correctness

`derive_correct`: from `deriveArm`'s precondition, `vg_dsa_derive_key`
returns the status of `Spec.Dsa.deriveKeyBytes` and writes its key (or
zeros), and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest eval_eq wp_mov wp_movw wp_dp op2_imm op2_reg dpVal)

/-- Key derivation, by the checks the code makes. -/
theorem deriveKeyBytes_iff {pLen qLen : Nat} {params x : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) (hxl : x.length = qLen) :
    Spec.Dsa.deriveKeyBytes pLen qLen params x =
      if shapeValid (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q ∧
          deriveChecks (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q
            (Spec.Dsa.paramsBytes pLen qLen params).g (Spec.Dsa.decodeBE x)
      then some (params ++ Spec.Dsa.encodeBE pLen ((Spec.Dsa.paramsBytes pLen qLen params).g ^
        Spec.Dsa.decodeBE x % (Spec.Dsa.paramsBytes pLen qLen params).p) ++ x)
      else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq hl hpl hxl]
  simp only [VG.Proof.Dsa.powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  refine if_congr ⟨fun ⟨⟨a, b, c⟩, d, e, f, g, h⟩ => ⟨⟨a, c, b⟩, ⟨⟨g, e⟩, d⟩, h, f⟩,
    fun ⟨⟨a, c, b⟩, ⟨⟨g, e⟩, d⟩, h, f⟩ => ⟨⟨a, b, c⟩, d, e, f, g, h⟩⟩ rfl rfl

/-- The derivation's failure: zeros in the output and 0 in `r0`. -/
theorem deriveFailure_ok {s : State} {base : Addr} {size pLen qLen : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (hL : 3 * pLen + 2 * qLen < 2 ^ 16) (h0 : 0 < 3 * pLen + 2 * qLen)
    (fit : (pointerValue base s (.input .out)).toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (wr : ∀ i < 3 * pLen + 2 * qLen,
      InRegions s.wr (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 i) 1) :
    WP isa (Generate.deriveFailure pLen qLen) s fun t =>
      t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (3 * pLen + 2 * qLen) =
        List.replicate (3 * pLen + 2 * qLen) 0 ∧
      Rest [.r0, .r4, .r11, .lr] s t ∧
      Outside (State.addr (pointerValue base s (.input .out))) 0 (3 * pLen + 2 * qLen) s.mem t.mem := by
  simp only [Generate.deriveFailure, Core.sequence, List.foldr]
  refine WP.seq (wp_ldr12 hs (d := 96) (by decide) (by omega_arith) fun u₁ v₁ => ?_)
  refine wp_movw fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => wp_mov (op2_imm (by decide)) fun u₄ v₄ => WP.block_nil ?_
  have out : u₄.gpr .r11 = pointerValue base s (.input .out) := by
    rw [v₄.other .r11 (by decide), v₃.other .r11 (by decide), v₂.other .r11 (by decide), v₁.gpr]; rfl
  have lr : u₄.gpr .lr = pointerValue base s (.input .out) + BitVec.ofNat 32 (3 * pLen + 2 * qLen) := by
    rw [v₄.other .lr (by decide), v₃.gpr, dpVal, v₂.gpr, v₂.other .r11 (by decide), v₁.gpr, movw_ofNat hL]
    rfl
  have R₄ : Rest [.r4, .r11, .lr] s u₄ :=
    (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans (v₄.rest (by decide))
  have M₄ : u₄.mem = s.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.seq (WP.mono (failureLoop_ok h0 fit (by omega_arith) out lr v₄.gpr
    (fun i hi => by rw [R₄.wr]; exact wr i hi)) fun t ⟨B, Ot, Rt⟩ => ?_)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t' v => WP.block_nil (WP.block_nil ⟨v.gpr, ?_, ?_, ?_⟩))
  · rw [v.mem]; exact VG.Proof.Zeroize.prefix_spec B
  · exact ((R₄.mono (by decide)).trans (Rt.mono (by decide))).trans (v.rest (by decide))
  · rw [v.mem, ← M₄]; exact Ot

/-- The derivation's inputs, at a state with its environment. -/
theorem deriveIn {s t : State} {base : Addr} {size : Nat} (h : derivePre s) (hb : State.addr (arg s 3) = base)
    (hsz : (arg s 4).toNat * 8 = size) (E : Env s base size (deriveFields s) t) :
    Input t base size (.input .p) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)) ∧
      Input t base size (.input .q) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
          (arg s 2).toNat)) ∧
      Input t base size (.input .g) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .nonce) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, dPS, dXS, _, _, fP, fX, _, hv, _, hr3, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have pr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have xr : (⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (arg s 0).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r2) (by simp))
    pr fP (by omega_arith) (.inr rfl) dPS hz
  rw [BitVec.add_zero] at ip
  have ix := input_of E (p := .input .nonce) (by decide : Impl.Dsa.Layout.Field.nonce ≠ .mask) (o := 0)
    (len := (arg s 2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 88) (v := arg s 1) (by simp))
    xr fX (by omega_arith) (.inr rfl) dXS hz
  rw [BitVec.add_zero] at ix
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r2) xs).trans (congrArg (fun n => s.gpr .r2 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz, ix⟩
  · exact (E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)).trans (cg (xs := [arg s 0]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2]) (by simp))

/-- A caller's buffer apart from the working space, through the environment. -/
theorem bytesIn_env {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {P : BitVec 32} {n : Nat} (hr : (⟨State.addr P, n⟩ : Region) ∈ s₀.rd) (hfit : P.toNat + n ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr P, n⟩ ⟨base, size⟩) :
    BytesIn t P (Spec.Rsa.bytesAt s₀.mem (State.addr P) n) := by
  have nw := E.ws.nowrap
  refine ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hfit, fun i hi => ?_,
    fun i hi => ?_⟩
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    rw [E.rd, E.wr]
    exact ⟨_, List.mem_append_left _ hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    refine E.mem _ (.inr ?_)
    rw [Nat.zero_add]
    refine ofs_apart hd.symm ?_
    have := ofs_off (State.addr P) (d := 0) (i := i) (by omega_arith)
    rw [off, BitVec.add_zero, Nat.zero_add] at this
    rw [this]; exact hi

theorem derive_correct {s : State} (h : derivePre s) :
    WP isa Generate.deriveKey s fun t => abiPreserved s t ∧ deriveArm.post s t := by
  obtain ⟨hsp, hrd, hwr, dOP, dOX, dOS, dOA, dPS, dXS, dSA, fO, fP, fX, fS, hv, hr1, hr3, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s 0).toNat ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Generate.deriveKey, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (deriveEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := deriveFields_ok s
  refine WP.seq (genDispatch_ok Generate.deriveSized _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := arg s 0) (by simp)]) (by rw [E₀.field (d := 104) (v := arg s 2) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 4).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -⟩ := deriveIn h rfl rfl E₁
  -- The specification's components.
  have hpl : (deriveParams s).length = 2 * (arg s 0).toNat + (arg s 2).toNat := by
    simp only [deriveParams, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3
  have hxl : (deriveX s).length = (arg s 2).toNat := by
    simp only [deriveX, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have PB := paramsBytes_at s.mem (State.addr (s.gpr .r2)) (pLen := (arg s 0).toNat) (qLen := (arg s 2).toNat)
    (total := (s.gpr .r3).toNat) (by omega_arith)
  have spec := deriveKeyBytes_iff hv hpl hxl
  simp only [deriveParams, deriveX] at spec
  rw [PB] at spec
  dsimp only at spec
  have SR : deriveRes s = _ := spec
  unfold Generate.deriveSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  have po : pointerValue (State.addr (arg s 3)) t₂ (.input .out) = s.gpr .r0 :=
    E₂.field (d := 96) (v := s.gpr .r0) (by simp)
  have ofit : (pointerValue (State.addr (arg s 3)) t₂ (.input .out)).toNat +
      (3 * (arg s 0).toNat + 2 * (arg s 2).toNat) ≤ 2 ^ 32 := by rw [po]; omega_arith
  have owr : ∀ i < 3 * (arg s 0).toNat + 2 * (arg s 2).toNat,
      InRegions t₂.wr (State.addr (pointerValue (State.addr (arg s 3)) t₂ (.input .out)) + BitVec.ofNat 64 i) 1 :=
    fun i hi => by
      rw [po, E₂.wr, hwr]
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dOS' : Region.Disjoint ⟨State.addr (s.gpr .r0), 3 * (arg s 0).toNat + 2 * (arg s 2).toNat⟩
      ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩ := hr1 ▸ dOS
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    have nv := of_decide_eq_true (Z ▸ ht)
    refine WP.mono (deriveFailure_ok E₂.ws (by omega_arith) (by omega_arith) (by omega_arith) ofit owr)
      fun t₃ ⟨Z₃, B₃, R₃, O₃⟩ => ?_
    rw [po] at B₃ O₃
    have none : deriveRes s = none := by rw [SR]; exact ite_eq_right fun h => nv h.1
    refine finish_ok (E₂.ws.of_rest R₃ (by decide)) (by omega_arith) (E₂.saved_outside O₃ dOS' (by omega_arith))
      (R₃.sp.trans E₂.sp) fun u A r0 Mu => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, none]; rfl
    · rw [Mu, hr1, B₃, none]; rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig, Ix⟩ := deriveIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have hm : maskW (State.addr (arg s 3)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · next hn => exact absurd valid hn
    refine WP.seq (WP.mono (deriveCompute_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Ix hP hPo hQ hQo)
      fun t₃ ⟨F₃, Y₃, Rn₃⟩ => ?_)
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    rw [hm, BitVec.allOnes_and] at F₃
    have po₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .out) = s.gpr .r0 :=
      E₃.field (d := 96) (v := s.gpr .r0) (by simp)
    have pp₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .p) = s.gpr .r2 :=
      E₃.field (d := 64) (v := s.gpr .r2) (by simp)
    have px₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .nonce) = arg s 1 :=
      E₃.field (d := 88) (v := arg s 1) (by simp)
    have K : KeySources t₃ (State.addr (arg s 3)) ((arg s 4).toNat * 8) (arg s 0).toNat (arg s 2).toNat
        (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (2 * (arg s 0).toNat + (arg s 2).toNat))
        (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) := by
      refine ⟨E₃.ws, by omega_arith, by omega_arith, q0, by omega_arith, by simp [Spec.Rsa.bytesAt], by simp [Spec.Rsa.bytesAt], ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [pp₃]
        exact bytesIn_env E₃ (by rw [hrd, ← hr3]; simp) (by omega_arith) (dPS.sub_left (Region.sub_prefix (by omega_arith)))
      · rw [px₃]
        exact bytesIn_env E₃ (by rw [hrd]; simp) fX dXS
      · rw [po₃]; omega_arith
      · intro i hi
        rw [po₃, E₃.wr, hwr]
        exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [pp₃, po₃]; exact (hr1 ▸ dOP.symm).sub_left (Region.sub_prefix (by omega_arith))
      · rw [px₃, po₃]; exact hr1 ▸ dOX.symm
      · rw [po₃]; exact dOS'.symm
    refine WP.mono (writeKey_ok K _ F₃ (by simp only [Impl.Dsa.Layout.t2]; omega_arith))
      fun t₄ ⟨r0₄, B₄, O₄, R₄⟩ => ?_
    rw [po₃] at B₄ O₄
    rw [Y₃] at B₄
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega_arith) (E₃.saved_outside O₄ dOS' (by omega_arith))
      (R₄.sp.trans E₃.sp) fun u A r0 Mu => ⟨A, ?_, ?_⟩
    · rw [status_toNat (r0.trans r0₄), SR]
      split_ifs with hc₁ hc₂ hc₂
      · rfl
      · exact absurd ⟨valid, hc₁⟩ hc₂
      · exact absurd hc₂.2 hc₁
      · rfl
    · rw [Mu, hr1, B₄, SR]
      split_ifs with hc₁ hc₂ hc₂
      · rw [Option.getD_some, hr3]
      · exact absurd ⟨valid, hc₁⟩ hc₂
      · exact absurd hc₂.2 hc₁
      · rfl

end VG.Proof.Dsa.Arm
