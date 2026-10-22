module

import VerifiedGarbage.Proof.Dsa.Arm.GenerateTrace
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.RsaPss

/-!
# DSA key derivation on 32-bit ARM: constant time

Two runs whose public data agree (`deriveArm.pub`: the arguments, the
domain's bytes and whether derivation succeeds) leak the same trace: the
shape check and the arithmetic read their operands through the same
pointers (`GenerateTrace.lean`), and the key is copied out through pointers
loaded before the first store, under the flag, which only masks the bytes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-- The loads that start the key's output. -/
theorem writeHead_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size) :
    WP isa (.block [.ldr .r3 .r12 (Layout.field .mask), .ldr .r10 .r12 (Layout.field .out),
      .ldr .r1 .r12 (Layout.field .p), .ldr .r4 .r12 (Layout.field .nonce)]) s fun t =>
      t.gpr .r10 = hdr base s 96 ∧ t.gpr .r1 = hdr base s 64 ∧ t.gpr .r4 = hdr base s 88 ∧ Ws t base size := by
  refine wp_ldr12 hs (d := 116) (by decide) (by omega) fun u₁ v₁ => ?_
  refine wp_ldr12 (hs.of_upd v₁ (by decide)) (d := 96) (by decide) (by omega) fun u₂ v₂ => ?_
  refine wp_ldr12 ((hs.of_upd v₁ (by decide)).of_upd v₂ (by decide)) (d := 64) (by decide) (by omega)
    fun u₃ v₃ => ?_
  refine wp_ldr12 (((hs.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)) (d := 88) (by decide)
    (by omega) fun u₄ v₄ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr]; simp only [hdr, v₁.mem]
  · rw [v₄.other _ (by decide), v₃.gpr]; simp only [hdr, v₂.mem, v₁.mem]
  · rw [v₄.gpr]; simp only [hdr, v₃.mem, v₂.mem, v₁.mem]
  · exact (((hs.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)

/-- The key's output: its pointers are the same in both runs. -/
theorem writeKey_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (pLen qLen : Nat)
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (ho : hdr base s₁ 96 = hdr base s₂ 96) (hp : hdr base s₁ 64 = hdr base s₂ 64)
    (hx : hdr base s₁ 88 = hdr base s₂ 88) :
    SameTrace isa (.seq (Generate.writeKey pLen qLen) Tail) s₁ s₂ := by
  simp only [Generate.writeKey, Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (block_relCT_T0 _ rfl) (agree0 h₁ h₂))
    (writeHead_ok h₁ hz₁) (writeHead_ok h₂ hz₂) fun u₁ u₂ ⟨O₁, P₁, X₁, w₁⟩ ⟨O₂, P₂, X₂, w₂⟩ => ?_)
  refine SameTrace.of_relCT (erased_relCT (τ := Taint.ofRegs [.r12, .r10, .r1, .r4]) (σ := Taint.ofRegs [])
    (c₀ := .seq (Core.sequence [Generate.copyFrom 0, .block (ptr .r1 t2), Generate.copyFrom 0,
      .block [.mov .r1 (.reg .r4)], Generate.copyFrom 0, .block SignVerify.result]) Tail)
    (VG.Taint.hintOf taint (Taint.ofRegs [.r12, .r10, .r1, .r4])
      (.seq (Core.sequence [Generate.copyFrom 0, .block (ptr .r1 t2), Generate.copyFrom 0,
        .block [.mov .r1 (.reg .r4)], Generate.copyFrom 0, .block SignVerify.result]) Tail))
    (by rfl) (Taint.noBase_ofRegs _) (by rfl)) ?_
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ws.r12_eq w₁ w₂
  · rw [O₁, O₂, ho]
  · rw [P₁, P₂, hp]
  · rw [X₁, X₂, hx]

theorem deriveFailureHead_ok {s : State} {base : Addr} {size L : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (hL : L < 2 ^ 16) :
    WP isa (.block [.ldr .r11 .r12 (Layout.field .out), .movw .r4 (BitVec.ofNat 16 L),
      .dp .add .lr .r11 (.reg .r4), .mov .r4 (.imm 0)]) s fun t =>
      t.gpr .r11 = hdr base s 96 ∧ t.gpr .lr = hdr base s 96 + BitVec.ofNat 32 L ∧ Ws t base size := by
  refine wp_ldr12 hs (d := 96) (by decide) (by omega) fun u₁ v₁ => ?_
  refine VG.Proof.X25519.Arm.wp_movw fun u₂ v₂ =>
    VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u₃ v₃ =>
    VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u₄ v₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v₄.other .r11 (by decide), v₃.other .r11 (by decide), v₂.other .r11 (by decide), v₁.gpr]
  · rw [v₄.other .lr (by decide), v₃.gpr, VG.Proof.X25519.Arm.dpVal, v₂.gpr, v₂.other .r11 (by decide), v₁.gpr,
      movw_ofNat hL]
  · exact (((hs.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)

theorem deriveFailure_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (pLen qLen : Nat)
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (hL : 3 * pLen + 2 * qLen < 2 ^ 16) (ho : hdr base s₁ 96 = hdr base s₂ 96) :
    SameTrace isa (.seq (Generate.deriveFailure pLen qLen) Tail) s₁ s₂ := by
  simp only [Generate.deriveFailure, Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (erased_relCT (σ := T0)
      (c₀ := .block [.ldr .r11 .r12 0, .movw .r4 0, .dp .add .lr .r11 (.reg .r4), .mov .r4 (.imm 0)])
      (VG.Taint.hintOf taint T0 (.block [.ldr .r11 .r12 0, .movw .r4 0, .dp .add .lr .r11 (.reg .r4),
        .mov .r4 (.imm 0)])) (by rfl) (wsT_noBase _ _) (by rfl)) (agree0 h₁ h₂))
    (deriveFailureHead_ok h₁ hz₁ hL) (deriveFailureHead_ok h₂ hz₂ hL) fun u₁ u₂ ⟨A₁, L₁, w₁⟩ ⟨A₂, L₂, w₂⟩ => ?_)
  exact SameTrace.of_relCT ((relCT_of_check (σ := Taint.ofRegs []) (h := VG.Taint.hintOf taint (wsT true true)
    (.seq (.seq (.loop (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) .ne)
      (.seq (.block [.mov .r0 (.imm 0)]) (.block []))) Tail)) rfl).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (agreeWs true true w₁ w₂ (fun _ => by rw [A₁, A₂, ho]) (fun _ => by rw [L₁, L₂, ho]))

/-- Derivation's operands. -/
def deriveIns (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .nonce, qLen)]

/-- Their values. -/
def deriveVal (s : State) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
      (arg s 2).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)
  | .input .nonce => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
  | _ => 0

theorem deriveCtx {s t : State} {base : Addr} {size : Nat} (h : derivePre s)
    (hb : State.addr (arg s 3) = base) (hsz : (arg s 4).toNat * 8 = size)
    (E : Env s base size (deriveFields s) t) :
    Ctx base size (arg s 0).toNat (arg s 2).toNat (((arg s 0).toNat + 7) / 8) (((arg s 2).toNat + 7) / 8)
      (deriveIns (arg s 0).toNat (arg s 2).toNat) (deriveVal s) t := by
  have hv := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig, Ix⟩ := deriveIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [deriveIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Ix

theorem derivePtrs {s t : State} {base : Addr} {size pLen qLen : Nat} (E : Env s base size (deriveFields s) t) :
    ∀ i ∈ deriveIns pLen qLen, pointerValue base t i.1 =
      match i.1 with
      | .input .p => s.gpr .r2
      | .input .q => s.gpr .r2 + arg s 0
      | .input .g => s.gpr .r2 + arg s 0 + arg s 2
      | _ => arg s 1 := by
  intro i hi
  simp only [deriveIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r2) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)
  · exact E.field (d := 88) (v := arg s 1) (by simp)

/-- The domain's bytes at an offset, the same in two runs that leak the same. -/
theorem derive_bytes {s₁ s₂ : State} (hl : deriveLeak s₁ = deriveLeak s₂)
    (hr2 : s₁.gpr .r2 = s₂.gpr .r2) (hr3 : s₁.gpr .r3 = s₂.gpr .r3) {o l : Nat}
    (hol : o + l ≤ (s₁.gpr .r3).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 o) l := by
  simp only [deriveLeak, deriveParams] at hl
  rw [← hr2, ← hr3] at hl
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp
    (List.append_inj hl (by simp [Spec.Rsa.bytesAt])).1
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem derive_constantTime : ConstantTime isa deriveArm.pre deriveArm.pub Generate.deriveKey := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
  obtain ⟨hsp, hl, hr0, hr1, hr2, hr3, ha⟩ := pub
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  obtain ⟨sp₁, _, wr₁, _, _, _, dOA₁, _, _, dSA₁, _, _, _, _, hv, _, hpl, hsw⟩ := id h₁
  obtain ⟨_, _, wr₂, _, _, _, dOA₂, _, _, dSA₂, _, _, _, _, _, _, _, _⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s₁ 0).toNat ≤ (arg s₁ 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 3) = State.addr (arg s₁ 3) := by rw [a3]
  have hz₂ : (arg s₂ 4).toNat * 8 = (arg s₁ 4).toNat * 8 := by rw [a4]
  simp only [Generate.deriveKey, Core.sequence, List.foldr]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 20 _ rfl) (agree_args (n := 5) hsp (by omega) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dOA₁.symm
        · exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dOA₂.symm
        · exact dSA₂.symm)))
    (WP.mono (deriveEntry_ok h₁) fun u I => Env.of_installed I (by omega))
    (WP.mono (deriveEntry_ok h₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine genDispatch_trace Generate.deriveSized _ E₁.ws E₂.ws (by omega) (by omega) (genWidths_mem hv) (by decide)
    (by rw [E₁.field (d := 100) (v := arg s₁ 0) (by simp)]) (by rw [E₁.field (d := 104) (v := arg s₁ 2) (by simp)])
    (by rw [E₂.field (d := 100) (v := arg s₂ 0) (by simp), a0])
    (by rw [E₂.field (d := 104) (v := arg s₂ 2) (by simp), a2])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 4).toNat * 8 := by omega
  have C₁ := deriveCtx h₁ rfl rfl F₁
  have C₂ := deriveCtx h₂ hb₂ hz₂ F₂
  rw [← a0, ← a2] at C₂
  have pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 3)) ((arg s₁ 4).toNat * 8) (deriveFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 3)) ((arg s₁ 4).toNat * 8) (deriveFields s₂) u₂),
      ∀ i ∈ deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat, PtrEq (State.addr (arg s₁ 3)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ i hi
    unfold PtrEq
    rw [derivePtrs G₁ i hi, derivePtrs (pLen := (arg s₁ 0).toNat) (qLen := (arg s₁ 2).toNat) G₂ i hi, hr2, a0, a1, a2]
  have key := fun {o l : Nat} (h : o + l ≤ (s₁.gpr .r3).toNat) => derive_bytes hl hr2 hr3 (o := o) (l := l) h
  have Vp : deriveVal s₂ (.input .p) = deriveVal s₁ (.input .p) := by
    have k := key (o := 0) (l := (arg s₁ 0).toNat) (by omega)
    rw [BitVec.add_zero] at k
    simp only [deriveVal]; rw [← hr2, ← a0, k]
  have Vq : deriveVal s₂ (.input .q) = deriveVal s₁ (.input .q) := by
    simp only [deriveVal]; rw [← hr2, ← a0, ← a2, key (by omega)]
  have mp : (.input .p, (arg s₁ 0).toNat) ∈ deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat := by simp [deriveIns]
  have mq : (.input .q, (arg s₁ 2).toNat) ∈ deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat := by simp [deriveIns]
  have mg : (.input .g, (arg s₁ 0).toNat) ∈ deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat := by simp [deriveIns]
  have mx : (.input .nonce, (arg s₁ 2).toNat) ∈ deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat := by simp [deriveIns]
  have Pe : operand (State.addr (arg s₁ 3)) t₁ (.input .p) (arg s₁ 0).toNat =
      operand (State.addr (arg s₁ 3)) t₂ (.input .p) (arg s₁ 0).toNat := by
    rw [(C₁.inp mp).value, (C₂.inp mp).value, Vp]
  have Qe : operand (State.addr (arg s₁ 3)) t₁ (.input .q) (arg s₁ 2).toNat =
      operand (State.addr (arg s₁ 3)) t₂ (.input .q) (arg s₁ 2).toNat := by
    rw [(C₁.inp mq).value, (C₂.inp mq).value, Vq]
  unfold Generate.deriveSized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq (C₁.inp mp).toReady
      (C₂.inp mp).toReady (C₁.inp mq).toReady (C₂.inp mq).toReady (pe F₁ F₂ _ mp) (pe F₁ F₂ _ mq))
    (check_ok F₁.ws hz wp wq (C₁.inp mp).toReady (C₁.inp mq).toReady rfl rfl)
    (check_ok F₂.ws hz wp wq (C₂.inp mp).toReady (C₂.inp mq).toReady rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, _, S₁, O₁⟩ ⟨Z₂, K₂, _, S₂, O₂⟩ => ?_)
  have kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 4).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have G₁ := F₁.keep (deriveFields_ok s₁) S₁ (by decide) O₁ kee
  have G₂ := F₂.keep (deriveFields_ok s₂) S₂ (by decide) O₂ kee
  have ho : ∀ {w₁ w₂ : State}, Env s₁ (State.addr (arg s₁ 3)) ((arg s₁ 4).toNat * 8) (deriveFields s₁) w₁ →
      Env s₂ (State.addr (arg s₁ 3)) ((arg s₁ 4).toNat * 8) (deriveFields s₂) w₂ →
      hdr (State.addr (arg s₁ 3)) w₁ 96 = hdr (State.addr (arg s₁ 3)) w₂ 96 ∧
      hdr (State.addr (arg s₁ 3)) w₁ 64 = hdr (State.addr (arg s₁ 3)) w₂ 64 ∧
      hdr (State.addr (arg s₁ 3)) w₁ 88 = hdr (State.addr (arg s₁ 3)) w₂ 88 := fun H₁ H₂ =>
    ⟨by rw [H₁.field (d := 96) (v := s₁.gpr .r0) (by simp), H₂.field (d := 96) (v := s₂.gpr .r0) (by simp), hr0],
      by rw [H₁.field (d := 64) (v := s₁.gpr .r2) (by simp), H₂.field (d := 64) (v := s₂.gpr .r2) (by simp), hr2],
      by rw [H₁.field (d := 88) (v := arg s₁ 1) (by simp), H₂.field (d := 88) (v := arg s₂ 1) (by simp), a1]⟩
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact deriveFailure_trace _ _ G₁.ws G₂.ws (by omega) (by omega) (by omega) (ho G₁ G₂).1
  · have valid : shapeValid (operand (State.addr (arg s₁ 3)) t₁ (.input .p) (arg s₁ 0).toNat)
        (operand (State.addr (arg s₁ 3)) t₁ (.input .q) (arg s₁ 2).toNat) := by
      rw [eval_eq, Z₁] at hf
      exact Classical.not_not.mp (of_decide_eq_false (Option.some.inj hf))
    rw [(C₁.inp mp).value, (C₁.inp mq).value] at valid
    have B₁ := shape_bounds valid
    have Dm₁ : DomainOk (deriveVal s₁ (.input .p)) (deriveVal s₁ (.input .q)) := ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    have Dm₂ : DomainOk (deriveVal s₂ (.input .p)) (deriveVal s₂ (.input .q)) := by rw [Vp, Vq]; exact Dm₁
    have D₁ := deriveCtx h₁ rfl rfl G₁
    have D₂ := deriveCtx h₂ hb₂ hz₂ G₂
    rw [← a0, ← a2] at D₂
    have X : Pair (State.addr (arg s₁ 3)) ((arg s₁ 4).toNat * 8) ((arg s₁ 4).toNat * 8) (arg s₁ 0).toNat
        (arg s₁ 2).toNat (((arg s₁ 0).toNat + 7) / 8) (((arg s₁ 2).toNat + 7) / 8)
        (deriveIns (arg s₁ 0).toNat (arg s₁ 2).toNat) (deriveVal s₁) (deriveVal s₂) v₁ v₂ :=
      ⟨D₁, D₂, pe G₁ G₂⟩
    refine SameTrace.assoc_left (SameTrace.seq (deriveCompute_trace X mp mq mg mx Dm₁ Dm₂)
      (deriveCompute_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp mx) Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo)
      (deriveCompute_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp mx) Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo)
      fun w₁ w₂ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => ?_)
    have keep : ∀ r ∈ runRanges, r.1 + r.2 ≤ (arg s₁ 4).toNat * 8 ∧
        (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega
    have H₁ := G₁.keep (deriveFields_ok s₁) Rn₁.rest (by decide) Rn₁.mem keep
    have H₂ := G₂.keep (deriveFields_ok s₂) Rn₂.rest (by decide) Rn₂.mem keep
    obtain ⟨e96, e64, e88⟩ := ho H₁ H₂
    exact writeKey_trace _ _ H₁.ws H₂.ws (by omega) (by omega) e96 e64 e88

end VG.Proof.Dsa.Arm
