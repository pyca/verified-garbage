module

public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Proof.Dsa.Arm.Compute
public import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Dsa.Arm.Sign
import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing for a validated private key on 32-bit ARM: correctness

`prevSignArm` is signing's contract (`signArm`) for a key whose exact
bytes validate (`Spec.Dsa.validatePrivateKeyBytes`). `prevSign_correct`:
`vg_dsa_sign_prevalidated` returns `Spec.Dsa.signBytes`, since rebuilding
q − 2 and checking the nonce's range in place of the checks of the key
leaves out only checks that the precondition makes hold.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest eval_eq)

/-- What `vg_dsa_sign_prevalidated` needs: `signPre`, and a key whose exact
bytes validate. -/
def prevSignPre (s : State) : Prop :=
  signPre s ∧ Spec.Dsa.validatePrivateKeyBytes (arg s 0).toNat (arg s 2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = true

def prevSignArm : Contract isa where
  pre := prevSignPre
  post := signArm.post
  pub := signArm.pub

theorem signPrevDispatch_ok (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Ws s base size) (hz : 120 ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp : (hdr base s 100).toNat = pLen) (hq : (hdr base s 104).toNat = qLen)
    (body : ∀ t, Rest [.r4, .r5] s t → t.mem = s.mem → WP isa (PrevalidatedSign.sized pLen qLen) t Q) :
    WP isa (PrevalidatedSign.dispatch widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold PrevalidatedSign.dispatch
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

/-- The checks the prevalidated signer makes: the nonce, and nonzero r and s. -/
abbrev signPrevChecks (P Q G X K D : Nat) : Prop :=
  (0 < K ∧ K < Q) ∧ rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0

theorem signPrevCompute_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (PrevalidatedSign.compute pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (signPrevChecks P Q G X K D) ∧
      localVal base t Impl.Dsa.Layout.r qLen = rValue P Q G K ∧
      localVal base t Impl.Dsa.Layout.s qLen = sValue P Q G X K D ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  have Qlt := operand_lt_of Iq
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.qMinusTwo ∧ Impl.Dsa.Layout.qMinusTwo + qLen ≤ 15712 := by omega
  simp only [PrevalidatedSign.compute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) Sc.ws (by omega) Sc.wq Iq.toReady
    Iq.value (by omega) hQo (by omega) (by decide) (by decide) (by omega) (by decide)) fun u₁ ⟨B₁, St₁⟩ => ?_)
  have Sc₁ := Sc.stage St₁
  have r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.next Sc St₁ (.inr ho)
  refine WP.seq (WP.mono (range_ok Sc₁.ws (by omega) Sc.wq (r₁ Iq).toReady (r₁ Ik).toReady false)
    fun u₂ ⟨F₂, St₂⟩ => ?_)
  rw [(r₁ Iq).value, (r₁ Ik).value] at F₂
  have Sc₂ := Sc₁.stage St₂
  have r₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₂ base size p len v :=
    fun I => (r₁ I).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)
  have L₂ : localVal base u₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₂.localVal_eq (by omega) (by omega) (by omega) (by omega)]
    exact localVal_of_bytes B₁ (by omega)
  have hc₂ : countValue base u₂ Core.digestPrefix = c :=
    ((countValue_stage St₂ (by omega)).trans (countValue_stage St₁ (by omega))).trans hc
  refine WP.seq (WP.mono (sign_ok Sc₂ (r₂ Ip) (r₂ Iq) (r₂ Ig) (r₂ Ix) (r₂ Ik) (r₂ Id) hc₂ L₂ hP hPo hQ hQo)
    fun u₃ ⟨R₃, S₃, M₃, Rn₃⟩ => ?_)
  have Sc₃ := Sc₂.run Rn₃
  refine WP.seq (WP.seq (WP.mono (zero_ok Sc₃.ws (by omega_arith) Sc.wq
    (localReady (o := Impl.Dsa.Layout.r) (len := qLen) Sc₃.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₄ ⟨F₄, St₄⟩ => WP.mono (zero_ok (St₄.ws Sc₃.ws) (by omega_arith) Sc.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) (St₄.ws Sc₃.ws) (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩))
  · rw [local_operand Sc₃.ws (by omega_arith), R₃] at F₄
    rw [local_operand (St₄.ws Sc₃.ws) (by omega_arith), St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      S₃] at F₅
    rw [F₅, F₄, M₃, F₂, St₁.maskW (by omega), BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte, signPrevChecks]))
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₃]
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), S₃]
  · exact (((((St₁.run (.inr ho)).trans (St₂.run (.inl ⟨rfl, rfl⟩))).trans Rn₃).trans
      (St₄.run (.inl ⟨rfl, rfl⟩))).trans (St₅.run (.inl ⟨rfl, rfl⟩)))

theorem signPrevBody_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1)
    (hm : maskW base s = BitVec.allOnes 32) (O : Output s base size (2 * qLen))
    (pre : publicChecks P Q G Y ∧ (0 < X ∧ X < Q) ∧ G ^ X % P = Y) :
    WP isa (PrevalidatedSign.body pLen qLen) s fun t =>
      t.gpr .r0 = (if signChecks P Q G Y X K D then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (2 * qLen) =
        (if signChecks P Q G Y X K D then
          Spec.Dsa.encodeBE qLen (rValue P Q G K) ++ Spec.Dsa.encodeBE qLen (sValue P Q G X K D)
        else List.replicate (2 * qLen) 0) ∧
      Body base (State.addr (pointerValue base s (.input .out))) (2 * qLen) s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have Qlt := operand_lt_of Iq
  have qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  unfold PrevalidatedSign.body
  refine WP.seq (WP.mono (signPrevCompute_ok Sc Ip Iq Ig Ix Ik Id hc hP hPo hQ hQo) fun u ⟨Fu, Ru, Su, Rn⟩ => ?_)
  have mu : maskW base u = mask32 (signChecks P Q G Y X K D) := by
    rw [Fu, hm, BitVec.allOnes_and]
    exact mask32_iff ⟨fun ⟨hk, hr, hs⟩ => ⟨pre.1, ⟨pre.2.1, hk⟩, pre.2.2, hr, hs⟩,
      fun ⟨_, ⟨_, hk⟩, _, hr, hs⟩ => ⟨hk, hr, hs⟩⟩
  have Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem (by decide) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  have Ou := O.run Rn
  have wu := Rn.ws Sc.ws
  refine WP.seq (WP.mono (writeScalar_ok wu big Sc.wq q32 (by omega_arith) (by omega_arith) Ru (by simp only [rValue]; exact qlt _)
    _ mu Ou false) fun v ⟨Bv, mv, Pv, Wv, Kv, _, Bdv⟩ => ?_)
  have wv := wu.of_rest Bdv.rest (by decide)
  refine WP.seq (WP.mono (writeScalar_ok (v := sValue P Q G X K D) wv big Sc.wq q32 (by omega_arith) (by omega_arith)
    (by rw [Kv _ _ (by omega_arith) (by omega_arith)]; exact Su) (by simp only [sValue]; exact qlt _) _ (mv.trans mu)
    (Ou.keep Pv Wv) true) fun w ⟨Bw, mw, Pw, Ww, Kw, Ew, Bdw⟩ => ?_)
  have ww := wv.of_rest Bdw.rest (by decide)
  refine WP.mono (result_ok ww (by omega_arith) _ ((mw.trans mv).trans mu)) fun t ⟨r0, Rt, Mt⟩ => ⟨r0, ?_, ?_⟩
  · rw [Pu] at Bv
    rw [Pv, Pu] at Bw
    simp only [Bool.false_eq_true, ↓reduceIte] at Bv Bw
    rw [Mt]
    refine VG.Proof.Dsa.signatureBytes _ ?_ Bw
    have E := Ew 0 qLen (by omega_arith) (.inl (by simp only [↓reduceIte]; omega_arith))
    rw [Pv, Pu, BitVec.add_zero] at E
    rw [E]
    simpa only [BitVec.add_zero] using Bv
  · rw [Pu] at Bdv
    rw [Pv, Pu] at Bdw
    exact ((Body.of_run Rn).trans Bdv).trans (Bdw.trans ⟨Rt.mono (by decide), fun x _ _ => by rw [Mt]⟩)

theorem prevSign_correct {s : State} (h : prevSignPre s) :
    WP isa PrevalidatedSign.sign s fun t => abiPreserved s t ∧ signArm.post s t := by
  obtain ⟨h, hval⟩ := h
  obtain ⟨hsp, hrd, hwr, _, _, _, dOS, _, dKS, dNS, dDS, _, fO, fK, fN, fD, fS, hv, hr1, hr3, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s 0).toNat ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [PrevalidatedSign.sign, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (signEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := signFields_ok s
  refine WP.seq (signPrevDispatch_ok _ E₀.ws (by omega_arith) (widths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := arg s 0) (by simp)]) (by rw [E₀.field (d := 104) (v := arg s 2) (by simp)]) fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 6).toNat * 8 := by omega_arith
  have kr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain ⟨Ip₁, Iq₁, -, -, -⟩ := signKeyIn h rfl rfl E₁
  unfold PrevalidatedSign.sized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, D₂, R₂, O₂⟩ => ?_)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · have nv := of_decide_eq_true (Z ▸ ht)
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    refine WP.mono (failure_ok E₂.ws (by omega_arith) (signOutput h rfl rfl E₂) (by rw [E₂.field (d := 104) (v := arg s 2) (by simp)])
      q0 q32) fun t₃ ⟨Z₃, B₃, R₃, O₃⟩ => ?_
    rw [po] at B₃ O₃
    have none : signRes s = none :=
      VG.Proof.Dsa.signBytes_invalid_shape (by rw [signKey _ _ (by omega_arith)]; exact nv)
    refine finish_ok (E₂.ws.of_rest R₃ (by decide)) (by omega_arith) (E₂.saved_outside O₃ (hr1 ▸ dOS) (by omega_arith))
      (R₃.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, none]; rfl
    · rw [M, hr1, B₃, none]; rfl
  · have valid := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    have hm : maskW (State.addr (arg s 5)) t₂ = BitVec.allOnes 32 := by
      rw [M]; simp only [mask32, valid, ↓reduceIte]
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    obtain ⟨Ip, Iq, Ig, Iy, Ix⟩ := signKeyIn h rfl rfl E₂
    have In := signNonceIn h rfl rfl E₂
    have Id := signDigestIn h rfl rfl E₂ (Nat.min_le_left (arg s 4).toNat (qWidth (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))))
    have hc : countValue (State.addr (arg s 5)) t₂ Core.digestPrefix = min (arg s 4).toNat (qWidth
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))) := by
      refine D₂.trans ?_
      rw [E₁.field (d := 108) (v := arg s 4) (by simp)]
    rw [VG.Proof.Dsa.bytesAt_prefix, qWidth_of_shape valid] at Id
    rw [qWidth_of_shape valid] at hc
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have chk := of_decide_eq_true ((VG.Proof.Dsa.validatePrivateKeyBytes_eq hv
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3)
      (signKey _ _ (by omega_arith))).symm.trans hval)
    refine WP.mono (signPrevBody_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Ix In Id hc hP hPo hQ hQo hm
      (signOutput h rfl rfl E₂) chk.2) fun t₃ ⟨Z₃, B₃, Bd₃⟩ => ?_
    rw [po] at B₃ Bd₃
    have SR : signRes s = _ := signBytes_eq (nonce := Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) (digest := Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat) hv valid
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3)
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) (signKey _ _ (by omega_arith)) rfl
    refine finish_ok (E₂.ws.of_rest Bd₃.rest (by decide)) (by omega_arith) (E₂.saved_body Bd₃ (hr1 ▸ dOS) (by omega_arith))
      (Bd₃.rest.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, SR]
      split <;> rfl
    · rw [M, hr1, B₃, SR]
      split <;> rfl

end VG.Proof.Dsa.Arm
