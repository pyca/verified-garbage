module

public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateTrace
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.SigningKey
import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.OutputBytes
public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.Env
import VerifiedGarbage.Proof.Dsa.Arm.Prevalidated
import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness

/-! ### `Dsa.Arm.ValidatePrivate`, which this module and modules that import it used -/

section

/-!
# DSA private-key validation on 32-bit ARM: correctness

`validatePrivArm` is the domain check's contract (`checkArm`) with a whole
private key, whose result is `Spec.Dsa.validatePrivateKeyBytes`.
`validatePriv_correct`: `vg_dsa_validate_private_key` returns whether the
key validates, by the signer's checks of the key with the nonce at x.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest Upd Mupd eval_eq wp_mov op2_imm)

variable {umaal : Bool}

/-! ## The contract -/

/-- What `vg_dsa_validate_private_key` needs: `(key = r0, key_len = r1,
p_len = r2, q_len = r3, scratch = [sp], scratch_len = [sp + 4])`. -/
def validatePrivPre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [key, args] ∧ s.wr = [scratch] ∧
    key.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat + 2 * (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat

/-- The bytes of the key. -/
abbrev validatePrivKey (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The result of the validation in a state. -/
abbrev validatePrivRes (s : State) : Bool :=
  Spec.Dsa.validatePrivateKeyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat (validatePrivKey s)

/-- What validation may leak: the public part of the key, and its result. -/
abbrev validatePrivLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r2).toNat (s.gpr .r3).toNat (validatePrivKey s) ++
    [if validatePrivRes s then 1 else 0]

def validatePrivArm : Contract isa where
  pre := validatePrivPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if validatePrivRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ validatePrivLeak s₁ = validatePrivLeak s₂ ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 2, arg s₁ i = arg s₂ i

/-! ## The entry -/

/-- The fields of private-key validation: the domain check's, with the nonce at x. -/
abbrev privateFields (s : State) : Fields :=
  (88, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) :: checkFields s

theorem privateFields_ok (s : State) : FieldsOk (privateFields s) := by
  intro f hf
  simp only [privateFields, checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem validateEntry_of {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32)
    (hrd : (⟨State.addr s.sp, 4 * 2⟩ : Region) ∈ s.rd)
    (hwr : s.wr = [⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩])
    (hsb : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32)
    (hv : Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat)
    (hsw : Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat) :
    WP isa (.block PrevalidatedSign.validateEntry) s
      (Installed s (State.addr (arg s 0)) ((arg s 1).toNat * 8) (privateFields s)) := by
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 16384 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have h84 : 80 + 4 ≤ (arg s 1).toNat * 8 := by omega_using [hs16]
  have h92 : 88 + 4 ≤ (arg s 1).toNat * 8 := by omega_using [hs16]
  show WP isa (.block (Generate.checkEntry ++ [.ldr .r4 .r12 80, .str .r4 .r12 88])) s _
  refine VG.Proof.X25519.Arm.WP.append (l := Generate.checkEntry) (checkEntry_of hsp hrd hwr hsb hv hsw)
    fun u I => ?_
  have nw := I.ws.nowrap
  have hx : u.mem.readW (off (State.addr (arg s 0)) 80) 32 = s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2 :=
    I.fields (80, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) (by simp)
  refine wp_ldr12 I.ws (d := 80) (by decide) h84 fun u₁ v₁ => ?_
  refine wp_str12 (I.ws.of_upd v₁ (by decide)) (d := 88) (by decide) h92 fun u₂ m₂ => WP.block_nil ?_
  have val : u₁.gpr .r4 = s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2 := by
    rw [v₁.gpr]; exact hx
  have mem₂ : u₂.mem = u.mem.writeW (off (State.addr (arg s 0)) 88)
      (s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) := by
    rw [m₂.mem, val, v₁.mem]
  refine ⟨(I.ws.of_upd v₁ (by decide)).of_mupd m₂, fun f hf => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [mem₂]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact readW_off_self _ _ _ _
    · have hf' := hf
      simp only [checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf'
      rcases hf' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact stored (by simp) (by omega_arith) (by omega_arith) (I.fields _ hf) _
  · rw [mem₂]
    exact stored (.inr (by omega_arith)) (by omega_arith) (by omega_arith) (I.saved i hi) _
  · rw [mem₂]
    exact I.mem.trans (outside_word (by decide) (by decide) (by omega_arith) _)
  · exact (I.rest.trans (v₁.rest (by simp))).trans (m₂.rest _)


/-- The key's components, at a state with the environment of validation:
the nonce is x. -/
theorem validatePrivIn {s t : State} {base : Addr} {size : Nat} (h : validatePrivPre s)
    (hb : State.addr (arg s 0) = base) (hsz : (arg s 1).toNat * 8 = size)
    (E : Env s base size (privateFields s) t) :
    Input t base size (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .y) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r2).toNat)) ∧
      Input t base size (.input .x) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .nonce) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r3).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, dKS, _, fK, _, hv, hr1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 12016 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have kr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (s.gpr .r2).toNat)
    (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp)) kr fK (by omega_arith) (.inr rfl) dKS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .x) (by decide : Impl.Dsa.Layout.Field.x ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .nonce) (by decide : Impl.Dsa.Layout.Field.nonce ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))
  · exact (E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2]) (by simp; omega_arith))
  · exact (E.field (d := 80) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2, s.gpr .r2]) (by simp; omega_arith))
  · exact (E.field (d := 88) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2, s.gpr .r2]) (by simp; omega_arith))

/-! ## Validation -/

theorem validatePriv_correct {s : State} (h : validatePrivPre s) :
    WP isa (PrevalidatedSign.validate umaal) s fun t => abiPreserved s t ∧ validatePrivArm.post s t := by
  obtain ⟨hsp, hrd, hwr, _, _, _, hsb, hv, hr1, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have keyLen : (validatePrivKey s).length = 3 * (s.gpr .r2).toNat + 2 * (s.gpr .r3).toNat := by
    simp only [validatePrivKey, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1
  have spec := VG.Proof.Dsa.validatePrivateKeyBytes_eq hv keyLen (signKey _ _ (by omega_arith))
  simp only [PrevalidatedSign.validate, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (validateEntry_of hsp (by rw [hrd]; simp) hwr hsb hv hsw) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := privateFields_ok s
  refine WP.seq (genDispatch_ok (PrevalidatedSign.validateSized umaal) _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 12016 ≤ (arg s 1).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -, -, -⟩ := validatePrivIn h rfl rfl E₁
  unfold PrevalidatedSign.validateSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    have nv := of_decide_eq_true (Z ▸ ht)
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega_arith) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 _ => ⟨A, ?_⟩
    have : validatePrivRes s = false := by
      simp only [validatePrivRes, spec]
      exact decide_eq_false fun hc => nv hc.1
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if validatePrivRes s = true then 1 else 0
    rw [this, BitVec.setWidth_append_eq_right, r0, v₃.gpr]
    rfl
  · have valid := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig, Iy, Ix, In⟩ := validatePrivIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have hm : maskW (State.addr (arg s 0)) t₂ = BitVec.allOnes 32 := by
      rw [M]; simp only [mask32, valid, ↓reduceIte]
    have Sc : Sched t₂ (State.addr (arg s 0)) ((arg s 1).toNat * 8) (s.gpr .r2).toNat (s.gpr .r3).toNat _ _ :=
      ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩
    refine WP.seq (WP.mono (signingKey_ok Sc Ip Iq Ig Iy hP hPo hQ hQo) fun u₁ ⟨F₁, _, Rn₁⟩ => ?_)
    have fits := Sc.fits
    have r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat},
        Input t₂ (State.addr (arg s 0)) ((arg s 1).toNat * 8) p len v →
        Input u₁ (State.addr (arg s 0)) ((arg s 1).toNat * 8) p len v :=
      fun I => I.run Rn₁ (by omega_arith) fits
    refine WP.seq (WP.mono (privateKey_ok (Sc.run Rn₁) (r₁ Ip) (r₁ Iq) (r₁ Ig) (r₁ Iy) (r₁ Ix) (r₁ In) hP hPo)
      fun u₂ ⟨F₂, _, Rn₂⟩ => ?_)
    have Rn := Rn₁.trans Rn₂
    have E₃ := E₂.keep fok Rn.rest (by decide) Rn.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    have F : maskW (State.addr (arg s 0)) u₂ = mask32 (validatePrivRes s = true) := by
      simp only [validatePrivRes, validatePrivKey, spec, decide_eq_true_eq]
      rw [F₂, F₁, hm, BitVec.allOnes_and, mask32_and]
      exact (mask32_iff (signingPublicChecks_consistent hP)).trans
        (mask32_iff ⟨fun ⟨hp, ⟨hx, _⟩, he⟩ => ⟨valid, hp, hx, he⟩,
          fun ⟨_, hp, hx, he⟩ => ⟨hp, ⟨hx, hx⟩, he⟩⟩)
    refine WP.mono (result_ok E₃.ws (by omega_arith) _ F) fun t₄ ⟨r0₄, R₄, M₄⟩ => ?_
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega_arith) (fun i hi => by rw [M₄]; exact E₃.saved i hi)
      (R₄.sp.trans E₃.sp) fun u A r0 _ => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if validatePrivRes s = true then 1 else 0
    exact status_toNat (r0.trans r0₄)

end VG.Proof.Dsa.Arm

end

end

-- separate module: the constant-time proof costs more than its imports, and the satisfiability
-- witness of `ValidatePrivateVerified.lean` should not re-check it.

/-!
# DSA private-key validation on 32-bit ARM: constant time

Two runs with the same arguments and the same public part of the key take
the same path: as the public key's validation (`PrevalidatedCT.lean`), with
the private key's checks (`KeyTrace.lean`), whose trace does not depend on x.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

variable {umaal : Bool}


/-- The key's operands. -/
def privIns (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen), (.input .x, qLen),
    (.input .nonce, qLen)]

/-- Their values. -/
def privVal (s : State) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
      (s.gpr .r3).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .y => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .x => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r3).toNat)
  | .input .nonce => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r3).toNat)
  | _ => 0

theorem privCtx {s t : State} {base : Addr} {size : Nat} (h : validatePrivPre s)
    (hb : State.addr (arg s 0) = base) (hsz : (arg s 1).toNat * 8 = size)
    (E : Env s base size (privateFields s) t) :
    Ctx base size (s.gpr .r2).toNat (s.gpr .r3).toNat (((s.gpr .r2).toNat + 7) / 8) (((s.gpr .r3).toNat + 7) / 8)
      (privIns (s.gpr .r2).toNat (s.gpr .r3).toNat) (privVal s) t := by
  have hv := h.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega_using [hsw, p128]
  obtain ⟨Ip, Iq, Ig, Iy, Ix, In⟩ := validatePrivIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [privIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Iy
  · exact Ix
  · exact In

theorem privPtrs {s t : State} {base : Addr} {size pLen qLen : Nat} (E : Env s base size (privateFields s) t) :
    ∀ i ∈ privIns pLen qLen, pointerValue base t i.1 =
      match i.1 with
      | .input .p => s.gpr .r0
      | .input .q => s.gpr .r0 + s.gpr .r2
      | .input .g => s.gpr .r0 + s.gpr .r2 + s.gpr .r3
      | .input .y => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2
      | _ => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2 := by
  intro i hi
  simp only [privIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r0) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)
  · exact E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)
  · exact E.field (d := 80) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) (by simp)
  · exact E.field (d := 88) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2) (by simp)

/-- The key's bytes at an offset, the same in two runs that leak the same. -/
theorem priv_bytes {s₁ s₂ : State} (h₁ : validatePrivPre s₁) (hl : validatePrivLeak s₁ = validatePrivLeak s₂)
    (hr0 : s₁.gpr .r0 = s₂.gpr .r0) (hr1 : s₁.gpr .r1 = s₂.gpr .r1) (hr2 : s₁.gpr .r2 = s₂.gpr .r2)
    (hr3 : s₁.gpr .r3 = s₂.gpr .r3) {o l : Nat} (hol : o + l ≤ 3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l := by
  have r1 := h₁.2.2.2.2.2.2.2.2.1
  simp only [validatePrivLeak, validatePrivKey, Spec.Dsa.publicBytesLeak] at hl
  rw [← hr0, ← hr1, ← hr2, ← hr3] at hl
  obtain E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp
    (List.append_inj hl (by simp [Spec.Rsa.bytesAt])).1
  rw [← VG.Proof.Dsa.bytesAt_prefix, ← VG.Proof.Dsa.bytesAt_prefix,
    show min (s₁.gpr .r1).toNat (3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) =
      3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat by omega_using [r1]] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem validatePriv_constantTime :
    ConstantTime isa validatePrivArm.pre validatePrivArm.pub (PrevalidatedSign.validate umaal) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
  obtain ⟨hsp, hl, hr0, hr1, hr2, hr3, ha⟩ := pub
  obtain a0 := ha 0 (by decide)
  obtain a1 := ha 1 (by decide)
  obtain ⟨sp₁, rd₁, wr₁, _, dSA₁, _, sb₁, hv, hpl, hsw⟩ := id h₁
  obtain ⟨sp₂, rd₂, wr₂, _, dSA₂, _, sb₂, hv₂, _, hsw₂⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 128 * (s₁.gpr .r2).toNat ≤ (arg s₁ 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_using [hsw]
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  obtain hb₂ : State.addr (arg s₂ 0) = State.addr (arg s₁ 0) := by rw [a0]
  obtain hz₂ : (arg s₂ 1).toNat * 8 = (arg s₁ 1).toNat * 8 := by rw [a1]
  simp only [PrevalidatedSign.validate, Core.sequence, List.foldr]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 8 _ rfl) (agree_args (n := 2) hsp (by omega_using [sp₁]) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₂.symm)))
    (WP.mono (validateEntry_of sp₁ (by rw [rd₁]; simp) wr₁ sb₁ hv hsw) fun u I => Env.of_installed I (by omega_using [hr2, a0, a1, sb₁, hpl, hsw, sb₂, hsw₂, v, hs16, qp, p128, hz₂]))
    (WP.mono (validateEntry_of sp₂ (by rw [rd₂]; simp) wr₂ sb₂ hv₂ hsw₂) fun u I => by
      obtain E := Env.of_installed I (by rw [hz₂]; omega_using [hr2, a0, a1, sb₁, hpl, hsw, sb₂, hsw₂, v, hs16, qp, p128, hz₂])
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine genDispatch_trace (PrevalidatedSign.validateSized umaal) _ E₁.ws E₂.ws (by omega_using [hr2, a0, a1, sb₁, hpl, hsw, sb₂, hsw₂, v, hs16, qp, p128, hz₂]) (by omega_using [hr2, a0, a1, sb₁, hpl, hsw, sb₂, hsw₂, v, hs16, qp, p128, hz₂]) (genWidths_mem hv)
    (by decide) (by rw [E₁.field (d := 100) (v := s₁.gpr .r2) (by simp)])
    (by rw [E₁.field (d := 104) (v := s₁.gpr .r3) (by simp)])
    (by rw [E₂.field (d := 100) (v := s₂.gpr .r2) (by simp), hr2])
    (by rw [E₂.field (d := 104) (v := s₂.gpr .r3) (by simp), hr3])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  obtain F₁ := E₁.of_mem R₁ (by decide) M₁
  obtain F₂ := E₂.of_mem R₂ (by decide) M₂
  obtain hz : 12016 ≤ (arg s₁ 1).toNat * 8 := by omega_using [hr2, a0, a1, sb₁, hpl, hsw, sb₂, hsw₂, v, hs16, qp, p128, hz₂]
  obtain C₁ := privCtx h₁ rfl rfl F₁
  obtain C₂ := privCtx h₂ hb₂ hz₂ F₂
  rw [← hr2, ← hr3] at C₂
  obtain pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (privateFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (privateFields s₂) u₂),
      ∀ i ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat, PtrEq (State.addr (arg s₁ 0)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ i hi
    unfold PtrEq
    rw [privPtrs G₁ i hi, privPtrs (pLen := (s₁.gpr .r2).toNat) (qLen := (s₁.gpr .r3).toNat) G₂ i hi,
      hr0, hr2, hr3]
  -- Both runs see the same key.
  obtain key := fun {o l : Nat} (h : o + l ≤ 3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) =>
    priv_bytes h₁ hl hr0 hr1 hr2 hr3 (o := o) (l := l) h
  obtain Vp : privVal s₂ (.input .p) = privVal s₁ (.input .p) := by
    obtain k := key (o := 0) (l := (s₁.gpr .r2).toNat) (by omega_using [])
    rw [BitVec.add_zero] at k
    simp only [privVal]; rw [← hr0, ← hr2, k]
  obtain Vq : privVal s₂ (.input .q) = privVal s₁ (.input .q) := by
    simp only [privVal]; rw [← hr0, ← hr2, ← hr3, key (by omega_using [])]
  obtain mp : (.input .p, (s₁.gpr .r2).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [privIns]
  obtain mq : (.input .q, (s₁.gpr .r3).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [privIns]
  obtain mg : (.input .g, (s₁.gpr .r2).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [privIns]
  obtain my : (.input .y, (s₁.gpr .r2).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [privIns]
  obtain Pe : operand (State.addr (arg s₁ 0)) t₁ (.input .p) (s₁.gpr .r2).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .p) (s₁.gpr .r2).toNat := by
    rw [(C₁.inp mp).value, (C₂.inp mp).value, Vp]
  obtain Qe : operand (State.addr (arg s₁ 0)) t₁ (.input .q) (s₁.gpr .r3).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .q) (s₁.gpr .r3).toNat := by
    rw [(C₁.inp mq).value, (C₂.inp mq).value, Vq]
  unfold PrevalidatedSign.validateSized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq (C₁.inp mp).toReady
      (C₂.inp mp).toReady (C₁.inp mq).toReady (C₂.inp mq).toReady (pe F₁ F₂ _ mp) (pe F₁ F₂ _ mq))
    (check_ok F₁.ws hz wp wq (C₁.inp mp).toReady (C₁.inp mq).toReady rfl rfl)
    (check_ok F₂.ws hz wp wq (C₂.inp mp).toReady (C₂.inp mq).toReady rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, _, S₁, O₁⟩ ⟨Z₂, K₂, _, S₂, O₂⟩ => ?_)
  obtain kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 1).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_using [hz]
  obtain G₁ := F₁.keep (privateFields_ok s₁) S₁ (by decide) O₁ kee
  obtain G₂ := F₂.keep (privateFields_ok s₂) S₂ (by decide) O₂ kee
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact SameTrace.of_relCT (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.seq (block_relCT_T0 _ rfl)
      (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial))) (agree0 G₁.ws G₂.ws)
  · have valid : shapeValid (operand (State.addr (arg s₁ 0)) t₁ (.input .p) (s₁.gpr .r2).toNat)
        (operand (State.addr (arg s₁ 0)) t₁ (.input .q) (s₁.gpr .r3).toNat) := by
      rw [eval_eq, Z₁] at hf
      exact Classical.not_not.mp (of_decide_eq_false (Option.some.inj hf))
    rw [(C₁.inp mp).value, (C₁.inp mq).value] at valid
    obtain B₁ := shape_bounds valid
    obtain Dm₁ : DomainOk (privVal s₁ (.input .p)) (privVal s₁ (.input .q)) :=
      ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    obtain Dm₂ : DomainOk (privVal s₂ (.input .p)) (privVal s₂ (.input .q)) := by rw [Vp, Vq]; exact Dm₁
    obtain D₁ := privCtx h₁ rfl rfl G₁
    obtain D₂ := privCtx h₂ hb₂ hz₂ G₂
    rw [← hr2, ← hr3] at D₂
    obtain X : Pair (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) ((arg s₁ 1).toNat * 8) (s₁.gpr .r2).toNat
        (s₁.gpr .r3).toNat (((s₁.gpr .r2).toNat + 7) / 8) (((s₁.gpr .r3).toNat + 7) / 8)
        (privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat) (privVal s₁) (privVal s₂) v₁ v₂ :=
      ⟨D₁, D₂, pe G₁ G₂⟩
    obtain mx : (.input .x, (s₁.gpr .r3).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
      simp [privIns]
    obtain mk : (.input .nonce, (s₁.gpr .r3).toNat) ∈ privIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
      simp [privIns]
    refine SameTrace.assoc_left (SameTrace.seq (signingKey_trace X mp mq mg my Dm₁ Dm₂)
      (signingKey_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo)
      (signingKey_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo)
      fun w₁ w₂ ⟨_, _, A₁⟩ ⟨_, _, A₂⟩ => ?_)
    obtain X₁ := X.run A₁ A₂
    refine SameTrace.assoc_left (SameTrace.seq (privateKey_trace X₁ mp mq mg my mx mk Dm₁ Dm₂)
      (privateKey_ok X₁.C₁.S (X₁.C₁.inp mp) (X₁.C₁.inp mq) (X₁.C₁.inp mg) (X₁.C₁.inp my) (X₁.C₁.inp mx)
        (X₁.C₁.inp mk) Dm₁.hP Dm₁.hPo)
      (privateKey_ok X₁.C₂.S (X₁.C₂.inp mp) (X₁.C₂.inp mq) (X₁.C₂.inp mg) (X₁.C₂.inp my) (X₁.C₂.inp mx)
        (X₁.C₂.inp mk) Dm₂.hP Dm₂.hPo)
      fun z₁ z₂ ⟨_, _, B₁⟩ ⟨_, _, B₂⟩ => ?_)
    exact SameTrace.of_relCT (RelCT.seq result_relCT
      (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial)))
      (agree0 ((G₁.ws.of_rest A₁.rest (by decide)).of_rest B₁.rest (by decide))
        ((G₂.ws.of_rest A₂.rest (by decide)).of_rest B₂.rest (by decide)))

end VG.Proof.Dsa.Arm
