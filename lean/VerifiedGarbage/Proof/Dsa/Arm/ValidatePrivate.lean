module

public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.Prevalidated
import VerifiedGarbage.Proof.Dsa.Arm.SigningKey
import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Dsa.Arm.Install
import VerifiedGarbage.Proof.Dsa.Arm.EntrySave
import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
import VerifiedGarbage.Proof.Framework.Omega

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
  have h84 : 80 + 4 ≤ (arg s 1).toNat * 8 := by omega
  have h92 : 88 + 4 ≤ (arg s 1).toNat * 8 := by omega
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
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
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
    WP isa PrevalidatedSign.validate s fun t => abiPreserved s t ∧ validatePrivArm.post s t := by
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
  refine WP.seq (genDispatch_ok PrevalidatedSign.validateSized _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by omega_arith
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
