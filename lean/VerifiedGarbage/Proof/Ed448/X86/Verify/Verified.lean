import VerifiedGarbage.Proof.Ed448.X86.Verify.Body
import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification on x86 (32-bit): constant time, and `Verified`

The check of `ctxlen` and the branch on it depend only on `ctxlen`, which is
public. In the frame, as for the public key: the blocks address memory only
through `esp` (or `scratch`, the same in both runs), and the calls get the
same arguments in both runs. `verify_equation`'s public data also includes
its inputs' bytes: the public key and the signature, the same in both runs
(`vfLocal.pub`), and `k`, the reduced hash of the inputs, which the proof
carries through the hash (`hash_ok`) and the reduction. `verify_verified`:
for any `eq` meeting `verifyEquationLocal` (`CalleeOk`), `code eq` meets
`Spec.Ed448.verifyContract X86.abi 280`.
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86 VG.Impl.Ed448.X86.Verify
open VG.Impl.Ed448.X86.Shake (callWith hdrAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots)

variable {σ₁ σ₂ : State} {g₁ g₂ : Reg → BitVec 32}

theorem base_eq (hp : vfLocal.pub σ₁ σ₂) : base σ₂ = base σ₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : vfLocal.pub σ₁ σ₂) : vfRd σ₂ = vfRd σ₁ := by
  obtain ⟨e, a0, a1, a2, a3, a4, a5, _⟩ := hp
  simp only [vfRd, PK, CTX, MSG, SIG, argAddr, e, a0, a1, a2, a3, a4, a5]

theorem wr_eq (hp : vfLocal.pub σ₁ σ₂) : vfWr σ₂ = vfWr σ₁ := by
  simp only [vfWr, hp.2.2.2.2.2.2.2.1]

theorem args₂ (hp : vfLocal.pub σ₁ σ₂) : Shake.Args (base σ₁) 7 (arg σ₁) σ₂.mem := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, a6, _⟩ := id hp
  intro i hi
  rw [← base_eq hp, args_val σ₂ 7 i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

/-- The inputs' bytes are the same in both runs. -/
theorem inputs_eq (hp : vfLocal.pub σ₁ σ₂) :
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 0).setWidth 64) 57 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat =
      Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat =
      Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 5).setWidth 64) 114 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 114 := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, _, pk, ctx, msg, sig⟩ := hp
  rw [← a0] at pk
  rw [← a1, ← a2] at ctx
  rw [← a3, ← a4] at msg
  rw [← a5] at sig
  exact ⟨pk.symm, ctx.symm, msg.symm, sig.symm⟩

/-- The hash both runs compute. -/
abbrev HV (σ : State) (m : Mem) : List Byte :=
  Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg σ 1).setWidth 64) (arg σ 2).toNat)
    (Spec.Sha3.bytesAt m ((arg σ 5).setWidth 64) 57 ++ Spec.Sha3.bytesAt m ((arg σ 0).setWidth 64) 57 ++
      Spec.Sha3.bytesAt m ((arg σ 3).setWidth 64) (arg σ 4).toNat)

theorem hv_eq (hp : vfLocal.pub σ₁ σ₂) : HV σ₁ σ₂.mem = HV σ₁ σ₁.mem := by
  obtain ⟨pk, ctx, msg, sig⟩ := inputs_eq hp
  have r : Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 5).setWidth 64) 57 = Spec.Sha3.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 57 := by
    have := congrArg (List.take 57) sig
    rwa [bytesAt_take57, bytesAt_take57] at this
  simp only [HV]
  rw [show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 0).setWidth 64) 57 = _ from pk,
    show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat = _ from ctx,
    show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat = _ from msg, r]
  rfl

abbrev Two₁ (σ₁ σ₂ : State) (g₁ g₂ : Reg → BitVec 32) :=
  Two (base σ₁) (vfRd σ₁) (vfWr σ₁) g₁ g₂ σ₁.mem σ₂.mem

/-- Bytes outside `Lo E`, as a callee sees them. -/
theorem entry_bytes' {E : BitVec 32} {t : State} (he : t.gpr .esp = E) (hE : 24 ≤ E.toNat) {D : Region}
    (h : (Lo E).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.callEntry.mem D.base D.len = Spec.Ed448.bytesAt t.mem D.base D.len :=
  frame_bytes (VG.Proof.Ed25519.X86.Whole.callEntry_frame t) (fun r hr => by
    rw [List.mem_singleton.mp hr, he]; exact (h.sub_left (below4_lo hE)).symm) hn

section
variable {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : Facts σ₁)
  (hp : vfLocal.pub σ₁ σ₂) (hcl : (arg σ₁ 2).toNat < 256)

include h hp in
/-- The hash, in both runs. -/
theorem hash_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) Impl.Ed448.X86.Verify.hash
      (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  have hsc := scr_at σ₁
  have fa := hk.fr_addr (d := HDR) (by decide)
  unfold Impl.Ed448.X86.Verify.hash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HDR) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HDR) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 1 0) (len := .caller 2 0) (P := arg σ₁ 1)
    (N := (arg σ₁ 2).toNat) (show 1 < 7 by decide) (show 2 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in σ₁), whole _⟩) (hk.away_input (ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .const 57) (P := arg σ₁ 5) (N := 57)
    (show 5 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (sig_in σ₁), sig57 σ₁⟩) (hk.away_input (sig_in σ₁) (sig57 σ₁))
    (by have := h.sig; omega) (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 0 0) (len := .const 57) (P := arg σ₁ 0) (N := 57)
    (show 0 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (pk_in σ₁), whole _⟩) (hk.away_input (pk_in σ₁) (whole _))
    h.pk (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 7 by decide) (show 4 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in σ₁), whole _⟩) (hk.away_input (msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

/-- The hash in the frame, the same in both runs. -/
abbrev HQ (σ₁ : State) (u : State) : Prop :=
  Spec.Ed448.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 HASH) 114 = HV σ₁ σ₁.mem

/-- `k` in the frame, the same in both runs. -/
abbrev KQ (σ₁ : State) (u : State) : Prop :=
  Spec.Ed448.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = Spec.Ed448.scalarReduce (HV σ₁ σ₁.mem)

include h hp hcl in
theorem front_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (.seq (.block (hdrAt 2 HDR)) Impl.Ed448.X86.Verify.hash)
      (Two₁ σ₁ σ₂ g₁ g₂ (HQ σ₁)) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  let HH : State → Prop := fun u =>
    Spec.Sha3.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg σ₁ 2)
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ HH)
    (block_ct (by taint_decide)
      (fun _ hc _ => WP.mono (hk.hdr_ok hc ha (j := 2) (off := HDR) (by decide) hcl (by decide))
        fun _ h => ⟨h.1, h.2.2.1⟩)
      (fun _ hc _ => WP.mono (hk.hdr_ok hc hb (j := 2) (off := HDR) (by decide) hcl (by decide))
        fun _ h => ⟨h.1, h.2.2.1⟩)) ?_
  refine (((hash_ct h hp).mono (P' := Two₁ σ₁ σ₂ g₁ g₂ HH)
    (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩) (fun _ _ h => h)).wp
    (F₁ := fun u => GCtx σ₁ g₁ σ₁.mem u ∧ HQ σ₁ u) (F₂ := fun u => GCtx σ₁ g₂ σ₂.mem u ∧ HQ σ₁ u)
    (fun a b hab => ⟨WP.mono (hash_ok h hab.1.1 ha hab.1.2) fun u hu => ⟨hu.1, show HQ σ₁ u from hu.2⟩,
      WP.mono (hash_ok h hab.2.1 hb hab.2.2) fun u hu => ⟨hu.1, show HQ σ₁ u from hu.2.trans (hv_eq hp)⟩⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)

include h hp in
/-- `k`, the hash reduced modulo `L`. -/
theorem reduce_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ (HQ σ₁))
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (Two₁ σ₁ σ₂ g₁ g₂ (KQ σ₁)) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  have keep : ∀ {t u : State}, Frame [⟨(base σ₁).setWidth 64, 24⟩] t.mem u.mem → HQ σ₁ t → HQ σ₁ u :=
    fun hm hq => (frame_bytes hm (D := fr (base σ₁) HASH 114) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)).trans hq
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ fun u => ReduceSlots σ₁ u ∧ HQ σ₁ u)
    (block_ct (by taint_decide) (fun _ hc hq => WP.mono (reduce_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq⟩)
      (fun _ hc hq => WP.mono (reduce_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq⟩)) ?_
  refine call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
    (fun _ _ _ hc hs => reduce_ready h hc hs.1)
    (fun a b ea eb ha' hb' ar aw br bw => by
      have e := hk.args_eq ea eb (k := 3) (by decide) (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        exacts [ha'.1.a0.trans hb'.1.a0.symm, ha'.1.a1.trans hb'.1.a1.symm, ha'.1.a2.trans hb'.1.a2.symm])
        ar aw br bw
      exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
    (fun _ hc hs => WP.mono (reduce_call h hc hs.1) fun _ hv => ⟨hv.1, by
      show Spec.Ed448.bytesAt _ ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = _
      rw [hv.2.2, (hs.2 : Spec.Ed448.bytesAt _ _ 114 = _)]⟩)
    (fun _ hc hs => WP.mono (reduce_call h hc hs.1) fun _ hv => ⟨hv.1, by
      show Spec.Ed448.bytesAt _ ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = _
      rw [hv.2.2, (hs.2 : Spec.Ed448.bytesAt _ _ 114 = _)]⟩)

/-- What `verify_equation`'s call needs to be the same in both runs. -/
abbrev EqQ (σ₁ : State) (u : State) : Prop :=
  EqSlots σ₁ u ∧ KQ σ₁ u ∧
    Spec.Ed448.bytesAt u.mem ((arg σ₁ 0).setWidth 64) 57 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt u.mem ((arg σ₁ 5).setWidth 64) 114 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 114

include hE h hp in
theorem equation_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ (KQ σ₁)) (callWith equationArgs "vg_ed448_verify_equation" eq)
      (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  obtain ⟨pk₂, _, _, sig₂⟩ := inputs_eq hp
  have fk := hk.fr_addr (d := K) (by decide)
  have keep : ∀ {t u : State}, Frame [⟨(base σ₁).setWidth 64, 24⟩] t.mem u.mem → KQ σ₁ t → KQ σ₁ u :=
    fun hm hq => (frame_bytes hm (D := fr (base σ₁) K 57) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 57 ≤ 2 ^ 64; decide)).trans hq
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ (EqQ σ₁))
    (block_ct (by taint_decide)
      (fun _ hc hq => WP.mono (eq_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq,
        hk.input_bytes (D := PK σ₁) hu.1 (pk_in σ₁) (whole (PK σ₁)) (by show 57 ≤ 2 ^ 64; decide),
        hk.input_bytes (D := SIG σ₁) hu.1 (sig_in σ₁) (whole (SIG σ₁)) (by show 114 ≤ 2 ^ 64; decide)⟩)
      (fun _ hc hq => WP.mono (eq_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq,
        (hk.input_bytes (D := PK σ₁) hu.1 (pk_in σ₁) (whole (PK σ₁)) (by show 57 ≤ 2 ^ 64; decide)).trans pk₂,
        (hk.input_bytes (D := SIG σ₁) hu.1 (sig_in σ₁) (whole (SIG σ₁)) (by show 114 ≤ 2 ^ 64; decide)).trans sig₂⟩)) ?_
  refine call_ct hE.ok hE.ct (fun _ _ _ hc hs => eq_ready h hc hs.1) ?_
    (fun _ hc hs => WP.mono (eq_call hE h hc hs.1) fun _ hv => ⟨hv.1, trivial⟩)
    (fun _ hc hs => WP.mono (eq_call hE h hc hs.1) fun _ hv => ⟨hv.1, trivial⟩)
  intro a b ea eb ha' hb' ar aw br bw
  have ca : ∀ j < 4, arg a.callEntry j = Whole.slots (base σ₁) a j := fun j hj =>
    VG.Proof.Ed25519.X86.Whole.call_arg ea hk.below hk.frame (by omega)
  have cb : ∀ j < 4, arg b.callEntry j = Whole.slots (base σ₁) b j := fun j hj =>
    VG.Proof.Ed25519.X86.Whole.call_arg eb hk.below hk.frame (by omega)
  have lpk := (hk.away_input (pk_in σ₁) (whole _)).lo
  have lsig := (hk.away_input (sig_in σ₁) (whole _)).lo
  have lk := lo_fr (base σ₁) (d := K) (l := 57) (by decide) (by decide)
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_esp, arg_withRegions, ca 0 (by decide), ca 1 (by decide), ca 2 (by decide), ca 3 (by decide),
    cb 0 (by decide), cb 1 (by decide), cb 2 (by decide), cb 3 (by decide), ha'.1.a0, ha'.1.a1, ha'.1.a2,
    ha'.1.a3, hb'.1.a0, hb'.1.a1, hb'.1.a2, hb'.1.a3, fk, ea, eb]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_⟩
  · rw [entry_bytes' ea hk.below (D := PK σ₁) lpk (by show 57 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := PK σ₁) lpk (by show 57 ≤ 2 ^ 64; decide)]
    exact ha'.2.2.1.trans hb'.2.2.1.symm
  · rw [entry_bytes' ea hk.below (D := SIG σ₁) lsig (by show 114 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := SIG σ₁) lsig (by show 114 ≤ 2 ^ 64; decide)]
    exact ha'.2.2.2.trans hb'.2.2.2.symm
  · rw [entry_bytes' ea hk.below (D := fr (base σ₁) K 57) lk (by show 57 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := fr (base σ₁) K 57) lk (by show 57 ≤ 2 ^ 64; decide)]
    exact ha'.2.1.trans hb'.2.1.symm

include hE h hp hcl in
theorem body_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (body eq) (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  unfold body
  exact RelCT.assoc ((front_ct h hp hcl).seq ((reduce_ct h hp).seq (equation_ct hE h hp)))

end

/-! ## The whole function -/

/-- After the check of `ctxlen`. -/
def After (σ t : State) : Prop :=
  t.gpr .esp = σ.gpr .esp ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧
    (∀ r, r ≠ .eax → t.gpr r = σ.gpr r) ∧ t.zf = some (decide ((arg σ 2).toNat < 256))

theorem verify_ct {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) :
    ConstantTime isa vfLocal.pre vfLocal.pub (code eq) := by
  apply RelCT.constantTime
  unfold code
  refine RelCT.seq (Q := fun _ _ => True) ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2.2.1) (by taint_decide)).wpDep (F := After)
    (fun s₁ s₂ h => ⟨check_ok (facts h.1) h.1.1, check_ok (facts h.2.1) h.2.1.1⟩)) ?_
  refine RelCT.ite ?_ ?_ ?_
  · rintro a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩
    change a.zf = b.zf
    rw [A₁.2.2.2.2.2, A₂.2.2.2.2.2, hp.2.2.2.1]
  · refine RelCT.frame (R := fun _ _ => True) ?_ ?_
    · rintro a b ⟨⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩, _⟩
      rw [A₁.1, A₂.1, hp.1]
    · rintro x y tx ty x' y' ⟨a, b, ⟨⟨_, σ₁, σ₂, ⟨p₁, p₂, hp⟩, A₁, A₂⟩, hev⟩, rfl, rfl⟩ e₁ e₂
      have hcl : (arg σ₁ 2).toNat < 256 := by
        change a.zf = some true at hev
        rw [A₁.2.2.2.2.2] at hev
        exact of_decide_eq_true (Option.some.inj hev)
      have h₁ := facts p₁
      have c₁ := push_ctx (s := a) (A₁.2.2.1.trans p₁.1) (A₁.2.2.2.1.trans p₁.2.1) (by rw [A₁.1]; exact h₁.below)
      have eb₁ : base a = base σ₁ := by simp only [base, A₁.1]
      rw [eb₁, A₁.2.1] at c₁
      have c₂ := push_ctx (s := b) (A₂.2.2.1.trans p₂.1) (A₂.2.2.2.1.trans p₂.2.1)
        (by rw [A₂.1]; exact (facts p₂).below)
      have eb₂ : base b = base σ₁ := by simp only [base, A₂.1, hp.1]
      rw [eb₂, A₂.2.1, rd_eq hp, wr_eq hp] at c₂
      exact ⟨(body_ct (g₁ := a.gpr) (g₂ := b.gpr) hE h₁ hp hcl _ _ _ _ _ _ ⟨⟨c₁, trivial⟩, ⟨c₂, trivial⟩⟩
        e₁ e₂).1, trivial⟩
  · refine RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (by taint_decide)
    rw [List.mem_singleton.mp hr]
    obtain ⟨⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩, _⟩ := h
    rw [A₁.1, A₂.1, hp.1]

/-! ## The shared contract -/

def vfWide : Contract isa := { vfLocal with
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let sig : Region := ⟨(arg s 5).setWidth 64, 114⟩
    let scr : Region := ⟨(arg s 6).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [pk, ctx, msg, sig] ∧ s.wr = [scr, args] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

theorem vfWide_pre (s : State) (h : vfWide.pre s) :
    vfLocal.pre (s.withRegions (vfRd s) (vfWr s)) := by
  obtain ⟨_, _, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, nb, g⟩ := h
  simp only [vfLocal, vfRd, vfWr, PK, CTX, MSG, SIG, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, nb, g⟩

def vfSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x8011 then 0x30 else
    if a = 0x8019 then 0x40 else if a = 0x801d then 0x50 else 0

def vfSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := vfSatMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩]
  wr := [⟨0x5000, 8192⟩, ⟨0x8004, 28⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem vfWide_implies : vfWide.Implies (Spec.Ed448.verifyContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vfWide, vfLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = _ at h
    rw [h, BitVec.setWidth_append_eq_right]
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, a0, a1, a2, a3, a4, a5, a6⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, sig⟩ := List.append_inj' hb (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, msg⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, a4])
    obtain ⟨pk, ctx⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, a2])
    exact ⟨sp, a0, a1, a2, a3, a4, a5, a6, pk, ctx, msg, sig⟩
  sat := by
    have a0 : arg vfSatState 0 = 0x1000 := by decide
    have a1 : arg vfSatState 1 = 0x2000 := by decide
    have a2 : arg vfSatState 2 = 0 := by decide
    have a3 : arg vfSatState 3 = 0x3000 := by decide
    have a4 : arg vfSatState 4 = 0 := by decide
    have a5 : arg vfSatState 5 = 0x4000 := by decide
    have a6 : arg vfSatState 6 = 0x5000 := by decide
    have e : argAddr vfSatState 0 = 0x8004 := by decide
    have esp : vfSatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vfWide, vfLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using vfSatState

theorem verify_verified {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) :
    Verified X86.target (code eq) (Spec.Ed448.verifyContract X86.abi 280) := by
  have hsat := vfWide_implies.sat_left
  have satLocal : ∃ s, vfLocal.pre s := hsat.elim fun s h => ⟨_, vfWide_pre s h⟩
  have verifiedLocal : Verified X86.target (code eq) vfLocal :=
    Verified.of_correct (fun _ h => verify_ok hE h) (verify_ct hE) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal vfRd vfWr vfWide_pre
    ?_ ?_ ?_ ?_ hsat) vfWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [vfRd, vfWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [vfWr, List.mem_singleton] at hr
    subst hr
    simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [vfWide, vfLocal, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

end VG.Proof.Ed448.X86.Verify
