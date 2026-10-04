import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Body
import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 public-key derivation on x86 (32-bit): constant time, and `Verified`

As Ed25519's on this target: two runs from the same pointers and `esp` set
up the same arguments for every call, each callee is constant time under its
own contract (the sponge functions' and `scalarBaseLocal`, `CalleeOk.ct`),
and the blocks between the calls address memory only through `esp`
(`taint_decide`). `publicKey_verified`: for any `base` meeting
`scalarBaseLocal` (`CalleeOk`), `code base` meets
`Spec.Ed448.publicKeyContract X86.abi 280`.
-/

namespace VG.Proof.Ed448.X86.PublicKey

open VG VG.X86 VG.Impl.Ed448.X86.PublicKey
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots)

variable {s₁ s₂ : State}

theorem base_eq (hp : pkLocal.pub s₁ s₂) : base s₂ = base s₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : pkLocal.pub s₁ s₂) : pkRd s₂ = pkRd s₁ := by
  simp only [pkRd, argAddr, hp.1, hp.2.2.1]

theorem wr_eq (hp : pkLocal.pub s₁ s₂) : pkWr s₂ = pkWr s₁ := by
  simp only [pkWr, hp.2.1, hp.2.2.2]

/-- The second run's argument words, as the first's. -/
theorem args₂ (hp : pkLocal.pub s₁ s₂) : Args (base s₁) 3 (arg s₁) s₂.mem := by
  intro i hi
  rw [← base_eq hp, args_val s₂ 3 i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [hp.2.1.symm, hp.2.2.1.symm, hp.2.2.2.symm]

abbrev Two₁ (s₁ s₂ : State) := Two (base s₁) (pkRd s₁) (pkWr s₁) s₁.gpr s₂.gpr s₁.mem s₂.mem

theorem base_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s₁) :
    RelCT isa (Two₁ s₁ s₂ (BaseSlots s₁)) (.call "vg_ed448_scalar_base" base') (Two₁ s₁ s₂ fun _ => True) :=
  call_ct hB.ok hB.ct (fun _ _ _ hc hs => base_ready h hc hs)
    (fun a b ea eb ha hb ar aw br bw => by
      have e := (kit h).args_eq ea eb (k := 3) (by decide) (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
      exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
    (fun _ hc hs => WP.mono (base_call hB h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
    (fun _ hc hs => WP.mono (base_call hB h hc hs) fun _ hv => ⟨hv.1, trivial⟩)

theorem body_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s₁)
    (hp : pkLocal.pub s₁ s₂) :
    RelCT isa (Two₁ s₁ s₂ fun _ => True) (body base') (Two₁ s₁ s₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val s₁ 3
  have hb := args₂ hp
  have hsc := scr_at s₁
  unfold body Impl.Ed448.X86.PublicKey.hash callWith
  refine RelCT.seq (RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide))
    (RelCT.seq (hk.first_ct ha hb hsc (src := .caller 1 0) (len := .const 57) (P := arg s₁ 1) (N := 57)
      (show 1 < 3 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
      (.inr ⟨SEED s₁, List.mem_append_left _ (seed_in s₁), whole _⟩) (hk.away_input (seed_in s₁) (whole _))
      h.seed (by taint_decide))
      (RelCT.seq (hk.padStep_ct ha hb hsc (pos := 57 % 136) (by decide) (by taint_decide))
        (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))))) ?_
  refine RelCT.seq (hk.prune_ct (q := HASH) (by decide) (by taint_decide)) (RelCT.seq (RelCT.seq ?_
    (base_ct (s₂ := s₂) hB h)) ?_)
  · exact block_ct (by taint_decide) (fun _ hc _ => WP.mono (base_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (base_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2⟩)
  · exact block_ct (by taint_decide) (fun _ hc _ => WP.mono (wipe_step h hc) fun _ hu => ⟨hu.1, trivial⟩)
      (fun _ hc _ => WP.mono (wipe_step h hc) fun _ hu => ⟨hu.1, trivial⟩)

theorem publicKey_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    ConstantTime isa pkLocal.pre pkLocal.pub (code base') := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have c₂ := push_ctx p₂.1 p₂.2.1 (facts p₂).below
  rw [base_eq hp, rd_eq hp, wr_eq hp] at c₂
  exact ⟨(body_ct hB (facts p₁) hp _ _ _ _ _ _
    ⟨⟨push_ctx p₁.1 p₁.2.1 (facts p₁).below, trivial⟩, ⟨c₂, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The shared contract -/

def pkWide : Contract isa := { pkLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def pkSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pkSatMem
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩ := h
  simp only [pkLocal, pkRd, pkWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩

theorem pkWide_implies : pkWide.Implies (Spec.Ed448.publicKeyContract X86.abi 280) := by
  have a0 : arg pkSatState 0 = 0x1000 := by decide
  have a1 : arg pkSatState 1 = 0x2000 := by decide
  have a2 : arg pkSatState 2 = 0x4000 := by decide
  have e : argAddr pkSatState 0 = 0x8004 := by decide
  have sp : pkSatState.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, pkWide, pkLocal, below, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, e, sp] using pkSatState

theorem publicKey_verified {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    Verified X86.target (code base') (Spec.Ed448.publicKeyContract X86.abi 280) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkLocal.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target (code base') pkLocal :=
    Verified.of_correct (fun _ h => publicKey_ok hB h) (publicKey_ct hB) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86.PublicKey
