import VerifiedGarbage.Proof.Ed448.X86.SignCached.Body
import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 signing with a cached key on x86 (32-bit): constant time, and `Verified`

As for the public key: two runs from the same pointers, lengths and `esp`
set up the same arguments for every call, each callee is constant time under
its own contract (the sponge functions', `scalarReduceLocal`,
`scalarMulAddLocal` and `scalarBaseLocal`), and the blocks between the calls
address memory only through `esp` (or `scratch`, the same in both runs).
`signCached_verified`: for any `base` meeting `scalarBaseLocal`
(`CalleeOk`), `code base` meets `Spec.Ed448.signCachedContract X86.abi 280`.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed448.X86.Shake (callWith hdrAt pruneAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Ctx.zeroWords)

variable {σ₁ σ₂ : State} {g₁ g₂ : Reg → BitVec 32}

theorem base_eq (hp : scLocal.pub σ₁ σ₂) : base σ₂ = base σ₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : scLocal.pub σ₁ σ₂) : scRd σ₂ = scRd σ₁ := by
  obtain ⟨e, _, a1, a2, a3, a4, a5, a6, _⟩ := hp
  simp only [scRd, SEED, PK, CTX, MSG, argAddr, e, a1, a2, a3, a4, a5, a6]

theorem wr_eq (hp : scLocal.pub σ₁ σ₂) : scWr σ₂ = scWr σ₁ := by
  obtain ⟨_, a0, _, _, _, _, _, _, a7⟩ := hp
  simp only [scWr, OUT, a0, a7]

theorem args₂ (hp : scLocal.pub σ₁ σ₂) : Shake.Args (base σ₁) 8 (arg σ₁) σ₂.mem := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, a6, a7⟩ := id hp
  intro i hi
  rw [← base_eq hp, args_val σ₂ 8 i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

abbrev Two₁ (σ₁ σ₂ : State) (g₁ g₂ : Reg → BitVec 32) :=
  Two (base σ₁) (scRd σ₁) (scWr σ₁) g₁ g₂ σ₁.mem σ₂.mem

section
variable {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts σ₁) (hp : scLocal.pub σ₁ σ₂)

include h in
/-- Three to five equal slots, from the same values in both runs. -/
theorem eq_args {a b : State} (ea : a.gpr .esp = base σ₁) (eb : b.gpr .esp = base σ₁) {k : Nat} (hk6 : k ≤ 6)
    (hs : ∀ i < k, Whole.slots (base σ₁) a i = Whole.slots (base σ₁) b i) (ar aw br bw : List Region) :
    ∀ i < k, arg (a.callEntry.withRegions ar aw) i = arg (b.callEntry.withRegions br bw) i :=
  (kit h).args_eq ea eb hk6 hs ar aw br bw

include h hp in
theorem seed_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) seedHash (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 8
  have hb := args₂ hp
  have hsc := scr_at σ₁
  unfold seedHash
  exact RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide))
    (RelCT.seq (hk.first_ct ha hb hsc (src := .caller 1 0) (len := .const 57) (P := arg σ₁ 1) (N := 57)
      (show 1 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
      (.inr ⟨SEED σ₁, List.mem_append_left _ (seed_in σ₁), whole _⟩) (hk.away_input (seed_in σ₁) (whole _))
      h.seed (by taint_decide))
      (RelCT.seq (hk.padStep_ct ha hb hsc (pos := 57 % 136) (by decide) (by taint_decide))
        (hk.sqzStep_ct ha hb hsc (d := S) (by decide) (by decide) (by taint_decide))))

include h hp in
theorem nonce_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) nonceHash (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 8
  have hb := args₂ hp
  have hsc := scr_at σ₁
  have fa := hk.fr_addr (d := HASH) (by decide)
  have fk := hk.fr_addr (d := K) (by decide)
  unfold nonceHash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HASH) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in σ₁), whole _⟩) (hk.away_input (ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .frame K) (len := .const 57)
    (P := base σ₁ + BitVec.ofNat 32 K) (N := 57) trivial trivial rfl rfl
    (by rw [fk]; exact .inl (frame_within _ (by decide)))
    (by rw [fk]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide))
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .caller 6 0) (P := arg σ₁ 5)
    (N := (arg σ₁ 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in σ₁), whole _⟩) (hk.away_input (msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

include h hp in
theorem chal_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) chalHash (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 8
  have hb := args₂ hp
  have hsc := scr_at σ₁
  have fa := hk.fr_addr (d := HASH) (by decide)
  unfold chalHash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HASH) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in σ₁), whole _⟩) (hk.away_input (ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 0 0) (len := .const 57) (P := arg σ₁ 0) (N := 57)
    (show 0 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_right _ (out_in σ₁), out1_within σ₁⟩)
    (hk.away_output (out_in σ₁) h.oc (out1_within σ₁)) (by have := h.out; omega)
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 2 0) (len := .const 57) (P := arg σ₁ 2) (N := 57)
    (show 2 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (pk_in σ₁), whole _⟩) (hk.away_input (pk_in σ₁) (whole _)) h.pk
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .caller 6 0) (P := arg σ₁ 5)
    (N := (arg σ₁ 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in σ₁), whole _⟩) (hk.away_input (msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

include h hp in
theorem r_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := RSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (r_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (r_setup h hc (args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
      (fun _ _ _ hc hs => r_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (r_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (r_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include hB h hp in
theorem b_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith baseArgs "vg_ed448_scalar_base" base') (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := BSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (b_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (b_setup h hc (args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct hB.ok hB.ct (fun _ _ _ hc hs => b_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (b_call h hB hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (b_call h hB hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include h hp in
theorem k_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := KSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (k_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (k_setup h hc (args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
      (fun _ _ _ hc hs => k_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (k_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (k_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include h hp in
theorem m_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := MSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (m_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (m_setup h hc (args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarMulAdd_ok s h) Proof.Ed448.X86.scalarMulAdd_ct
      (fun _ _ _ hc hs => m_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := eq_args h ea eb (k := 5) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm,
            ha.a3.trans hb.a3.symm, ha.a4.trans hb.a4.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide),
          e 3 (by decide), e 4 (by decide)⟩)
      (fun _ hc hs => WP.mono (m_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (m_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include hB h hp in
theorem body_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (body base') (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 8
  have hb := args₂ hp
  have hcl : (arg σ₁ 4).toNat < 256 := by have := h.ctxlen; omega
  have hdr := hk.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 4) (off := HASH) (by decide) hcl (by decide)
    (by taint_decide)
  unfold body
  exact (seed_ct h hp).seq ((hk.prune_ct (q := S) (by decide) (by taint_decide)).seq (hdr.seq
    ((nonce_ct h hp).seq ((r_ct h hp).seq ((b_ct hB h hp).seq (hdr.seq ((chal_ct h hp).seq ((k_ct h hp).seq
    ((m_ct h hp).seq (block_ct (by taint_decide)
      (fun _ hc _ => WP.mono (Whole.Ctx.zeroWords hc (start := 6) (count := 58) hk.frame (by decide))
        fun _ hu => ⟨hu.1, trivial⟩)
      (fun _ hc _ => WP.mono (Whole.Ctx.zeroWords hc (start := 6) (count := 58) hk.frame (by decide))
        fun _ hu => ⟨hu.1, trivial⟩)))))))))))

end

theorem signCached_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    ConstantTime isa scLocal.pre scLocal.pub (code base') := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have c₂ := push_ctx p₂.1 p₂.2.1 (facts p₂).below
  rw [base_eq hp, rd_eq hp, wr_eq hp] at c₂
  exact ⟨(body_ct hB (facts p₁) hp _ _ _ _ _ _
    ⟨⟨push_ctx p₁.1 p₁.2.1 (facts p₁).below, trivial⟩, ⟨c₂, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The shared contract -/

def scWide : Contract isa := { scLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 114⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let msg : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scr : Region := ⟨(arg s 7).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, ctx, msg] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
      (arg s 7).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
      Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57) ∧
      (arg s 4).toNat ≤ 255 }

theorem scWide_pre (s : State) (h : scWide.pre s) :
    scLocal.pre (s.withRegions (scRd s) (scWr s)) := by
  obtain ⟨_, _, a1, a2, a3, a4, a5, a6, ko, a8, a9, a10, a11, a12, a13, a14, ks, kp, kx, km, kc,
    b1, b2, b3, b4, b5, b6, nb, b8, b9, b10⟩ := h
  simp only [scLocal, scRd, scWr, SEED, PK, CTX, MSG, OUT, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, below,
    Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, a1, a2, a3, a4, a5, a6, ko, a8, a9, a10, a11, a12, a13, a14, ks, kp, kx, km, kc,
    b1, b2, b3, b4, b5, b6, nb, b8, b9, b10⟩

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, the arguments at `0x9004`, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3039 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else if a = 0x900d then 0x30 else
    if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9022 then 0x01 else 0

theorem sat_seed : Spec.Ed448.bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed448.bytesAt satMem 0x3000 57 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3039 from by omega, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk' : Spec.Ed448.bytesAt satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt satMem 0x2000 57) := by
  rw [sat_seed, sat_key]
  rfl

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩, ⟨0x9004, 32⟩]

theorem sat_pk : Spec.Ed448.bytesAt satMem ((arg satState 2).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt satMem ((arg satState 1).setWidth 64) 57) := by
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0x3000 := by decide
  rw [a1, a2]
  exact sat_pk'

theorem sat : ∃ s, (Spec.Ed448.signCachedContract X86.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState]
    sig_and_intros
    all_goals try exact sat_pk
    all_goals decide +kernel

theorem scWide_implies : scWide.Implies (Spec.Ed448.signCachedContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, scWide, scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, scWide, scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, scWide, scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  sat := sat

theorem signCached_verified {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    Verified X86.target (code base') (Spec.Ed448.signCachedContract X86.abi 280) := by
  have hsat := scWide_implies.sat_left
  have satLocal : ∃ s, scLocal.pre s := hsat.elim fun s h => ⟨_, scWide_pre s h⟩
  have verifiedLocal : Verified X86.target (code base') scLocal :=
    Verified.of_correct (fun _ h => signCached_ok hB h) (signCached_ct hB) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scRd scWr scWide_pre
    ?_ ?_ ?_ ?_ hsat) scWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scRd, scWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [scWide, scLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86.SignCached
