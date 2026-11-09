module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedShort
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStreamCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro

meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedShort
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro

-- separate module: the relational proofs cost more to check than their imports.

/-! # The staged small-secret sampler: constant time -/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

namespace RejBoundedShort

variable {pos : BitVec 64}

open RejBoundedCT

section
variable {σ₁ σ₂ : State} (hq : rbK.pub σ₁ σ₂)
include hq

theorem pub_eta : etaOf σ₁ = etaOf σ₂ := by simp only [etaOf, hq.2.1]
theorem pub_sp : spOf σ₁ pos = spOf σ₂ pos := congrArg (fun P : Sp => {P with prm := pos}) (RejBounded.pub_sp hq)
theorem pub_aP : σ₁.gpr .rdx = σ₂.gpr .rdx := hq.2.2.1

theorem spPub : SpPub (spOf σ₁ pos) (spOf σ₂ pos) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, rfl, hq.2.2.2.2.1⟩

theorem initPub : SpongeStream.Public (spInit σ₁) (spInit σ₂) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, hq.2.2.2.2.1⟩

/-- The half-bytes of the output are accepted alike in both runs. -/
theorem pub_oks : (X σ₁).map (hbOks (etaOf σ₁)) = (X σ₂).map (hbOks (etaOf σ₁)) := by
  have h := hq.2.2.2.2.2
  rw [← pub_eta hq] at h
  exact leak_hbOks h (B := 272) (by decide)

theorem pub_len (t : Nat) : (Lt σ₁ t).length = (Lt σ₂ t).length := by
  simp only [Lt]
  rw [← pub_eta hq]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, pub_oks hq])

theorem pub_ok {t : Nat} (ht : t < 272) :
    hbOks (etaOf σ₁) ((X σ₁).getD t 0) = hbOks (etaOf σ₁) ((X σ₂).getD t 0) := by
  have h := congrArg (fun L => L[t]?) (pub_oks hq)
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < (X σ₁).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X σ₂).length by rw [X_length]; exact ht), Option.map_some,
    Option.some.injEq] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < (X σ₁).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X σ₂).length by rw [X_length]; exact ht)]
  exact h

end

/-- Two runs at iteration `t` of the loop for `η`, `n = 272 - t` iterations
from the end. -/
def LI (pos : BitVec 64) (η n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, rbK.pre σ₁ ∧ rbK.pre σ₂ ∧ rbK.pub σ₁ σ₂ ∧ etaOf σ₁ = η ∧ n = 272 - t ∧ t < 272 ∧
    LAt σ₁ pos t s₁ ∧ LAt σ₂ pos t s₂

theorem bpre {σ : State} (hp : rbK.pre σ) {t : Nat} (ht : t < 272) {s : State} (h : LAt σ pos t s) :
    BPre s (σ.gpr .rdx) (Lt σ t) :=
  ⟨h.env.rbp, h.rdi, Lt_length_le t, .of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by rw [h.rsi, at_add]; exact inScrRd (spOk hp) h.env (by omega_arith)⟩

theorem li_brel {η n : Nat} {s₁ s₂ : State} (h : LI pos η n s₁ s₂) : BRel η s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, he, _, ht, l₁, l₂⟩ := h
  subst he
  refine ⟨σ₁.gpr .rdx, Lt σ₁ t, Lt σ₂ t, pub_len hq t, bpre p₁ ht l₁, by rw [pub_aP hq]; exact bpre p₂ ht l₂,
    by rw [l₁.rsi, l₂.rsi, pub_sp hq], by rw [l₁.rcx, l₂.rcx], ?_⟩
  rw [out_byte l₁ ht, out_byte l₂ ht]
  exact pub_ok hq ht

theorem lat_step' {σ : State} (hp : rbK.pre σ) {η t : Nat} (he : etaOf σ = η) {s : State} (ht : t < 272)
    (h : LAt σ pos t s) :
    WP isa (rbBody η) s fun s' => LAt σ pos (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (272 - t) - 1 == 0) := by
  subst he; exact lat_step hp ht h

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
  (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
  (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
    (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
  (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true)
include hη c1 c2 c3

theorem loop_ct (n : Nat) :
    RelCT isa (LI pos η n) (.loop (rbBody η) .ne) (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ pos 272 s) := by
  refine RelCT.loop (M := isa) (LI pos η) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, rbK.pre p.1 ∧ etaOf p.1 = η ∧ p.2 < 272 ∧
      LAt p.1 pos p.2 x → LAt p.1 pos (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (272 - p.2) - 1 == 0))
    (RelCT.mono (body_ct hη c1 c2 c3) (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, he, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => lat_step' hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2) ⟨(σ₁, t), p₁, he, ht, l₁⟩,
      WP.all' (fun p hp' => lat_step' hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2)
        ⟨(σ₂, t), p₂, by rw [← pub_eta hq, he], ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, he, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, he, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, by rw [← pub_eta hq, he], ht, l₂⟩
    have ez : (BitVec.ofNat 64 (272 - t) - 1 == 0) = decide (t + 1 = 272) := by
      rw [ofNat64_pred (by omega_arith) (by omega_arith), ofNat64_beq_zero (by omega_arith)]
      exact decide_eq_decide.mpr (by omega_arith)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 272 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨he, l₁'⟩, ⟨by rw [← pub_eta hq]; exact he, l₂'⟩⟩
    · have : t + 1 ≠ 272 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨272 - (t + 1), by omega_arith, σ₁, σ₂, t + 1, p₁, p₂, hq, he, rfl, by omega_arith, l₁', l₂'⟩

/-- After the first block of the loop's setup. -/
def IA (σ : State) (pos : BitVec 64) (s : State) : Prop :=
  Env (spOf σ pos) σ s ∧ bytesAt s.mem ((spOf σ pos).at' 840) 272 = X σ ∧ s.gpr .rsi = (spOf σ pos).at' 840 ∧
    s.gpr .rdi = 0 ∧ SpongeStream.Stream 136 272 (spOf σ pos) σ pos s

omit hη c1 c2 c3 in
theorem latB {σ s : State} (h : IA σ pos s) : WP isa (.block [.mov32 .rcx (.imm 272)]) s (LAt σ pos 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 272)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.1.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.2.1, by rw [k2.gpr (by decide), h.2.2.1]; simp,
    by rw [k2.gpr (by decide), h.2.2.2.1]; rfl, hcx, by rw [hm2]; exact stored_nil _ _, h.2.2.2.2.mem_eq hm2⟩

omit hη c1 c2 c3 in
theorem hok : ∀ σ, rbK.pre σ → SpOk (spOf σ pos) σ := fun _ hp => spOk hp

omit hη c1 c2 c3 in
theorem hpub : ∀ σ₁ σ₂, rbK.pre σ₁ → rbK.pre σ₂ → rbK.pub σ₁ σ₂ → SpPub (spOf σ₁ pos) (spOf σ₂ pos) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The loop for `η`, in runs of a call with that `η`. -/
theorem rbLoop_ct : RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ J6 136 272 (spOf σ pos) σ s ∧ SpongeStream.Stream 136 272 (spOf σ pos) σ pos s)
    (rbLoopCount η 272) (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ pos 272 s) := by
  refine RelCT.seq (relInv (I' := fun σ s => etaOf σ = η ∧ IA σ pos s) (fun σ s _ h => WP.mono (lat0 h.2.1 h.2.2) fun _ h' =>
      ⟨h.1, h'⟩)
    (taintSp (f := fun σ => spOf σ pos) hpub (J := fun P σ s => etaOf σ = η ∧ J6 136 272 P σ s ∧ SpongeStream.Stream 136 272 P σ pos s) (fun _ _ h => h.2.1.env) []
      nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => etaOf σ = η ∧ LAt σ pos 0 s)
        (fun σ s _ h => WP.mono (latB h.2) fun _ h' => ⟨h.1, h'⟩)
        (taintSp (f := fun σ => spOf σ pos) hpub (J := fun P σ s => etaOf σ = η ∧ Env P σ s ∧
          bytesAt s.mem (P.at' 840) 272 = X σ ∧ s.gpr .rsi = P.at' 840 ∧ s.gpr .rdi = 0 ∧ SpongeStream.Stream 136 272 P σ pos s)
          (fun _ _ h => h.2.1) [] nil_regs (by taint_decide)))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨he, l₁⟩, ⟨_, l₂⟩⟩ =>
        ⟨σ₁, σ₂, 0, p₁, p₂, hq, he, rfl, by omega_arith, l₁, l₂⟩)
      (loop_ct hη c1 c2 c3 272))

end


/-- The entry comparison preserves every part of the sampler's public input. -/
theorem entry_pub {σ₁ σ₂ x y : State} (hq : rbK.pub σ₁ σ₂)
    (h₁ : Entry σ₁ x) (h₂ : Entry σ₂ y) : rbK.pub x y := by
  refine ⟨h₁.seed.trans (hq.1.trans h₂.seed.symm), h₁.eta.trans (hq.2.1.trans h₂.eta.symm),
    h₁.out.trans (hq.2.2.1.trans h₂.out.symm), h₁.scratch.trans (hq.2.2.2.1.trans h₂.scratch.symm),
    (h₁.preserved.1 _ (by decide)).trans (hq.2.2.2.2.1.trans (h₂.preserved.1 _ (by decide)).symm), ?_⟩
  show Spec.MlDsa.rejBoundedLeak (etaOf x) (bytesAt x.mem (x.gpr .rdi) 66) =
    Spec.MlDsa.rejBoundedLeak (etaOf y) (bytesAt y.mem (y.gpr .rdi) 66)
  rw [etaOf, etaOf, h₁.eta, h₂.eta, h₁.seed, h₂.seed, h₁.bytes, h₂.bytes]
  exact hq.2.2.2.2.2

/-- The prefix state, after testing whether it filled the polynomial. -/
structure Ready (σ : State) (pos : BitVec 64) (s : State) : Prop where
  lat : LAt σ pos 272 s
  zf : s.zf = some (BitVec.ofNat 64 (Lt σ 272).length == 256)

abbrev RR (η : Nat) (I : State → State → Prop) :=
  Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ I σ s

theorem ready_ok {σ s : State} (h : LAt σ pos 272 s) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s (Ready σ pos) := by
  refine WP.mono (WP.keep [.rdi] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.zf = some (s.gpr .rdi - 256 == 0)) (by xrun; rfl) (by decide))
    fun s' ⟨⟨hm, hd, hz⟩, hk⟩ => ?_
  refine ⟨⟨h.env.keep hm (hk.mono (by decide)), by rw [hm]; exact h.out,
    (hk.gpr (by decide)).trans h.rsi, hd.trans h.rdi, (hk.gpr (by decide)).trans h.rcx,
    by rw [hm]; exact h.stored, h.stream.mem_eq hm⟩, ?_⟩
  rw [hz, h.rdi]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  rfl

theorem cmp_ct {η : Nat} : RelCT isa (RR η fun σ => LAt σ pos 272)
    (.block [.alu .cmp .rdi (.imm 256)]) (RR η fun σ => Ready σ pos) :=
  relInv (fun _ _ _ h => WP.mono (ready_ok h.2) fun _ h' => ⟨h.1, h'⟩)
    (taintRel [] nil_regs (by taint_decide))

theorem continue_ct {η : Nat} (hη : η = 2 ∨ η = 4) :
    RelCT isa (RR η fun σ => Ready σ pos) (rbContinue η) (fun _ _ => True) := by
  have hints : ∃ h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true ∧
      (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
        (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true ∧
      (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true := by
    rcases hη with rfl | rfl <;> exact ⟨_, _, _, by taint_decide, by taint_decide, by taint_decide⟩
  obtain ⟨_, _, _, c1, c2, c3⟩ := hints
  have resume_hint : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp])
        (.block (resumeArgs 1112 272 ++ [.mov32 .r12 (.imm (BitVec.ofNat 32 η))])) hc).isSome = true := by
    rcases hη with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hresume⟩ := resume_hint

  refine RelCT.seq (relInv (I' := fun σ s => etaOf σ = η ∧ RejBounded.LAt σ 272 s)
    (fun σ s hp h => WP.mono (by simpa only [h.1] using continue_args_ok hp h.2.lat) fun _ h' => ⟨h.1, h'⟩) ?_)
    (RelCT.seq (RelCT.mono (RejBounded.loop_ct hη c1 c2 c3 272) ?_ (fun _ _ h => h)) ?_)
  · refine RelCT.seq (RelCT.mono (SpongeStream.count_ct hok hpub (rate := 136) (done := 272) (pos := pos)) ?_ (fun _ _ h => h))
      (RelCT.seq (SpongeStream.more_ct hok hpub (rate := 136) (offset := 1112) (len := 272) (done := 272) (pos := pos)
        (.inl rfl) (by decide) (fun _ _ => rfl) (by decide) (by taint_decide))
        (taintSp hpub (J := fun P σ s => Env P σ s) (fun _ _ h => h) [] nil_regs hresume))
    intro x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.2.lat.env, h₁.2.lat.stream⟩, ⟨h₂.2.lat.env, h₂.2.lat.stream⟩⟩
  · intro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨he, l₁⟩, ⟨_, l₂⟩⟩
    exact ⟨σ₁, σ₂, 272, p₁, p₂, hq, he, rfl, by decide, l₁, l₂⟩
  · exact taintSp RejBounded.hpub (c := .block (retJ ++ epi))
      (J := fun _ σ s => RejBounded.LAt σ 544 s)
      (fun _ _ h => h.env) [] nil_regs (by taint_decide)

theorem finish_ct {η : Nat} (hη : η = 2 ∨ η = 4) : RelCT isa (RR η fun σ => LAt σ pos 272)
    (.seq (.block [.alu .cmp .rdi (.imm 256)])
      (.ite .e (.block (retJ ++ epi)) (rbContinue η))) (fun _ _ => True) := by
  refine RelCT.seq cmp_ct (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => ?_) ?_ ?_)
  · show x.zf = y.zf
    rw [h₁.2.zf, h₂.2.zf, pub_len hq]
  · exact RelCT.mono (taintSp hpub (J := fun _ σ s => etaOf σ = η ∧ Ready σ pos s)
      (fun _ _ h => h.2.lat.env) [] nil_regs (by taint_decide)) (fun _ _ h => h.1) (fun _ _ h => h)
  · exact RelCT.mono (continue_ct hη) (fun _ _ h => h.1) (fun _ _ h => h)

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
  (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
  (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
    (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
  (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true)
include hη c1 c2 c3

/-- The body for a fixed public parameter. -/
theorem short_ct : ConstantTime isa (fun σ => rbK.pre σ ∧ etaOf σ = η) rbK.pub (rbShort η) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spInit σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp.1)
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (SpongeStream.stream_ct (fun _ h => initOk h.1) (fun _ _ _ _ h => initPub h)
    (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  apply RelCT.exists_
  intro pos
  refine RelCT.seq (RelCT.mono (rbLoop_ct (pos := pos) hη c1 c2 c3) ?_ (fun _ _ h => h)) (finish_ct hη)
  intro x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩
  exact ⟨σ₁, σ₂, p₁.1, p₂.1, hq, ⟨p₁.2, h₁⟩, ⟨p₂.2, h₂⟩⟩

/-- A relational wrapper for the two fixed-parameter bodies. -/
theorem short_rel : RelCT isa (fun x y => rbK.pre x ∧ rbK.pre y ∧ rbK.pub x y ∧
    etaOf x = η ∧ etaOf y = η) (rbShort η) (fun _ _ => True) := by
  intro x y t₁ t₂ x' y' ⟨p₁, p₂, hq, e₁, e₂⟩ h₁ h₂
  exact ⟨short_ct hη c1 c2 c3 x y t₁ t₂ x' y' ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ hq h₁ h₂, trivial⟩

end

/-- Both branches use only the sampler's existing public input and leak. -/
theorem ct : ConstantTime isa rbK.pre rbK.pub rejBoundedShort := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => Entry σ s ∧ s.zf = some ((σ.gpr .rsi).setWidth 32 - 2 == 0))
    (fun σ s hp h => by subst h; exact entry_cmp_ok hp)
    (taintRel [] nil_regs (by taint_decide))) (RelCT.ite
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
        show x.zf = y.zf; rw [h₁.2, h₂.2, hq.2.1]) ?_ ?_))
  · refine RelCT.mono (short_rel (.inl rfl) (by taint_decide) (by taint_decide) (by taint_decide)) ?_ (fun _ _ h => h)
    intro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩
    have he : etaOf σ₁ = 2 := by
      rcases eta p₁ with h2 | h4
      · exact h2
      · have hv : (σ₁.gpr .rsi).setWidth 32 = BitVec.ofNat 32 (etaOf σ₁) := by
          simp only [etaOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        have hz : x.zf = some true := hb
        rw [h₁.2, hv, h4] at hz
        contradiction
    exact ⟨h₁.1.pre, h₂.1.pre, entry_pub hq h₁.1 h₂.1,
      (congrArg BitVec.toNat h₁.1.eta).trans he,
      (congrArg BitVec.toNat h₂.1.eta).trans ((pub_eta hq).symm.trans he)⟩
  · refine RelCT.mono (short_rel (.inr rfl) (by taint_decide) (by taint_decide) (by taint_decide)) ?_ (fun _ _ h => h)
    intro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩
    have he : etaOf σ₁ = 4 := by
      rcases eta p₁ with h2 | h4
      · have hv : (σ₁.gpr .rsi).setWidth 32 = BitVec.ofNat 32 (etaOf σ₁) := by
          simp only [etaOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        have hz : x.zf = some false := hb
        rw [h₁.2, hv, h2] at hz
        contradiction
      · exact h4
    exact ⟨h₁.1.pre, h₂.1.pre, entry_pub hq h₁.1 h₂.1,
      (congrArg BitVec.toNat h₁.1.eta).trans he,
      (congrArg BitVec.toNat h₂.1.eta).trans ((pub_eta hq).symm.trans he)⟩

theorem verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.rejBoundedShort (Proof.MlDsa.rejBoundedContract X86_64.abi 16) :=
  Verified.of_correct correct ct
    { pre := by sig_implies_pre [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, rbK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, rbK, X86_64.abi, X86_64.argRegs]
        dsimp only [rbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
            show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
            rw [rejBounded_some _ hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
              rw [rejBounded_none _ (B := 544) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, rbK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, hb⟩
      sat := by sig_implies_sat [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, rbK, X86_64.abi,
        X86_64.argRegs] [rbSat] using rbSat }

end RejBoundedShort
end VG.Proof.MlDsa.X86_64.Sample
