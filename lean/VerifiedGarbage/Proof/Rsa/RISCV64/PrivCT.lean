module

import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCorrect
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivTaint
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCT
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCT
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPubCall
public import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_private_checked` on RISC-V: constant time

Two runs are related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each
step, both satisfying the same predicate for the same public data
(`dataOf`): the blocks between the calls by the taint analysis
(`PrivTaint.lean`), and the calls by the callees' constant time
(`RelCT.callEx`), whose public data at the call the correctness facts fix
(`crt_pub`, `pre_pub`, `pub_pub`); what each run satisfies after each step
follows from correctness (`two_post`). The frame's `alloc` and `free` leak
nothing (`relCT_alloc`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post)

/-- Allocating and freeing a buffer leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The public data. -/
def dataOf (s : State) : List (BitVec 64) × List (BitVec 64) × List Nat × Addr :=
  (argRegs.map s.gpr, (List.range 12).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat ++
      Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).map (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : frameBytes = 3247 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_twelve, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_twelve, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hsp]

/-- The public data's facts. -/
structure Same (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < 12, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat =
    Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat =
    Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h3 : s₁.gpr .a3 = s₂.gpr .a3 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.Rsa.bytesAt_length', h3])
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩

/-- On entry, with the public data `d`. -/
def Φ0 (d : List (BitVec 64) × List (BitVec 64) × List Nat × Addr) (s : State) : Prop :=
  (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s ∧ dataOf s = d

/-- Two states for the same public data. -/
theorem same {d} {s₁ s₂ : State} (h₁ : Φ0 d s₁) (h₂ : Φ0 d s₂) : Same s₁ s₂ :=
  same_of (h₁.2.trans h₂.2.symm)

theorem fb_same {s₁ s₂ : State} (S : Same s₁ s₂) : fb s₁ = fb s₂ := by simp only [fb, S.sp]

theorem r_same {s₁ s₂ : State} (S : Same s₁ s₂) {r : Reg} (hr : r ∈ argRegs := by decide) :
    s₁.gpr r = s₂.gpr r := S.gpr r hr

/-! ## The calls -/

theorem crt_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP s₁) (h₂ : PreP s₂) (S : Same s₁ s₂) (A₁ : AtCrt s₁ t₁)
    (A₂ : AtCrt s₂ t₂) : Proof.Bignum.RISCV64.Crt.fnContract.pub (crtEntry s₁ t₁) (crtEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP s → AtCrt s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega)
  have hl : ∀ {s t : State}, AtCrt s t →
      (List.range 10).map (stackArg (crtEntry s t)) = (List.range 10).map fun i => stackArg s (2 + i) :=
    fun A => List.map_congr_left fun i hi => crtEntry_stackArg A (List.mem_range.mp hi)
  refine ⟨fun r hr => ?_, by rw [show (crtEntry s₁ t₁).sp = fb s₁ from A₁.sp,
      show (crtEntry s₂ t₂).sp = fb s₂ from A₂.sp, fb_same S], ?_, ?_⟩
  · rw [g r (fun h => by revert r; decide), g r (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, fb_same S]
    · rw [A₁.a1, A₂.a1, r_same S]
    · rw [A₁.a2, A₂.a2, r_same S]
    · rw [A₁.a3, A₂.a3, r_same S]
    · rw [A₁.a4, A₂.a4, r_same S]
    · rw [A₁.a5, A₂.a5, r_same S]
    · rw [A₁.a6, A₂.a6, S.arg 0 (by decide)]
    · rw [A₁.a7, A₂.a7, S.arg 1 (by decide)]
  · rw [hl A₁, hl A₂]
    exact List.map_congr_left fun i hi => S.arg _ (by have := List.mem_range.mp hi; omega)
  · show Spec.Rsa.bytesAt t₁.mem ((crtEntry s₁ t₁).gpr .a2) ((crtEntry s₁ t₁).gpr .a3).toNat =
      Spec.Rsa.bytesAt t₂.mem ((crtEntry s₂ t₂).gpr .a2) ((crtEntry s₂ t₂).gpr .a3).toNat
    rw [g .a2 (by decide), g .a3 (by decide), g .a2 (by decide), g .a3 (by decide), A₁.a2, A₁.a3, A₂.a2,
      A₂.a3, hn h₁ A₁, hn h₂ A₂, S.n]

theorem pre_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP s₁) (h₂ : PreP s₂) (S : Same s₁ s₂) (A₁ : AtPre s₁ t₁)
    (A₂ : AtPre s₂ t₂) : Proof.Bignum.RISCV64.Pre.fnContract.pub (t₁.callEntry.withRegions [nR s₁] (preWr s₁))
      (t₂.callEntry.withRegions [nR s₂] (preWr s₂)) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP s → AtPre s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega)
  simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), A₁.a0, A₁.a1, A₁.a2, A₁.a3, A₁.a4, A₁.a5, A₂.a0,
    A₂.a1, A₂.a2, A₂.a3, A₂.a4, A₂.a5, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
    State.callEntry_sp, A₁.sp, A₂.sp]
  rw [hn h₁ A₁, hn h₂ A₂, S.n, fb_same S, r_same S (r := .a2), r_same S (r := .a3), S.arg 10 (by decide),
    S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pubEntry_sa {s t : State} (A : AtPubC s t) :
    stackArg (pubEntry s t) 0 = stackArg s 10 ∧ stackArg (pubEntry s t) 1 = stackArg s 11 := by
  have hsp : (pubEntry s t).sp = fb s := A.sp
  refine ⟨?_, ?_⟩
  · show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa0
  · show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa1

theorem pub_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP s₁) (h₂ : PreP s₂) (S : Same s₁ s₂) (A₁ : AtPubC s₁ t₁)
    (A₂ : AtPubC s₂ t₂) : Proof.Bignum.RISCV64.Pub.fnContract.pub (pubEntry s₁ t₁) (pubEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (pubEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have he : ∀ {s t : State}, PreP s → AtPubC s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.ke.symm
      · exact h.es) (by have := h.we; omega)
  obtain ⟨a₁, b₁⟩ := pubEntry_sa A₁
  obtain ⟨a₂, b₂⟩ := pubEntry_sa A₂
  simp only [Proof.Bignum.RISCV64.Pub.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), A₁.a0, A₁.a1,
    A₁.a2, A₁.a3, A₁.a4, A₁.a5, A₁.a6, A₁.a7, A₂.a0, A₂.a1, A₂.a2, A₂.a3, A₂.a4, A₂.a5, A₂.a6, A₂.a7, a₁, b₁, a₂,
    b₂, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp, State.callEntry_sp, A₁.sp, A₂.sp,
    pre_toNat h₁, pre_toNat h₂]
  rw [A₁.pre, A₂.pre, he h₁ A₁, he h₂ A₂, S.n, S.e, fb_same S, r_same S (r := .a0), r_same S (r := .a3),
    r_same S (r := .a4), r_same S (r := .a5), S.arg 10 (by decide), S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The chain -/

/-- The public data. -/
abbrev Data := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

def Φ1 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ u = allocd frameBytes s
def Ψ1 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtCrt s u
def Ψ2 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ Mid s u ∧ crtOut s u
def Ψ3 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtPre s u
def Ψ4 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtPub s u
def Ψ5 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtPubC s u
def Ψ6 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtCmp s u

theorem crt_rel : RelCT isa (Two Ψ1) crtCall fun _ _ => True := by
  unfold crtCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Crt.fn_correct Proof.Bignum.RISCV64.Crt.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := preP_of φ₁.1
  have h₂ := preP_of φ₂.1
  exact ⟨crtRd s₁, crtWr s₁, crtRd s₂, crtWr s₂, crt_pre h₁ A₁, crt_pre h₂ A₂,
    crt_pub h₁ h₂ (same φ₁ φ₂) A₁ A₂, (crt_covers h₁ A₁).1, (crt_covers h₁ A₁).2, (crt_covers h₂ A₂).1,
    (crt_covers h₂ A₂).2⟩

theorem pre_rel : RelCT isa (Two Ψ3) preCall fun _ _ => True := by
  unfold preCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Pre.fn_correct Proof.Bignum.RISCV64.Pre.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := preP_of φ₁.1
  have h₂ := preP_of φ₂.1
  exact ⟨[nR s₁], preWr s₁, [nR s₂], preWr s₂, pre_pre h₁ A₁, pre_pre h₂ A₂,
    pre_pub h₁ h₂ (same φ₁ φ₂) A₁ A₂, (pre_covers h₁ A₁).1, (pre_covers h₁ A₁).2, (pre_covers h₂ A₂).1,
    (pre_covers h₂ A₂).2⟩

theorem pub_rel : RelCT isa (Two Ψ5) pubCall fun _ _ => True := by
  unfold pubCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Pub.fn_correct Proof.Bignum.RISCV64.Pub.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := preP_of φ₁.1
  have h₂ := preP_of φ₂.1
  obtain ⟨p₁, c₁, w₁⟩ := pub_pre h₁ A₁
  obtain ⟨p₂, c₂, w₂⟩ := pub_pre h₂ A₂
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, pub_pub h₁ h₂ (same φ₁ φ₂) A₁ A₂, c₁, w₁, c₂, w₂⟩

theorem pins_Ψ6 : Pins Ψ6 [.s1, .s3, .s6] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := same φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [A₁.s1, A₂.s1, r_same S]
  · rw [A₁.s3, A₂.s3, r_same S]
  · rw [A₁.s6, A₂.s6, r_same S]

theorem body_rel : RelCT isa (Two Φ1) body fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_post (Ψ := Ψ1) (setup_taint Φ1) fun d u ⟨s, φ, e⟩ =>
    e ▸ WP.mono (setup_ok (preP_of φ.1)) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ2) crt_rel fun d u ⟨s, φ, A⟩ =>
    crtCall_ok (preP_of φ.1) A fun v M C => ⟨s, φ, M, C⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ3) (preArgs_taint Ψ2) fun d u ⟨s, φ, M, C⟩ =>
    WP.mono (preArgs_ok (preP_of φ.1) M C) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ4) pre_rel fun d u ⟨s, φ, A⟩ =>
    preCall_ok (preP_of φ.1) A fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ5) (pubArgs_taint Ψ4) fun d u ⟨s, φ, A⟩ =>
    WP.mono (pubArgs_ok (preP_of φ.1) A) fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ6) pub_rel fun d u ⟨s, φ, A⟩ =>
    pubCall_ok (preP_of φ.1) A fun v B => ⟨s, φ, B⟩) ?_
  exact tail_taint pins_Ψ6

theorem code_rel : RelCT isa (Two Φ0) code fun _ _ => True :=
  relCT_alloc (body_rel.mono (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
    ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocd, hsp]⟩) fun _ _ h => h)

theorem code_ct : ConstantTime isa (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre
    (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.Rsa.RISCV64.Priv
