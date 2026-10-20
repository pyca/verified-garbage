module

public import VerifiedGarbage.Proof.MdStream.X86_64.OneShot
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86_64.OneShot
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# One-shot Merkle–Damgård digests on x86-64: constant time

The body is constant time for any compression function (`CalleeOk`), so it
is proven once for every implementation. As for the streaming `update`
(`Proof/MdStream/X86_64/UpdateCT.lean`), the taint analysis cannot look
into the compression function, which saves our registers in memory it also
writes secrets to, so we relate two runs (`RelCT`). Between the pieces, the
correctness of each piece in each run determines our registers from the
public arguments alone. The pieces between the calls are constant time by
the taint analysis (`Taints`, checked for each hash function's code), and
the calls by `compressWith_rel`.
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64.OneShot

open VG VG.X86_64 VG.Impl.MdStream.X86_64 VG.Impl.MdStream.X86_64.OneShot

/-- The registers that hold public values between the pieces. -/
abbrev pubRegs : List Reg := [.rbx, .r15, .rbp, .r12, .rsp]

/-- What the taint analysis proves of the pieces of `body` between the calls,
for one hash function's code: each is `⟨_, by taint_decide⟩`. -/
structure Taints (P : Params) : Prop where
  setup : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block (setup P)) hc).isSome = true
  wholeHead : ∃ hc, (taint.check (Taint.ofRegs pubRegs) (.block (wholeHead P)) hc).isSome = true
  wholeEnd : ∃ hc, (taint.check (Taint.ofRegs (.r13 :: .r14 :: pubRegs)) (.block (wholeEnd P)) hc).isSome = true
  zeroBuf : ∃ hc, (taint.check (Taint.ofRegs pubRegs) (.block (zeroBuf P)) hc).isSome = true
  copyTail : ∃ hc, (taint.check (Taint.ofRegs (.r13 :: pubRegs)) (copyTail P) hc).isSome = true
  cmpLen : ∃ hc, (taint.check (Taint.ofRegs (.r10 :: pubRegs)) (.block (cmpLen P)) hc).isSome = true
  blkArg : ∃ hc, (taint.check (Taint.ofRegs pubRegs) (.block (blkArg P)) hc).isSome = true
  lenArg : ∃ hc, (taint.check (Taint.ofRegs pubRegs) (.block (P.len ++ Impl.MdStream.X86_64.OneShot.blkArg P)) hc).isSome = true
  finish : ∃ hc, (taint.check (Taint.ofRegs pubRegs) (.block (finish P)) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.len {s₀ s₀' : State} (hq : PubEq s₀ s₀') : len s₀ = len s₀' := congrArg BitVec.toNat hq.rsi

theorem Mid.agree {P : Params} {s₀ s₀' : State} (hq : PubEq s₀ s₀') {t t' : State} (h : Mid P s₀ t)
    (h' : Mid P s₀' t') : ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rcx
  · rw [h.r15, h'.r15, show sb s₀ = sb s₀' from hq.rcx]
  · rw [h.rbp, h'.rbp]; exact hq.rdx
  · rw [h.r12, h'.r12]; exact hq.rsi
  · rw [h.rsp, h'.rsp]; exact hq.rsp

/-- A piece the taint analysis proves constant time from registers that agree,
with what its correctness gives in each run. -/
theorem piece {s₀ s₀' : State} {X Y : State → State → Prop} {c : Prog isa} {rs : List Reg}
    {hc : VG.Taint.Hint X86_64.Taint.T} (ht : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (ha : ∀ s₁ s₂, X s₀ s₁ → X s₀' s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw₁ : ∀ t, X s₀ t → WP isa c t (Y s₀)) (hw₂ : ∀ t, X s₀' t → WP isa c t (Y s₀')) :
    RelCT isa (fun s₁ s₂ => X s₀ s₁ ∧ X s₀' s₂) c fun s₁ s₂ => Y s₀ s₁ ∧ Y s₀' s₂ :=
  ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (ha s₁ s₂ h.1 h.2)) ht).wp
    fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-! ## What each run keeps between the pieces -/

section
variable (P : Params) (σ t : State)

abbrev J1 : Prop := Mid P σ t ∧ t.gpr .r13 = dp σ ∧ t.gpr .rdi = sb σ
abbrev J2 : Prop := Mid P σ t ∧ t.gpr .r13 = dp σ
abbrev J3 : Prop := J2 P σ t ∧ t.gpr .r14 = BitVec.ofNat 64 (len σ / P.B) ∧ t.zf = some (decide (len σ / P.B = 0))
abbrev J3z : Prop := J2 P σ t ∧ len σ / P.B = 0
abbrev J3n : Prop := J2 P σ t ∧ t.gpr .r14 = BitVec.ofNat 64 (len σ / P.B) ∧ len σ / P.B ≠ 0
abbrev J4 : Prop := J3n P σ t ∧ t.gpr .rsi = dp σ
abbrev J5 : Prop := J2 P σ t ∧ t.gpr .r14 = BitVec.ofNat 64 (len σ / P.B)
abbrev J6 : Prop := Mid P σ t ∧ t.gpr .r13 = dp σ + BitVec.ofNat 64 (whl P σ)
abbrev J7 : Prop := J6 P σ t ∧ Blk P σ 0 t.mem
abbrev J8 : Prop := Mid P σ t ∧ t.gpr .r10 = BitVec.ofNat 64 (rem P σ)
abbrev J9 : Prop := Mid P σ t ∧ t.cf = some (decide (rem P σ < P.B - P.L))
abbrev JA : Prop := Mid P σ t ∧ t.gpr .rsi = sb σ + BitVec.ofNat 64 P.N

end

theorem body_rel {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    (ht : Taints P) {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false) (hin : init.noCalls = true)
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) init hc).isSome = true)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ s₀' : State} (hp : Pre P D s₀)
    (hp' : Pre P D s₀') (hq : PubEq s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (body P init name code) fun _ _ => True := by
  have hl := hq.len
  have hsb : sb s₀ = sb s₀' := hq.rcx
  have hdp : dp s₀ = dp s₀' := hq.rdi
  have ag : ∀ {t t' : State}, Mid P s₀ t → Mid P s₀' t' → ∀ r ∈ pubRegs, t.gpr r = t'.gpr r :=
    fun h h' => Mid.agree hq h h'
  obtain ⟨_, tSetup⟩ := ht.setup
  obtain ⟨_, tInit⟩ := hict
  obtain ⟨_, tHead⟩ := ht.wholeHead
  obtain ⟨_, tEnd⟩ := ht.wholeEnd
  obtain ⟨_, tZero⟩ := ht.zeroBuf
  obtain ⟨_, tCopy⟩ := ht.copyTail
  obtain ⟨_, tCmp⟩ := ht.cmpLen
  obtain ⟨_, tArg⟩ := ht.blkArg
  obtain ⟨_, tLen⟩ := ht.lenArg
  obtain ⟨_, tFin⟩ := ht.finish
  obtain ⟨_, tNil⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, tRsi⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r13]) (.block [.mov .rsi (.reg .r13)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  -- `setup`
  have r1 : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block (setup P))
      fun s₁ s₂ => J1 P s₀ s₁ ∧ J1 P s₀' s₂ :=
    piece (X := fun σ t => t = σ) tSetup
      (fun s₁ s₂ e e' r hr => by
        subst e e'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        exacts [hq.rdi, hq.rsi, hq.rdx, hq.rcx, hq.rsp])
      (fun t e => by subst e; exact setup_ok hF hd hp) (fun t e => by subst e; exact setup_ok hF hd hp')
  -- `init`
  have r2 : RelCT isa (fun s₁ s₂ => J1 P s₀ s₁ ∧ J1 P s₀' s₂) init fun s₁ s₂ => J2 P s₀ s₁ ∧ J2 P s₀' s₂ :=
    piece tInit
      (fun s₁ s₂ h h' r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.2, h'.2.2, hsb])
      (fun t h => (init_ok hF hd hi hiw hin hp h.1 h.2.1 h.2.2).mono fun _ h => ⟨h.1, h.2.1⟩)
      (fun t h => (init_ok hF hd hi hiw hin hp' h.1 h.2.1 h.2.2).mono fun _ h => ⟨h.1, h.2.1⟩)
  -- `whole`
  have rHead : RelCT isa (fun s₁ s₂ => J2 P s₀ s₁ ∧ J2 P s₀' s₂) (.block (wholeHead P))
      fun s₁ s₂ => J3 P s₀ s₁ ∧ J3 P s₀' s₂ :=
    piece tHead (fun s₁ s₂ h h' => ag h.1 h'.1)
      (fun t h => (wholeHead_ok hd h.1).mono fun _ ⟨m, h14, hz, _, g⟩ => ⟨⟨m, (g _ (by decide)).trans h.2⟩, h14, hz⟩)
      (fun t h => (wholeHead_ok hd h.1).mono fun _ ⟨m, h14, hz, _, g⟩ => ⟨⟨m, (g _ (by decide)).trans h.2⟩, h14, hz⟩)
  have rSkip : RelCT isa (fun s₁ s₂ => J3z P s₀ s₁ ∧ J3z P s₀' s₂) (.block []) fun s₁ s₂ => J6 P s₀ s₁ ∧ J6 P s₀' s₂ :=
    piece tNil (fun _ _ _ _ _ hr => absurd hr List.not_mem_nil)
      (fun t h => WP.block_nil ⟨h.1.1, by rw [h.1.2, whl, h.2]; simp⟩)
      (fun t h => WP.block_nil ⟨h.1.1, by rw [h.1.2, whl, h.2]; simp⟩)
  have rRsi : RelCT isa (fun s₁ s₂ => J3n P s₀ s₁ ∧ J3n P s₀' s₂) (.block [.mov .rsi (.reg .r13)])
      fun s₁ s₂ => J4 P s₀ s₁ ∧ J4 P s₀' s₂ :=
    piece tRsi
      (fun s₁ s₂ h h' r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h'.1.2, hdp])
      (fun t h => (wholeArg_ok hd h.1.1).mono fun _ ⟨m, hsi, _, g⟩ =>
        ⟨⟨⟨m, (g _ (by decide)).trans h.1.2⟩, (g _ (by decide)).trans h.2.1, h.2.2⟩, hsi.trans h.1.2⟩)
      (fun t h => (wholeArg_ok hd h.1.1).mono fun _ ⟨m, hsi, _, g⟩ =>
        ⟨⟨⟨m, (g _ (by decide)).trans h.1.2⟩, (g _ (by decide)).trans h.2.1, h.2.2⟩, hsi.trans h.1.2⟩)
  have hk : ∀ σ : State, (BitVec.ofNat 64 (len σ / P.B)).toNat = len σ / P.B := fun σ => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := len_lt σ; have := Nat.div_le_self (len σ) P.B; omega)]
  have callN : ∀ σ : State, Pre P D σ → ∀ t : State, J4 P σ t →
      WP isa (compressN name code) t (J5 P σ) := fun σ hpσ t h => by
    have := hF.lt; have := st_le P; have := sc_le P; have := hd.N; have := hd.B
    have hle : P.B * (len σ / P.B) ≤ len σ := Nat.mul_div_le _ _
    exact compressWith_ok H setsN_r14 hf (k := len σ / P.B) (by rw [h.1.2.1]; exact hk _)
      (callOk_data hF hpσ h.1.1.1 h.2 hle) (by have := len_lt σ; omega) (by omega)
      fun t' hrd hwr hcs hfr _ _ _ => ⟨⟨call_mid hF hd hpσ h.1.1.1 hrd hwr hcs hfr,
        (hcs _ (by decide)).trans h.1.1.2⟩, (hcs _ (by decide)).trans h.1.2.1⟩
  have rCallN : RelCT isa (fun s₁ s₂ => J4 P s₀ s₁ ∧ J4 P s₀' s₂) (compressN name code)
      fun s₁ s₂ => J5 P s₀ s₁ ∧ J5 P s₀' s₂ :=
    ((compressWith_rel H setsN_r14 ⟨_, by taint_decide⟩ hf (N := fun s => s.gpr .r14)
      fun s₁ s₂ ⟨h, h'⟩ => ⟨⟨_, _, _, _, by rw [h.1.2.1]; exact hk _, callOk_data hF hp h.1.1.1 h.2 (Nat.mul_div_le _ _)⟩,
        ⟨_, _, _, _, by rw [h'.1.2.1]; exact hk _, callOk_data hF hp' h'.1.1.1 h'.2 (Nat.mul_div_le _ _)⟩,
        ag h.1.1.1 h'.1.1.1 _ (by simp), ag h.1.1.1 h'.1.1.1 _ (by simp), by rw [h.2, h'.2, hdp],
        ag h.1.1.1 h'.1.1.1 _ (by simp), by rw [h.1.2.1, h'.1.2.1, hl]⟩).wp
      fun s₁ s₂ h => ⟨callN _ hp _ h.1, callN _ hp' _ h.2⟩).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩
  have rEnd : RelCT isa (fun s₁ s₂ => J5 P s₀ s₁ ∧ J5 P s₀' s₂) (.block (wholeEnd P))
      fun s₁ s₂ => J6 P s₀ s₁ ∧ J6 P s₀' s₂ := by
    refine piece tEnd (fun s₁ s₂ h h' r hr => ?_) (fun t h => ?_) (fun t h => ?_)
    · rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.1.2, h'.1.2, hdp]
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2, h'.2, hl]
      · exact ag h.1.1 h'.1.1 r hr
    · have := len_lt s₀; have := Nat.mul_div_le (len s₀) P.B
      exact (wholeEnd_ok hd h.1.1 (by omega) h.2).mono fun _ ⟨m, h13, _⟩ => ⟨m, by rw [h13, h.1.2]⟩
    · have := len_lt s₀'; have := Nat.mul_div_le (len s₀') P.B
      exact (wholeEnd_ok hd h.1.1 (by omega) h.2).mono fun _ ⟨m, h13, _⟩ => ⟨m, by rw [h13, h.1.2]⟩
  have zf_true : ∀ {σ t : State}, J3 P σ t → eval .e t = some true → len σ / P.B = 0 := fun h e => by
    simp only [eval, h.2.2, Option.some.injEq, decide_eq_true_eq] at e; exact e
  have zf_false : ∀ {σ t : State}, J3 P σ t → eval .e t = some false → len σ / P.B ≠ 0 := fun h e => by
    simp only [eval, h.2.2, Option.some.injEq, decide_eq_false_iff_not] at e; exact e
  have rWhole : RelCT isa (fun s₁ s₂ => J2 P s₀ s₁ ∧ J2 P s₀' s₂) (whole P name code)
      fun s₁ s₂ => J6 P s₀ s₁ ∧ J6 P s₀' s₂ := by
    refine rHead.seq (RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.1.2.2, h.2.2.2, hl]) ?_ ?_)
    · refine rSkip.mono (fun s₁ s₂ ⟨⟨h, h'⟩, e⟩ => ?_) fun _ _ h => h
      have z := zf_true h e
      exact ⟨⟨h.1, z⟩, ⟨h'.1, by rw [← hl]; exact z⟩⟩
    · refine (rRsi.seq (rCallN.seq rEnd)).mono (fun s₁ s₂ ⟨⟨h, h'⟩, e⟩ => ?_) fun _ _ h => h
      have z := zf_false h e
      exact ⟨⟨h.1, h.2.1, z⟩, ⟨h'.1, h'.2.1, by rw [← hl]; exact z⟩⟩
  -- `tail`
  have rZero : RelCT isa (fun s₁ s₂ => J6 P s₀ s₁ ∧ J6 P s₀' s₂) (.block (zeroBuf P))
      fun s₁ s₂ => J7 P s₀ s₁ ∧ J7 P s₀' s₂ :=
    piece tZero (fun s₁ s₂ h h' => ag h.1 h'.1)
      (fun t h => (zeroBuf_ok hF hd hp h.1).mono fun _ ⟨m, g, _, b⟩ => ⟨⟨m, by rw [g]; exact h.2⟩, b⟩)
      (fun t h => (zeroBuf_ok hF hd hp' h.1).mono fun _ ⟨m, g, _, b⟩ => ⟨⟨m, by rw [g]; exact h.2⟩, b⟩)
  have rCopy : RelCT isa (fun s₁ s₂ => J7 P s₀ s₁ ∧ J7 P s₀' s₂) (copyTail P)
      fun s₁ s₂ => J8 P s₀ s₁ ∧ J8 P s₀' s₂ := by
    refine piece tCopy (fun s₁ s₂ h h' r hr => ?_)
      (fun t h => (copyTail_ok hF hd hp h.1.1 h.1.2 h.2).mono fun _ ⟨m, h10, _⟩ => ⟨m, h10⟩)
      (fun t h => (copyTail_ok hF hd hp' h.1.1 h.1.2 h.2).mono fun _ ⟨m, h10, _⟩ => ⟨m, h10⟩)
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [h.1.2, h'.1.2]
      show dp s₀ + BitVec.ofNat 64 (P.B * (len s₀ / P.B)) = dp s₀' + BitVec.ofNat 64 (P.B * (len s₀' / P.B))
      rw [hdp, hl]
    · exact ag h.1.1 h'.1.1 r hr
  have rCmp : RelCT isa (fun s₁ s₂ => J8 P s₀ s₁ ∧ J8 P s₀' s₂) (.block (cmpLen P))
      fun s₁ s₂ => J9 P s₀ s₁ ∧ J9 P s₀' s₂ := by
    refine piece tCmp (fun s₁ s₂ h h' r hr => ?_)
      (fun t h => (cmpLen_ok hF hd h.1 h.2).mono fun _ ⟨m, hc, _⟩ => ⟨m, hc⟩)
      (fun t h => (cmpLen_ok hF hd h.1 h.2).mono fun _ ⟨m, hc, _⟩ => ⟨m, hc⟩)
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [h.2, h'.2]; show BitVec.ofNat 64 (len s₀ % P.B) = BitVec.ofNat 64 (len s₀' % P.B); rw [hl]
    · exact ag h.1 h'.1 r hr
  have rArg : RelCT isa (fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂) (.block (blkArg P))
      fun s₁ s₂ => JA P s₀ s₁ ∧ JA P s₀' s₂ :=
    piece tArg (fun s₁ s₂ h h' => ag h h')
      (fun t h => (blkArg_ok hF hd h).mono fun _ ⟨m, hsi, _⟩ => ⟨m, hsi⟩)
      (fun t h => (blkArg_ok hF hd h).mono fun _ ⟨m, hsi, _⟩ => ⟨m, hsi⟩)
  have rAt : RelCT isa (fun s₁ s₂ => JA P s₀ s₁ ∧ JA P s₀' s₂) (compressAt name code)
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ :=
    ((compressAt_rel H hf fun s₁ s₂ ⟨h, h'⟩ => ⟨⟨_, _, _, callOk_buf hF hp h.1 h.2⟩,
        ⟨_, _, _, callOk_buf hF hp' h'.1 h'.2⟩, ag h.1 h'.1 _ (by simp), ag h.1 h'.1 _ (by simp),
        by rw [h.2, h'.2, hsb], ag h.1 h'.1 _ (by simp)⟩).wp
      fun s₁ s₂ h => ⟨compressBuf_ok hF hd hf hp h.1.1 h.1.2 fun _ m _ _ => m,
        compressBuf_ok hF hd hf hp' h.2.1 h.2.2 fun _ m _ _ => m⟩).mono (fun _ _ h => h)
      fun _ _ h => ⟨h.2.1, h.2.2⟩
  have rZero' : RelCT isa (fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂) (.block (zeroBuf P))
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ :=
    piece tZero (fun s₁ s₂ h h' => ag h h')
      (fun t h => (zeroBuf_ok hF hd hp h).mono fun _ h => h.1)
      (fun t h => (zeroBuf_ok hF hd hp' h).mono fun _ h => h.1)
  have rNil : RelCT isa (fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂) (.block [])
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ :=
    piece tNil (fun _ _ _ _ _ hr => absurd hr List.not_mem_nil) (fun t h => WP.block_nil h)
      (fun t h => WP.block_nil h)
  have rLen : RelCT isa (fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂) (.block (P.len ++ blkArg P))
      fun s₁ s₂ => JA P s₀ s₁ ∧ JA P s₀' s₂ :=
    piece tLen (fun s₁ s₂ h h' => ag h h')
      (fun t h => (lenArg_ok hF hd hs hp h).mono fun _ ⟨m, hsi, _⟩ => ⟨m, hsi⟩)
      (fun t h => (lenArg_ok hF hd hs hp' h).mono fun _ ⟨m, hsi, _⟩ => ⟨m, hsi⟩)
  have rTail : RelCT isa (fun s₁ s₂ => J6 P s₀ s₁ ∧ J6 P s₀' s₂) (tail P name code)
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ := by
    refine rZero.seq (rCopy.seq (rCmp.seq ((RelCT.ite (fun s₁ s₂ h => by
      simp only [eval, h.1.2, h.2.2]; show _ = Option.map _ (some (decide (len s₀' % P.B < _))); rw [← hl])
        ((rArg.seq (rAt.seq rZero')).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
        (rNil.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)).seq (rLen.seq rAt))))
  have rFin : RelCT isa (fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂) (.block (finish P)) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => Taint.agree_ofRegs (ag h.1 h.2)) tFin
  exact r1.seq (r2.seq (rWhole.seq (rTail.seq rFin)))

/-! ## The body is verified -/

theorem constantTime {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    (ht : Taints P) {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false) (hin : init.noCalls = true)
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) init hc).isSome = true)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) :
    ConstantTime isa (oneK H iv D).pre (oneK H iv D).pub (body P init name code) := by
  intro s₀ s₀' t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (body_rel hF hd hs ht hi hiw hin hict hf h₁ h₂
    ⟨hpub.1, hpub.2.1, hpub.2.2.1, hpub.2.2.2.1, hpub.2.2.2.2⟩ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The body is verified against `oneK`, if it never loads MXCSR and some
state satisfies the precondition. -/
theorem verified {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    (ht : Taints P) {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false) (hin : init.noCalls = true)
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) init hc).isSome = true)
    {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (body P init name code).allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, Pre P D s) :
    Verified X86_64.target (body P init name code) (oneK H iv D) := by
  refine ⟨fun s hs' => ?_, constantTime hF hd hs ht hi hiw hin hict hf, hsat⟩
  obtain ⟨t, s', he, h⟩ := correct hF hd hs hi hiw hin hf hs'
  exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩

end VG.Proof.MdStream.X86_64.OneShot
