module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env

/-! ### `Dsa.X86.Generation.TimingBase`, which this module and modules that import it used -/

section

/-! # Two runs of parameter generation at the same point

Both runs satisfy the same predicate with the same parameters (`Both`): the
same environment, the same values of the state words that steer branches and
hold pointers, the same loop indices. Code whose trace depends only on
registers both runs agree on is checked by the taint analysis; a branch's
condition is fixed by the parameters; what each run reaches is what its
correctness proof says. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Both {α : Type} (Φ : α → State → Prop) (s t : State) : Prop := ∃ a, Φ a s ∧ Φ a t

theorem both_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Both Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Both Φ) c (Both Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  exact ⟨ht, a, wp_result (hw a _ h₁) e₁, wp_result (hw a _ h₂) e₂⟩

theorem both_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (f : α → β) (h : ∀ a s, Φ a s → Φ' (f a) s) (hct : RelCT isa (Both Φ') c Q) :
    RelCT isa (Both Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨f a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

/-- A fact that every related pair of states gives. -/
theorem relct_of_fact {P : Prop} {Φ : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (hP : ∀ s t, Φ s t → P) (h : P → RelCT isa Φ c Q) : RelCT isa Φ c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h (hP _ _ hp) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-- For each value of the parameters. -/
theorem both_exists {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s t => Φ a s ∧ Φ a t) c Q) : RelCT isa (Both Φ) c Q :=
  RelCT.exists_ h

/-- A branch whose condition the parameters fix. -/
theorem both_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop} (b : α → Bool) (hc : ∀ a s, Φ a s → isa.eval cond s = some (b a))
    (ht : RelCT isa (Both fun a s => Φ a s ∧ b a = true) th Q)
    (he : RelCT isa (Both fun a s => Φ a s ∧ b a = false) el Q) :
    RelCT isa (Both Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun s t ⟨a, h₁, h₂⟩ => by rw [hc a s h₁, hc a t h₂]) ?_ ?_
  · refine ht.mono (fun s t ⟨⟨a, h₁, h₂⟩, e⟩ => ⟨a, ⟨h₁, ?_⟩, h₂, ?_⟩) fun _ _ h => h <;>
    · rw [hc a s h₁] at e; exact Option.some.inj e
  · refine he.mono (fun s t ⟨⟨a, h₁, h₂⟩, e⟩ => ⟨a, ⟨h₁, ?_⟩, h₂, ?_⟩) fun _ _ h => h <;>
    · rw [hc a s h₁] at e; exact Option.some.inj e

/-- Code whose trace the taint analysis checks from registers the
parameters fix. -/
theorem both_agree {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop} (rs : List Reg)
    (val : α → Reg → BitVec 32) (hpin : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = val a r)
    (h : RelCT isa (VG.X86.Taint.Agree (τr rs)) c Q) : RelCT isa (Both Φ) c Q :=
  h.mono (fun s t ⟨a, h₁, h₂⟩ => agree_regs fun r hr => (hpin a s h₁ r hr).trans (hpin a t h₂ r hr).symm)
    fun _ _ h => h

/-- Code the taint analysis checks from the registers `rs`. -/
theorem tcheck (rs : List Reg) (c : Prog isa)
    (h : (VG.Taint.check taint (τr rs) c (VG.Taint.hintOf taint (τr rs) c)).isSome = true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c fun _ _ => True :=
  RelCT.taint (A := taint) (τr rs) (fun _ _ h => h) h

/-- Code the taint analysis checks from the registers `rs`, which it keeps
public. -/
theorem tkeep (rs : List Reg) (c : Prog isa)
    (h : (VG.Taint.check taint (τr rs) c (VG.Taint.hintOf taint (τr rs) c)).map (taint.le (τr rs)) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c (VG.X86.Taint.Agree (τr rs)) := by
  obtain ⟨τ', H, L⟩ := Option.map_eq_some_iff.mp h
  exact checkedProgramChange H L

/-- `RelCT.callWith`, popping into any register. -/
theorem callWithPop {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa} {r : Reg}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (.frame (.push rs) (.call n c) (.pop r rs.length)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

/-- `tcheck` for code checked as `c₀`, which differs only in immediates and
offsets. -/
theorem tcheckE (rs : List Reg) (c c₀ : Prog isa) (e : Code.erase c = Code.erase c₀)
    (hh : VG.X86.Taint.hintNoBases (VG.Taint.hintOf taint (τr rs) c₀) = true)
    (h : (VG.Taint.check taint (τr rs) c₀ (VG.Taint.hintOf taint (τr rs) c₀)).map (taint.le (τr [])) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c fun _ _ => True :=
  (erased_relCT c c₀ _ e rfl hh h).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- A list of programs in sequence, each keeping `P`, then the last. -/
theorem seqs_last {P Q : State → State → Prop} {xs : List (Prog isa)} {b : Prog isa}
    (hxs : ∀ p ∈ xs, RelCT isa P p P) (hb : RelCT isa P b Q) :
    RelCT isa P (VG.Impl.Dsa.X86.Generation.seqs (xs ++ [b])) Q := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    cases xs with
    | nil => exact RelCT.seq (hxs x List.mem_cons_self) hb
    | cons y ys =>
      exact RelCT.seq (hxs x List.mem_cons_self) (ih fun p hp => hxs p (List.mem_cons_of_mem _ hp))

theorem Base.edi {E : Env} {s : State} (B : Base E s) : s.gpr .edi = E.base.setWidth 32 := by
  rw [← B.scr.edi, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

end VG.Proof.Dsa.X86.Generation

end

end

/-! # Two runs of a hash leak the same: addresses from `edi` and `esp` -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Pbkdf2.Md.X86 (CmpArgs cmp_ok cmp_rel)
open VG.Proof.Pbkdf2.Stream.X86 (stk After)

/-- `Base` fixes `esp` and `edi`. -/
def baseVal (E : Env) : Reg → BitVec 32 := fun r => if r = .esp then E.sp else E.base.setWidth 32

theorem base_pins {E : Env} {s : State} (B : Base E s) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = baseVal E r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact B.sp
  · exact B.edi

/-- After the hash's first block: the compression function's arguments. -/
def HashMid (E : Env) (g : Geo) (t : State) : Prop :=
  CmpArgs g.H.N g.H.B g.H.so t (E.base.setWidth 32 + BitVec.ofNat 32 sState)
    (E.base.setWidth 32 + BitVec.ofNat 32 sHScr) ∧ t.gpr .esp = E.sp ∧ t.gpr .edi = E.base.setWidth 32

theorem hashPrep_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) :
    WP isa (.block (scr .ebx sState ++ ivStore g.iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (g.H.N + g.qLen) (padBytes g.qLen) ((64 - g.qLen) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 g.H.N))] : List Instr) ++ scr .ebp sHScr)) s
      (HashMid E g) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have hB := G.hash.B
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have nw := v.scratchFit
  have low := v.low
  have hs := B.scr
  rw [← G.N]
  refine prep_ok G.hash hs (by simp only [sHScr]; omega_using [sz]) fun t eb ea ep gt rd wr _ => ?_
  have tsp : t.gpr .esp = s.gpr .esp := gt _ (by decide) (by decide) (by decide) (by decide)
  have tdi : t.gpr .edi = s.gpr .edi := gt _ (by decide) (by decide) (by decide) (by decide)
  have hsS : sState < E.size := by simp only [sState]; omega_using [sz]
  have hsC : sHScr < E.size := by simp only [sHScr]; omega_using [sz]
  have yNat := Scr.toNat_add hs hsS
  have yW := Scr.wide hs hsS
  have cNat := Scr.toNat_add hs hsC
  have cW := Scr.wide hs hsC
  have stkSub : Region.Sub (stk s) E.stackRegion := by
    simp only [stk, B.sp, Env.stackRegion]; exact below_sub (by decide) (by omega_using [low])
  have hstk : (stk s).Disjoint E.scratchRegion := v.scratchStack.symm.sub_left stkSub
  rw [B.edi] at eb ea ep yNat yW cNat cW
  have cargs : CmpArgs g.H.N g.H.B g.H.so t (E.base.setWidth 32 + BitVec.ofNat 32 sState)
      (E.base.setWidth 32 + BitVec.ofNat 32 sHScr) :=
    { ebx := eb
      eax := ea
      ebp := ep
      sp48 := by rw [tsp, B.sp]; omega_using [low]
      cst := by rw [yW, wr]; exact Scr.covers hs (by rw [hB]; simp only [sState]; omega_using [sz, nl])
      csc := by rw [cW, wr]; exact Scr.covers hs (by simp only [sHScr]; omega_using [sz, so, sW])
      st_sc := by
        rw [yW, cW]
        exact Offset.disjoint E.base (by simp only [sState, sHScr]; rw [hB]; omega_using [nl]) (by rw [hB]; omega_using [nl, yNat]) (by omega_using [so, sW, nw, hsC])
      b_st := by
        rw [stk, tsp, yW]
        exact hstk.sub_right (Offset.sub_base E.base (by rw [hB]; simp only [sState]; omega_using [sz, nl]))
      b_sc := by
        rw [stk, tsp, cW]
        exact hstk.sub_right (Offset.sub_base E.base (by simp only [sHScr]; omega_using [sz, so, sW]))
      nst := by rw [yNat, hB]; simp only [sState]; omega_using [sz, nl, nw]
      nsc := by rw [cNat]; simp only [sHScr]; omega_using [sz, so, sW, nw] }
  exact ⟨cargs, tsp.trans B.sp, tdi.trans B.edi⟩

theorem hash_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (dst : Nat) :
    RelCT isa (Both fun (_ : Unit) s => Base E s) (hash g.H g.iv g.qLen dst) fun _ _ => True := by
  have hB := G.hash.B
  unfold Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := fun _ t => HashMid E g t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ B => base_pins B) G.prepCt)
    fun _ s B => hashPrep_ok G v B) ?_
  refine RelCT.seq (both_post (Ψ := fun _ t => t.gpr .esp = E.sp ∧ t.gpr .edi = E.base.setWidth 32)
    ((cmp_rel G.hash.ok.comp (by rw [hB]; decide) (sp := E.sp)
      (fun s s' ⟨_, h, h'⟩ => ⟨h.1, h'.1, h.2.1, h'.2.1⟩)).mono (fun _ _ h => h) fun _ _ h => h)
    fun _ t h => ?_) ?_
  · refine cmp_ok G.hash.ok.comp (by rw [hB]; decide) h.1 fun u au _ => ?_
    exact ⟨(au.cs .esp (by decide)).trans h.2.1, (au.cs .edi (by decide)).trans h.2.2⟩
  · refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ s h r hr => ?_) (G.outCt dst)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

end VG.Proof.Dsa.X86.Generation
