module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Dsa.Contract
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `Dsa.X86.Generation.HashCT`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86.Generation.AttemptCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.Generation.TimingFlags`, which this module and modules that import it used -/

section

/-! # Two runs at a branch on a state word -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

/-- After a comparison of a state word, from a state where `Φ a` held:
only `eax` and the flags changed. -/
def CmpAfter {α : Type} (Φ : α → State → Prop) (a : α) (t : State) : Prop :=
  ∃ s, Φ a s ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.syms = s.syms

theorem CmpAfter.base {α : Type} {Φ : α → State → Prop} {E : Env} (hb : ∀ a s, Φ a s → Base E s) {a : α}
    {t : State} (h : CmpAfter Φ a t) : Base E t := by
  obtain ⟨s, hs, g, m, rd, wr, sy⟩ := h
  exact (hb a s hs).regs m (g _ (by decide)) (g _ (by decide)) rd wr sy

theorem cmpF_erase (o v : Nat) : Code.erase (.block (cmpF o v)) = Code.erase (.block (cmpF 0 0)) := rfl

theorem stImm_erase (o v : Nat) : Code.erase (.block (stImm o v)) = Code.erase (.block (stImm 0 0)) := rfl

/-- A store of a constant into a state word. -/
theorem stImm_ct {α : Type} {Φ : α → State → Prop} {E : Env} (hb : ∀ a s, Φ a s → Base E s) (o v : Nat) :
    RelCT isa (Both Φ) (.block (stImm o v)) fun _ _ => True :=
  both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h))
    (tcheckE _ _ (.block (stImm 0 0)) (stImm_erase _ _) (by decide +kernel) (by decide +kernel))

/-- A comparison of the state word at `o`, whose value `w a` the parameters
fix, then a branch on it. -/
theorem cmpF_ct {α : Type} {Φ : α → State → Prop} {E : Env} {o v : Nat} (ho : o + 4 ≤ E.size)
    (hv : v < 2 ^ 32) (w : α → Nat) (hb : ∀ a s, Φ a s → Base E s)
    (hw : ∀ a s, Φ a s → s.mem.readW (off E.base o) 32 = BitVec.ofNat 32 (w a)) (hwl : ∀ a, w a < 2 ^ 32)
    {th el : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a = v) = true) th Q)
    (he : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a = v) = false) el Q) :
    RelCT isa (Both Φ) (.seq (.block (cmpF o v)) (.ite .e th el)) Q := by
  refine RelCT.seq (both_post (Ψ := fun a t => CmpAfter Φ a t ∧ isa.eval .e t = some (decide (w a = v)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h))
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    fun a s h => cmpF_end (hb a s h).scr ho (hw a s h) (hwl a) hv fun t g m rd wr sy z =>
      ⟨⟨s, h, g, m, rd, wr, sy⟩, z⟩) ?_
  exact both_ite (fun a => decide (w a = v)) (fun a t h => h.2)
    (ht.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)
    (he.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)

/-- A comparison of the state word at `o`, whose value `w a` the parameters
fix, then a branch on its borrow. -/
theorem cmpFb_ct {α : Type} {Φ : α → State → Prop} {E : Env} {o v : Nat} (ho : o + 4 ≤ E.size)
    (hv : v < 2 ^ 32) (w : α → Nat) (hb : ∀ a s, Φ a s → Base E s)
    (hw : ∀ a s, Φ a s → s.mem.readW (off E.base o) 32 = BitVec.ofNat 32 (w a)) (hwl : ∀ a, w a < 2 ^ 32)
    {th el : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a < v) = true) th Q)
    (he : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a < v) = false) el Q) :
    RelCT isa (Both Φ) (.seq (.block (cmpF o v)) (.ite .b th el)) Q := by
  refine RelCT.seq (both_post (Ψ := fun a t => CmpAfter Φ a t ∧ isa.eval .b t = some (decide (w a < v)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h))
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    fun a s h => cmpFb_end (hb a s h).scr ho (hw a s h) (hwl a) hv fun t g m rd wr sy z =>
      ⟨⟨s, h, g, m, rd, wr, sy⟩, z⟩) ?_
  exact both_ite (fun a => decide (w a < v)) (fun a t h => h.2)
    (ht.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)
    (he.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.QCT`, which only this module used -/

section

/-! ### `Dsa.X86.Generation.TestCT`, which this module and modules that import it used -/

section

/-! # Two runs of a probable-prime test of the same candidate leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a test: the witness cursor `p.1` and the candidate `p.2`. -/
def TPre (E : Env) (bits : Nat) (p : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 p.1 ∧ p.1 ≤ E.witLen ∧
    Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) = p.2 ∧
    p.2 % 2 = 1 ∧ Spec.Dsa.bitLength p.2 = bits

/-- The test's writable regions, with `esp` at `E.sp`. -/
def testWrSp (E : Env) : List Region :=
  [⟨off E.base sPP, 8 * ppWords⟩, ⟨off E.base fUsedOut, 8⟩, ⟨(E.sp - 20#32).setWidth 64, 20⟩]

theorem testWr_sp {E : Env} {t : State} (h : t.gpr .esp = E.sp) : testWr E t = testWrSp E := by
  simp only [testWr, testWrSp, h]

theorem test_ct {bits : Nat} {name : String} {callee : Prog isa}
    (verified : Verified target callee (ppContract bits)) (noSp : NoSp callee) (stack : stackUse callee ≤ 152)
    {E : Env} (v : E.Valid) (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) :
    RelCT isa (Both (TPre E bits)) (test name callee) fun _ _ => True := by
  have sz := v.size_ge
  have psz : sPP ≤ E.size := by simp only [sPP]; omega_using [sz]
  unfold test
  simp only [seqs]
  -- The cursor and the octets left.
  refine RelCT.seq (both_post (Ψ := fun p t => ∃ s, TPre E bits p s ∧
      TestHead E.base (E.wit.setWidth 32) E.witLen p.1 s t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1) (tcheck _ _ (by decide +kernel)))
    fun p s h => WP.mono (testHead_ok h.1.scr psz h.1.witW h.1.witLenW h.2.1 h.2.2.1 v.witLen32)
      fun t H => ⟨s, h, H⟩) ?_
  have pins₁ : ∀ (p : Nat × Nat) t, (∃ s, TPre E bits p s ∧ TestHead E.base (E.wit.setWidth 32) E.witLen p.1 s t) →
      ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r := by
    rintro p t ⟨s, h, H⟩ r hr
    rw [H.other r (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl <;> decide)]
    exact base_pins h.1 r hr
  refine RelCT.assoc (RelCT.seq (both_post (Ψ := fun p t => ∃ s, TPre E bits p s ∧
      TestArgs E.base (E.wit.setWidth 32) E.witLen p.1 s t) ?_
    fun p t ⟨s, h, H⟩ => WP.mono (testMid_ok h.1.scr psz h.1.witW H) fun u A => ⟨s, h, A⟩) ?_)
  · -- The pointer to the witnesses left.
    refine RelCT.seq (both_ite (fun p => decide (E.witLen - p.1 = 0)) (fun p t ⟨s, _, H⟩ => H.zf)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun p t h => pins₁ p t h.1) (tkeep _ _ (by decide +kernel)))
      (RelCT.nil fun x y ⟨p, h₁, h₂⟩ => agree_regs fun r hr =>
        (pins₁ p x h₁.1 r hr).trans (pins₁ p y h₂.1 r hr).symm)) (tcheck _ _ (by decide +kernel))
  refine RelCT.seq (both_post (Φ := fun p t => ∃ s, TPre E bits p s ∧
      TestArgs E.base (E.wit.setWidth 32) E.witLen p.1 s t)
    (Ψ := fun p u => ∃ s, TPre E bits p s ∧ TestRet E bits p.1 p.2 s u) ?_ fun p t hp => by
      obtain ⟨s, h, A⟩ := hp
      refine WP.mono (testCall_ok verified noSp stack v h.1 A h.2.2.1 lay
        (by rw [h.2.2.2.1]; exact h.2.2.2.2.1) (by rw [h.2.2.2.1]; exact h.2.2.2.2.2)) fun u R => ⟨s, h, ?_⟩
      rw [← h.2.2.2.1]; exact R) ?_
  · -- The call.
    refine both_exists fun p => ?_
    refine callWithPop (rs := testRegs) verified.1 verified.2.1 (testRd E p.1) (testWrSp E)
      fun t₁ t₂ hp => ?_
    obtain ⟨⟨s₁, h₁, A₁⟩, ⟨s₂, h₂, A₂⟩⟩ := hp
    have sp₁ : t₁.gpr .esp = E.sp := by
      rw [A₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.1.sp]
    have sp₂ : t₂.gpr .esp = E.sp := by
      rw [A₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h₂.1.sp]
    have c₁ := testCallPre v h₁.1 A₁ h₁.2.2.1 lay (by rw [h₁.2.2.2.1]; exact h₁.2.2.2.2.1)
      (by rw [h₁.2.2.2.1]; exact h₁.2.2.2.2.2)
    have c₂ := testCallPre v h₂.1 A₂ h₂.2.2.1 lay (by rw [h₂.2.2.2.1]; exact h₂.2.2.2.2.1)
      (by rw [h₂.2.2.2.1]; exact h₂.2.2.2.2.2)
    rw [testWr_sp sp₁] at c₁
    rw [testWr_sp sp₂] at c₂
    have F₁ := testEntry_facts v h₁.1 A₁ h₁.2.2.1 lay
    have F₂ := testEntry_facts v h₂.1 A₂ h₂.2.2.1 lay
    simp only [testEntry, testWr_sp sp₁, testWr_sp sp₂] at F₁ F₂
    refine ⟨c₁, c₂, sp₁.trans sp₂.symm, ?_⟩
    generalize (pushed testRegs t₁).callEntry.withRegions (testRd E p.1) (testWrSp E) = w₁ at F₁ ⊢
    generalize (pushed testRegs t₂).callEntry.withRegions (testRd E p.1) (testWrSp E) = w₂ at F₂ ⊢
    sig_pub [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    obtain ⟨esp₁, sy₁, a0₁, a1₁, a2₁, a3₁, -, a0'₁, a2'₁, a3'₁, a4'₁, cand₁, ent₁⟩ := F₁
    obtain ⟨esp₂, sy₂, a0₂, a1₂, a2₂, a3₂, -, a0'₂, a2'₂, a3'₂, a4'₂, cand₂, ent₂⟩ := F₂
    refine ⟨esp₁.trans esp₂.symm, ?_, ?_, by rw [a0'₁, a0'₂, h₁.1.edi, h₂.1.edi], a1₁.trans a1₂.symm,
      a2'₁.trans a2'₂.symm, a3'₁.trans a3'₂.symm, by rw [a4'₁, a4'₂, h₁.1.edi, h₂.1.edi]⟩
    · rw [sy₁, sy₂]
      have e := h₁.1.syms.trans h₂.1.syms.symm
      exact BitVec.eq_of_toNat_eq (by
        have := congrArg BitVec.toNat e
        rwa [toNat_wide, toNat_wide] at this)
    · rw [a0₁, a2₁, a3₁, cand₁, ent₁, a0₂, a2₂, a3₂, cand₂, ent₂, h₁.2.2.2.1, h₂.2.2.2.1]
  -- The status, and the octets read.
  have pins₃ : ∀ (p : Nat × Nat) u, (∃ s, TPre E bits p s ∧ TestRet E bits p.1 p.2 s u) →
      ∀ r ∈ [Reg.esp, .edi], u.gpr r = baseVal E r := by
    rintro p u ⟨s, h, R⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact R.esp
    · exact R.edi.trans h.1.edi
  refine RelCT.seq (both_post (Ψ := fun p x => x.zf = some (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
      (Spec.Dsa.probablePrime p.2 (E.witT.drop p.1))) - 0 == 0) ∧ ∀ r ∈ [Reg.esp, .edi], x.gpr r = baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) pins₃ (tcheck _ _ (by decide +kernel))) fun p u hp => ?_) ?_
  · obtain ⟨s, h, R⟩ := hp
    have hsU : Scr u E.base E.size := Scr.of_eq h.1.scr R.edi (R.esp.trans h.1.sp.symm) R.wr
    refine st_ok hsU (by simp only [fRes, hdr]; omega_using [sz]) fun x₁ M₁ => wp_cmpi fun x₂ F₂ _ z₂ => WP.block_nil ⟨?_, ?_⟩
    · rw [z₂, M₁.gpr, R.eax]
    · intro r hr; rw [F₂.gpr, M₁.gpr]; exact pins₃ p u ⟨s, h, R⟩ r hr
  · refine both_ite (fun p => BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
      (Spec.Dsa.probablePrime p.2 (E.witT.drop p.1))) - 0 == 0) (fun p x h => h.1) (RelCT.nil fun _ _ _ => trivial)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun p x h => h.1.2) (tcheck _ _ (by decide +kernel)))

end VG.Proof.Dsa.X86.Generation

end

end

/-! # Two runs of q from the same seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a copy from the tape at the state word `w`: its value. -/
def CopyIn (E : Env) (w : Nat) (x : BitVec 32) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base w) 32 = x

/-- A copy from a pointer in a state word: the pointer is the same in both
runs. -/
theorem copyIn_ct {E : Env} (v : E.Valid) {w : Nat} (hw : w + 4 ≤ 73728) (dst n : Nat) :
    RelCT isa (Both (CopyIn E w)) (copyTo [.mov .esi (.mem (sc w))] dst n) fun _ _ => True := by
  have sz := v.size_ge
  unfold copyTo
  refine RelCT.seq (both_post (Ψ := fun x t => ∀ r ∈ [Reg.esp, .edi, .esi, .ebx, .ecx],
      t.gpr r = if r = .esi then x else if r = .ebx then E.base.setWidth 32 + BitVec.ofNat 32 dst
        else if r = .ecx then BitVec.ofNat 32 n else baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
      (tcheckE _ _ (.block ([.mov .esi (.mem (sc 0))] ++ scr .ebx 0 ++ [.mov .ecx (.imm (BitVec.ofNat 32 0))]))
        (by kernel_rfl) (by decide +kernel) (by decide +kernel))) fun x s h => ?_)
    (both_agree [.esp, .edi, .esi, .ebx, .ecx] _ (fun _ _ h => h)
      (tcheck _ _ (by decide +kernel)))
  simp only [List.cons_append, List.nil_append, scr]
  refine ld_ok h.1.scr (d := w) (by omega_using [hw, sz]) fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_addi fun t₃ u₃ =>
    wp_movi fun t₄ u₄ => WP.block_nil ?_
  have pins := base_pins h.1
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact pins _ (by simp)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact pins _ (by simp)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.2]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.1.edi]; rfl
  · rw [u₄.gpr]; rfl

theorem copyS_erase (a b n : Nat) : Code.erase (copyS a b n) = Code.erase (copyS 0 0 1) := rfl

/-- Before q of seed `a.1`, with the witness cursor at `a.2`. -/
def QIn (E : Env) (a : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 a.2 ∧ a.2 ≤ E.witLen

theorem qAt_pins {E : Env} {g : Geo} {s t : State} (Q : QAt E g s t) : ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r :=
  base_pins Q.base

theorem qPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (QIn E)) g.qPart fun _ _ => True := by
  have sz := v.size_ge
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_using [h]
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_using [h]
  unfold Geo.qPart
  simp only [seqs]
  -- The seed in the block.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E a.1)
    (both_map (fun a => (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32) (fun a s h => ⟨h.1, h.2.2.1⟩)
      (copyIn_ct v (w := fSeed) (by decide) _ _))
    fun a s h => WP.mono (q1_ok G v hq h.1 h.2.1 h.2.2.1) fun t h' => ⟨s, h, h'⟩) ?_
  -- Its hash.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E a.1))
    (both_map (fun _ => ()) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact Q.base) (hash_ct G v _))
    fun a t h => by
      obtain ⟨s, hs, Q, S⟩ := h
      exact WP.mono (q2_ok G v Q S) fun u h' => ⟨s, hs, h'⟩) ?_
  -- q's top and low bits.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E a.1)) 7)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact qAt_pins Q)
      (tcheckE _ _ (.block (orByte 0 0x80 ++ orByte 0 1)) (by kernel_rfl) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨s, hs, Q, H⟩ := h
      exact WP.mono (q3_ok G v Q H) fun u h' => ⟨s, hs, h'⟩) ?_
  -- Into the test's working space.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)) t.mem
        (off E.base sPP) = Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact qAt_pins Q)
      (tcheckE _ _ (copyS 0 0 1) (copyS_erase _ _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨s, hs, Q, H⟩ := h
      exact WP.mono (q4_ok G v Q H) fun u h' => ⟨s, hs, h'.1, h'.2.1⟩) ?_
  -- The test.
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  refine both_map (fun a => (a.2, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1))) (fun a t h => ?_)
    (test_ct G.qv G.qNoSp G.qStack v lay)
  obtain ⟨s, hs, Q, cval⟩ := h
  have Ap := qPre_apart G v
  have qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega_using [q20]) (chunk E a.1)
  refine ⟨Q.base, ?_, hs.2.2.2.2, cval, qsh.1, VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega_using [q20]) _⟩
  rw [Env.Chg.word v Q.chg (by simp only [fUsed, hdr]; omega_using [sz]) (fun o ho => ⟨(Ap o ho).1, by
    simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> simp only [sState, sHScr, sPk, sPP, fUsed, hdr] <;> omega_using []⟩),
    hs.2.2.2.1]

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.PPartCT`, which only this module used -/

section

/-! ### `Dsa.X86.Generation.PCT`, which only this module used -/

section

/-! # Two runs of p's search from the same seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a hash of X: seed `a.1` and the counter's offset `a.2`. -/
def PH (E : Env) (g : Geo) (a : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 a.2 ∧ a.2 + g.count + 256 ≤ 2 ^ 32

theorem addBE_erase (n : Nat) : Code.erase (addBE n) = Code.erase (addBE 1) := rfl

theorem pHash_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {j : Nat}
    (hj : j ≤ g.count) : RelCT isa (Both (PH E g)) (g.pHash j) (Both (PH E g)) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have bd := G.bounds
  have hN := G.N
  obtain Ap := hRanges_apart G v hj
  obtain hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_using [hj])
  refine both_post ?_ fun a s h => WP.mono (pHash_ok G v hq h.1 h.2.1 h.2.2.1 h.2.2.2.1
    (by have := h.2.2.2.2; omega_using [hj, this]) hj)
    fun t ⟨B', _, C, _⟩ => ⟨B', h.2.1, ?_, ?_, h.2.2.2.2⟩
  rotate_left
  · rw [Env.Chg.word v C (by simp only [fSeed, hdr]; omega_using [sz]) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fSeed, hdr] <;> omega_arith⟩),
      h.2.2.1]
  · rw [Env.Chg.word v C (by simp only [fOffset, hdr]; omega_using [sz]) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega_arith⟩),
      h.2.2.2.1]
  unfold Geo.pHash
  simp only [seqs]
  -- The seed.
  refine RelCT.seq (both_post (Ψ := fun a t => Base E t ∧ t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 a.2 ∧
      a.2 + g.count + 256 ≤ 2 ^ 32)
    (both_map (fun a => (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32) (fun a s h => ⟨h.1, h.2.2.1⟩)
      (copyIn_ct v (w := fSeed) (by decide) _ _)) fun a s h => ?_) ?_
  · refine VG.X86.WP.mono_syms (seedIn_ok G v hq h.1 h.2.1 h.2.2.1) fun t₁ ⟨_, F₁, K₁⟩ sy₁ => ?_
    obtain C₁ : E.Chg (hRanges g j) s.mem t₁.mem := Env.Chg.of_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega_using []) (by simp only [sState]; omega_using [nl, bd])
    refine ⟨h.1.keep v C₁ Ap (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁, ?_, h.2.2.2.2⟩
    rw [Env.Chg.word v C₁ (by simp only [fOffset, hdr]; omega_using [sz]) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega_arith⟩),
      h.2.2.2.1]
  -- `seed + offset + j`'s addend and the end of the seed.
  refine RelCT.seq (both_post (Ψ := fun a t => Base E t ∧
      t.gpr .edx = E.base.setWidth 32 + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (a.2 + j) ∧ a.2 + j + 256 ≤ 2 ^ 32)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
      (tcheckE _ _ (.block (scr .edx 0 ++ [.mov .ecx (.mem (sc 0)), .alu .add .ecx (.imm (BitVec.ofNat 32 0))]))
        rfl (by decide +kernel) (by decide +kernel))) fun a t h => ?_) ?_
  · refine scr_ok fun t₂ e₂ g₂ m₂ rd₂ wr₂ sy₂ =>
      ld_ok (Scr.of_eq h.1.scr (g₂ _ (by decide)) (g₂ _ (by decide)) wr₂) (d := fOffset)
        (by simp only [fOffset, hdr]; omega_using [sz]) fun t₃ u₃ => wp_addi fun t₄ u₄ => WP.block_nil ?_
    obtain edi₄ : t₄.gpr .edi = t.gpr .edi := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
    obtain esp₄ : t₄.gpr .esp = t.gpr .esp := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
    refine ⟨h.1.regs (by rw [u₄.mem, u₃.mem, m₂]) edi₄ esp₄ (by rw [u₄.rd, u₃.rd, rd₂]) (by rw [u₄.wr, u₃.wr, wr₂])
      (by rw [u₄.syms, u₃.syms, sy₂]), ?_, ?_, by omega⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂, h.1.edi]
    · rw [u₄.gpr, u₃.gpr, m₂, h.2.1, BitVec.ofNat_add]
  -- The addition.
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
    (both_agree [.esp, .edi, .edx] (fun _ r => if r = .edx then
        E.base.setWidth 32 + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) else baseVal E r)
      (fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact base_pins h.1 _ (by simp)
        · exact base_pins h.1 _ (by simp)
        · exact h.2.1)
      (tcheckE _ _ (addBE 1) (addBE_erase _) (by decide +kernel) (by decide +kernel))) fun a t h => ?_) ?_
  · have hs := h.1.scr
    refine VG.X86.WP.mono_syms (addBE_ok hs (o := sState + g.H.N) (n := g.qLen) (c := a.2 + j)
      (by omega_using [bd]) (by simp only [sState]; omega_using [sz, nl, bd]) h.2.2.2 (by rw [h.2.1, h.1.edi]) h.2.2.1) fun t₅ ⟨_, F₅, K₅, _⟩ sy₅ => ?_
    refine h.1.keep v (os := [(sState, 128)]) (Env.Chg.of_frame F₅ fun r hr => ?_) (fun o ho => ?_)
      (K₅.1 _ (by decide)) (K₅.1 _ (by decide)) K₅.2.1 K₅.2.2 sy₅
    · simp only [List.mem_singleton] at hr; subst hr
      exact Env.in_range (o := (sState, 128)) (List.mem_singleton_self _) (by omega_using []) (by simp only [sState]; omega_using [nl, bd])
    · simp only [List.mem_singleton] at ho; subst ho
      simp only [sState, fOut, fWitLen, hdr]; omega_using [sz]
  -- The hash.
  exact both_map (fun _ => ()) (fun _ _ h => h) (hash_ct G v _)

theorem pX_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PH E g)) g.pX fun _ _ => True := by
  unfold Geo.pX
  refine seqs_last (fun p hp => ?_) (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
    (tcheckE _ _ (.block (orByte 0 0x80 ++ orByte 0 1)) rfl (by decide +kernel) (by decide +kernel)))
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact pHash_ct G v hq (by omega_using [hj])

/-- p's arithmetic: its trace depends only on `esp` and `edi`, which it keeps. -/
theorem pArith_ct {g : Geo} (G : GeoOk g) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (pArith g.pLen g.qLen) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tkeep _ _ (by decide +kernel)

/-- Before a counter's candidate. -/
structure PAIn (E : Env) (g : Geo) (k offset Q used : Nat) (s : State) : Prop where
  base : Base E s
  hk : (k + 1) * E.qLen ≤ E.seedsLen
  seed : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32
  offW : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset
  hoff : offset + g.count + 256 ≤ 2 ^ 32
  q : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q
  q0 : 0 < Q
  usedW : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used
  hu : used ≤ E.witLen
  p4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4

/-- `PAIn` with its parameters together. -/
abbrev PAIn' (E : Env) (g : Geo) (a : Nat × Nat × Nat × Nat) : State → Prop := PAIn E g a.1 a.2.1 a.2.2.1 a.2.2.2

/-- The candidate into the test's working space. -/
theorem paCopy_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k offset Q used : Nat} {s s₅ : State}
    (F : PAFront E g k offset Q used s s₅) (hu : used ≤ E.witLen)
    (hge : ¬ pcand g E k offset Q < 2 ^ (8 * g.pLen - 1)) :
    WP isa (copyS (sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) sPk g.pLen) s₅
      (TPre E (8 * g.pLen) (used, pcand g E k offset Q)) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain Apa := paRanges_apart G v
  obtain e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  obtain lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  obtain candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate + g.pLen ≤ 8 * ppWords := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega_using [lay]
  refine VG.X86.WP.mono_syms (copyS_ok F.base.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) (src := sPk) (n := g.pLen)
    (by omega_using [bd]) (by simp only [sPP, ppWords] at candLe ⊢; omega_using [sz, candLe]) (by simp only [sPk]; omega_using [sz, bd])
    (by right; simp only [sPP, sPk]; omega_using [bd])) fun t₆ ⟨R₆, F₆, K₆⟩ sy₆ => ?_
  obtain pp : (sPP, 8 * ppWords) ∈ paRanges g := by simp [paRanges]
  obtain C₆ : E.Chg [(sPP, 8 * ppWords)] s₅.mem t₆.mem := Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (List.mem_singleton_self _) (by omega_using []) (by omega_using [candLe])
  obtain App : E.Apart [(sPP, 8 * ppWords)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; exact pp)
  refine ⟨F.base.keep v C₆ App (K₆.1 _ (by decide)) (K₆.1 _ (by decide)) K₆.2.1 K₆.2.2 sy₆, ?_, hu, ?_, F.odd,
    (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [bd])).mpr ⟨by omega_using [hge], F.lt⟩⟩
  · rw [Env.Chg.word v C₆ (by simp only [fUsed, hdr]; omega_using [sz]) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fUsed, hdr]; omega_using [sz]), F.used]
  · unfold Proof.Dsa.ProbablePrime.candidateAt
    obtain b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).bits / 8 = g.pLen := by
      show 8 * g.pLen / 8 = g.pLen; omega_using []
    rw [b8, VG.Offset.add_add, R₆, F.pk, VG.Proof.Dsa.decodeBE_encodeBE (by rw [e256]; exact F.lt)]

theorem pAttempt_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PAIn' E g)) g.pAttempt fun _ _ => True := by
  have sz := v.size_ge
  obtain lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  unfold Geo.pAttempt
  simp only [seqs]
  -- X.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, PAIn' E g a s ∧ XPost E g a.1 a.2.1 s t)
    (both_map (fun a => (a.1, a.2.1)) (fun a s h => ⟨h.base, h.hk, h.seed, h.offW, h.hoff⟩) (pX_ct G v hq))
    fun a s h => WP.mono (pX_ok G v hq h.base h.hk h.seed h.offW h.hoff) fun t X => ⟨s, h, X⟩) ?_
  -- p, and its guard.
  refine RelCT.assoc (RelCT.seq (both_post
    (Ψ := fun a t => ∃ s, PAIn' E g a s ∧ PAFront E g a.1 a.2.1 a.2.2.1 a.2.2.2 s t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, X⟩ := h; exact base_pins X.base)
      (RelCT.seq (pArith_ct G) (tcheck _ _ (by decide +kernel))))
    fun a t h => by
      obtain ⟨s, hs, X⟩ := h
      exact WP.mono (paMid_ok G v X hs.q hs.q0 hs.usedW hs.p4) fun u F => ⟨s, hs, F⟩) ?_)
  refine both_ite (fun a => decide (pcand g E a.1 a.2.1 a.2.2.1 < 2 ^ (8 * g.pLen - 1)))
    (fun a t h => by obtain ⟨s, _, F⟩ := h; exact F.zf) (RelCT.nil fun _ _ _ => trivial) ?_
  -- The candidate into the test's working space.
  refine RelCT.seq (both_post (Ψ := fun a t => TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨⟨s, _, F⟩, _⟩ := h; exact base_pins F.base)
      (tcheckE _ _ (copyS 0 0 1) (copyS_erase _ _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨⟨s, hs, F⟩, hb⟩ := h
      exact paCopy_ok G v F hs.hu (of_decide_eq_false hb)) ?_
  -- The test.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t)
    (both_map (fun a => (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1)) (fun _ _ h => h) (test_ct G.pv G.pNoSp G.pStack v lay))
    fun a u h => WP.mono (test_ok G.pv G.pNoSp G.pStack v h.1 h.2.1 h.2.2.1 lay (by rw [h.2.2.2.1]; exact h.2.2.2.2.1)
      (by rw [h.2.2.2.1]; exact h.2.2.2.2.2)) fun t P => ⟨u, h, by
        have e := h.2.2.2.1
        simp only at e
        rw [e] at P
        exact P⟩) ?_
  -- Its status.
  obtain hb : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t) → Base E t :=
    fun a t h => by obtain ⟨u, _, P⟩ := h; exact P.base
  obtain hw : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t) →
      t.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
        (Spec.Dsa.probablePrime (pcand g E a.1 a.2.1 a.2.2.1) (E.witT.drop a.2.2.2))) :=
    fun a t h => by obtain ⟨u, _, P⟩ := h; exact P.res
  refine cmpF_ct (by simp only [fRes, hdr]; omega_using [sz]) (by decide) _ hb hw (fun _ => status_lt _)
    (stImm_ct (fun a t h => h.1.base hb) _ _) ?_
  refine cmpF_ct (Φ := fun a t => CmpAfter _ a t ∧ _) (by simp only [fRes, hdr]; omega_using [sz]) (by decide) _
    (fun a t h => h.1.base hb) (fun a t h => by obtain ⟨⟨u, hu, _, m, _⟩, _⟩ := h; rw [m]; exact hw a u hu)
    (fun _ => status_lt _) (stImm_ct (fun a t h => h.1.base (fun a t h => h.1.base hb)) _ _)
    (RelCT.nil fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Generation

end

end


/-! # Two runs of p's search from the same seed and q leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The next counter: its flag, and what it keeps. -/
theorem pAdv_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {t : State} (B : Base E t) {c : Nat}
    (hc : c < 4 * (8 * g.pLen))
    (counter : t.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 c)
    (offset : t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + c * (g.count + 1))) :
    WP isa (.block g.pAdvance) t fun t' => isa.eval .e t' = some (decide (c + 1 = 4 * (8 * g.pLen))) ∧
      Base E t' ∧ ∀ d, d + 4 ≤ sState → (d + 4 ≤ fCounter ∨ fOffset + 4 ≤ d) →
        t'.mem.readW (off E.base d) 32 = t.mem.readW (off E.base d) 32 := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain cm : c * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega_using [hc, bd]) cnt
  obtain cs : (c + 1) * (g.count + 1) = c * (g.count + 1) + (g.count + 1) := Nat.succ_mul _ _
  obtain wst : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
      (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega_using [sz, h₁])
      (by simp only [sState] at h₂; omega_using [sz, h₂]) h x
  unfold Geo.pAdvance
  refine ld_ok B.scr (d := fCounter) (by simp only [fCounter, hdr]; omega_using [sz]) fun t₃ u₃ =>
    wp_addi fun t₄ u₄ => st_ok (Scr.of_eq B.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fCounter)
      (by simp only [fCounter, hdr]; omega_using [sz]) fun t₅ M₅ => ?_
  obtain eax₄ : t₄.gpr .eax = BitVec.ofNat 32 (c + 1) := by
    rw [u₄.gpr, u₃.gpr, counter, BitVec.ofNat_add]; rfl
  obtain m₅ : t₅.mem = t.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1)) := by
    rw [M₅.mem, u₄.mem, u₃.mem, eax₄]
  obtain hs₅ : Scr t₅ E.base E.size := Scr.of_eq B.scr (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [M₅.wr, u₄.wr, u₃.wr])
  refine ld_ok hs₅ (d := fOffset) (by simp only [fOffset, hdr]; omega_using [sz]) fun t₆ u₆ =>
    wp_addi fun t₇ u₇ => st_ok (Scr.of_eq hs₅ (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
      (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fOffset)
      (by simp only [fOffset, hdr]; omega_using [sz]) fun t₈ M₈ => wp_cmpi fun t₉ f₉ _ z₉ => WP.block_nil ?_
  obtain ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
    rw [u₇.gpr, u₆.gpr, m₅, wst _ (by simp only [fOffset, sState, hdr]; omega_using [])
      (by simp only [fCounter, sState, hdr]; omega_using []) (by simp only [fOffset, fCounter, hdr]; omega_using []),
      offset, ← BitVec.ofNat_add, cs, Nat.add_assoc]
  obtain m₉ : t₉.mem = (t.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1))).writeW (off E.base fOffset)
      (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by rw [f₉.mem, M₈.mem, u₇.mem, u₆.mem, ecx₇, m₅]
  obtain g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → t₉.gpr r = t.gpr r := fun r h₁ h₂ => by
    rw [f₉.gpr, M₈.gpr, u₇.other r h₂, u₆.other r h₂, M₅.gpr, u₄.other r h₁, u₃.other r h₁]
  refine ⟨?_, B.keep v (os := [(fCounter, 4), (fOffset, 4)]) ?_ (fun o ho => ?_) (g₉ _ (by decide) (by decide))
    (g₉ _ (by decide) (by decide)) (by rw [f₉.rd, M₈.rd, u₇.rd, u₆.rd, M₅.rd, u₄.rd, u₃.rd])
    (by rw [f₉.wr, M₈.wr, u₇.wr, u₆.wr, M₅.wr, u₄.wr, u₃.wr])
    (by rw [f₉.syms, M₈.syms, u₇.syms, u₆.syms, M₅.syms, u₄.syms, u₃.syms]), fun d h₁ h₂ => ?_⟩
  · show t₉.zf = _
    rw [z₉, M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), M₅.gpr, eax₄,
      show (BitVec.ofNat 32 (32 * g.pLen) : BitVec 32) = BitVec.ofNat 32 (4 * (8 * g.pLen)) by congr 1; omega_using [],
      sub_beq (by omega_using [hc, bd]) (by omega_using [bd])]
  · rw [m₉]
    exact ((Env.Chg.refl _ _).store (List.mem_cons_self) (by decide) _).store
      (List.mem_cons_of_mem _ List.mem_cons_self) (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [fCounter, fOffset, fOut, fWitLen, hdr] <;> omega_using [sz]
  · rw [m₉, wst _ h₁ (by simp only [fOffset, sState, hdr]; omega_using []) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega_using [h₂]),
      wst _ h₁ (by simp only [fCounter, sState, hdr]; omega_using []) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega_using [h₂])]

/-- `fP` after counter `c`'s candidate, from `u` witness octets read. -/
def fpA (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then 4
  else pCode (Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u))

/-- The witness octets read after counter `c`'s candidate. -/
def usedA (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then u
  else nextUsed E.witLen u (Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u))

/-- `fP` at the end of counter `c`. -/
def fpEnd (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if fpA g E k Q c u = 4 then (if c + 1 = 4 * (8 * g.pLen) then 2 else 4) else fpA g E k Q c u

theorem fpA_lt (g : Geo) (E : Env) (k Q c u : Nat) : fpA g E k Q c u < 2 ^ 32 := by
  unfold fpA pCode
  split
  · decide
  · split <;> (try split) <;> decide

theorem pAdvance_erase (g : Geo) : Code.erase (.block g.pAdvance) = Code.erase (.block
    [.mov .eax (.mem (sc fCounter)), .alu .add .eax (.imm 1), .store (sc fCounter) .eax,
      .mov .ecx (.mem (sc fOffset)), .alu .add .ecx (.imm 0), .store (sc fOffset) .ecx,
      .alu .cmp .eax (.imm 0)]) := rfl

/-- After counter `c`'s candidate, from the loop's head `s`. -/
def PAfter (E : Env) (g : Geo) (k Q : Nat) (R : Option (Option Nat × Spec.RsaKeyGen.Rand)) (a : Nat × Nat)
    (t : State) : Prop :=
  ∃ s, (∃ σ, PLoop E g k Q R σ a.1 a.2 s) ∧ a.1 < 4 * (8 * g.pLen) ∧
    PAPost E g k (1 + a.1 * (g.count + 1)) Q a.2 s t

/-- The counter's words through its candidate. -/
theorem PAfter.words {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} {a : Nat × Nat} {t : State} (h : PAfter E g k Q R a t) :
    t.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 a.1 ∧
      t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + a.1 * (g.count + 1)) := by
  obtain ⟨s, ⟨σ, L⟩, _, A⟩ := h
  have sz := v.size_ge
  obtain Apa := paRanges_apart G v
  obtain word₁ : ∀ d, d + 4 ≤ fP → fRes + 4 ≤ d →
      t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := fun d h₁ h₂ =>
    Env.Chg.word v A.chg (by simp only [fP, hdr] at h₁; omega_using [sz, h₁]) (fun o ho => ⟨(Apa o ho).1, by
      simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩)
  exact ⟨by rw [word₁ fCounter (by simp only [fCounter, fP, hdr]; omega_using []) (by simp only [fCounter, fRes, hdr]; omega_using []),
      L.counter],
    by rw [word₁ fOffset (by simp only [fOffset, fP, hdr]; omega_using []) (by simp only [fOffset, fRes, hdr]; omega_using []),
      L.offset]⟩

/-- The rest of a counter but its last comparison: `fP` and the witnesses read. -/
theorem pMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} {a : Nat × Nat} {t : State} (h : PAfter E g k Q R a t) :
    WP isa (.seq (.block (cmpF fP 4)) (.ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])])
      (.block []))) t fun t' => Base E t' ∧
      t'.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpEnd g E k Q a.1 a.2) ∧
      t'.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := by
  have sz := v.size_ge
  obtain ⟨cw, ow⟩ := h.words G v
  obtain ⟨s, _, hc, A⟩ := h
  have hU : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := A.used
  refine WP.seq (cmpF_end A.base.scr (o := fP) (v := 4) (w := fpA g E k Q a.1 a.2) (by simp only [fP, hdr]; omega_using [sz])
    A.fp (fpA_lt _ _ _ _ _ _) (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  obtain B₂ := A.base.regs m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine WP.ite _ z₂ (fun h4 => ?_) (fun h4 => WP.block_nil ⟨B₂, ?_, by rw [m₂, hU]⟩)
  · have F4 : fpA g E k Q a.1 a.2 = 4 := of_decide_eq_true h4
    simp only [seqs]
    refine WP.seq (WP.mono (pAdv_ok G v B₂ hc (by rw [m₂]; exact cw) (by rw [m₂]; exact ow)) fun t₃ ⟨z₃, B₃, w₃⟩ => ?_)
    obtain fP₃ : t₃.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
      rw [w₃ fP (by simp only [fP, sState, hdr]; omega_using []) (.inr (by simp only [fP, fOffset, hdr]; omega_using [])), m₂, A.fp]
      exact congrArg _ F4
    obtain fU₃ : t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := by
      rw [w₃ fUsed (by simp only [fUsed, sState, hdr]; omega_using []) (.inl (by simp only [fUsed, fCounter, hdr]; omega_using [])), m₂,
        hU]
    refine WP.ite _ z₃ (fun hd => stImm_end B₃.scr (o := fP) (v := 2) (by simp only [fP, hdr]; omega_using [sz])
      fun t₄ g₄ m₄ rd₄ wr₄ sy₄ => ⟨?_, ?_, ?_⟩) (fun hd => WP.block_nil ⟨B₃, ?_, fU₃⟩)
    · have C : E.Chg [(fP, 4)] t₃.mem t₄.mem := by
        rw [m₄]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
      obtain Ap : E.Apart [(fP, 4)] := fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fP, fOut, fWitLen, hdr]; omega_using [sz]
      exact B₃.keep v C Ap (g₄ _ (by decide)) (g₄ _ (by decide)) rd₄ wr₄ sy₄
    · rw [m₄, Mem.readW_writeW_self32]
      simp only [fpEnd, F4, of_decide_eq_true hd, ↓reduceIte]
    · rw [m₄, word_store_other v _ (by simp only [fUsed, hdr]; omega_using [sz]) (by simp only [fP, hdr]; omega_using [sz])
        (by simp only [fUsed, fP, hdr]; omega_using []), fU₃]
    · rw [fP₃]
      simp only [fpEnd, F4, of_decide_eq_false hd, ↓reduceIte]
  · rw [m₂, A.fp]
    simp only [fpEnd, of_decide_eq_false h4, ↓reduceIte]
    rfl

/-- Two runs of a counter from the same head: the loop's flag and the witnesses
read agree. -/
theorem pBody_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} (hk : (k + 1) * E.qLen ≤ E.seedsLen) (hQ0 : 0 < Q) :
    RelCT isa (Both fun (a : Nat × Nat) t => (∃ σ, PLoop E g k Q R σ a.1 a.2 t) ∧ a.1 < 4 * (8 * g.pLen))
      (seqs [g.pAttempt, .block (cmpF fP 4),
        .ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])]) (.block []),
        .block (cmpF fP 4)])
      (Both fun (a : Nat × Nat) t => isa.eval .e t = some (decide (fpEnd g E k Q a.1 a.2 = 4)) ∧
        t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2)) := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  simp only [seqs]
  -- The candidate.
  refine RelCT.seq (both_post (Ψ := PAfter E g k Q R)
    (both_map (fun a => (k, 1 + a.1 * (g.count + 1), Q, a.2)) (fun a t h => by
      obtain ⟨⟨σ, L⟩, hc⟩ := h
      obtain cm : a.1 * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega_using [bd, hc]) cnt
      exact ⟨L.keep.base, hk, L.keep.seed, L.offset, by show 1 + a.1 * (g.count + 1) + g.count + 256 ≤ 2 ^ 32; omega_using [cnt, cm],
        L.keep.q, hQ0, L.used, L.hu, L.fp⟩)
      (pAttempt_ct G v hq))
    fun a t h => by
      obtain ⟨⟨σ, L⟩, hc⟩ := h
      obtain cm : a.1 * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega_using [bd, hc]) cnt
      exact WP.mono (pAttempt_ok G v hq L.keep.base hk L.keep.seed L.offset (by omega_using [cnt, cm]) L.keep.q hQ0 L.used L.hu L.fp)
        fun u A => ⟨t, ⟨σ, L⟩, hc, A⟩) ?_
  -- Still searching or not, and the next counter.
  obtain hbA : ∀ a t, PAfter E g k Q R a t → Base E t := fun a t h => by obtain ⟨_, _, _, A⟩ := h; exact A.base
  refine RelCT.assoc (RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpEnd g E k Q a.1 a.2) ∧
      t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2))
    (cmpF_ct (by simp only [fP, hdr]; omega_using [sz]) (by decide) (fun a => fpA g E k Q a.1 a.2) hbA
      (fun a t h => by obtain ⟨_, _, _, A⟩ := h; exact A.fp) (fun a => fpA_lt _ _ _ _ _ _) ?_
      (RelCT.nil fun _ _ _ => trivial))
    fun a t h => pMid_ok G v h) ?_)
  · refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t =>
        isa.eval .e t = some (decide (a.1 + 1 = 4 * (8 * g.pLen))) ∧
        Base E t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (h.1.base hbA))
        (tcheckE _ _ _ (pAdvance_erase g) (by decide +kernel) (by decide +kernel)))
      fun a t h => by
        obtain ⟨⟨s, hs, gs, ms, rds, wrs, sys⟩, _⟩ := h
        obtain ⟨cw, ow⟩ := hs.words G v
        obtain ⟨_, _, hc, _⟩ := id hs
        exact WP.mono (pAdv_ok G v ((hbA a s hs).regs ms (gs _ (by decide)) (gs _ (by decide)) rds wrs sys) hc
          (by rw [ms]; exact cw) (by rw [ms]; exact ow)) fun u ⟨z, B, _⟩ => ⟨z, B⟩) ?_
    exact both_ite (fun a => decide (a.1 + 1 = 4 * (8 * g.pLen))) (fun a t h => h.1)
      (stImm_ct (fun a t h => h.1.2) _ _) (RelCT.nil fun _ _ _ => trivial)
  -- The loop's flag.
  refine both_post (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1)
    (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => cmpF_end h.1.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega_using [sz]) h.2.1 ?_ (by decide)
      fun u _ m _ _ _ z => ⟨z, by rw [m]; exact h.2.2⟩
  unfold fpEnd
  split
  · split <;> decide
  · exact fpA_lt _ _ _ _ _ _

/-- Before p's search: seed `a.1`, q `a.2.1`, the witness cursor at `a.2.2`. -/
def PPIn (E : Env) (g : Geo) (a : Nat × Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = a.2.1 ∧ 0 < a.2.1 ∧
    s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 a.2.2 ∧ a.2.2 ≤ E.witLen

theorem pPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PPIn E g)) g.pPart fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.witLen32
  refine both_exists fun a => ?_
  obtain ⟨k, Q, used⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.2.1, h.1.2.2.2.2.1⟩ : _ ∧ _)) fun ⟨hk, hQ0⟩ => ?_
  unfold Geo.pPart
  show RelCT isa _ (.seq (.block _) (.loop _ .e)) _
  generalize hR : Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used) = R
  let N := 4 * (8 * g.pLen)
  obtain N0 : 0 < N := by have := G.bounds; show 0 < 4 * (8 * g.pLen); omega_using [this]
  let I : Nat → State → State → Prop := fun n => Both fun (cu : Nat × Nat) t =>
    (∃ σ, PLoop E g k Q R σ cu.1 cu.2 t) ∧ cu.1 < N ∧ cu.1 + n = N
  refine RelCT.seq (R := I N) ?_ ?_
  · -- The state words.
    obtain tr : RelCT isa (fun s t => PPIn E g (k, Q, used) s ∧ PPIn E g (k, Q, used) t)
        (.block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4)) fun _ _ => True :=
      (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (base_pins h.1.1 r hr).trans (base_pins h.2.1 r hr).symm) fun _ _ h => h
    refine (tr.wpDep (F := fun σ t => PLoop E g k Q R σ 0 used t) fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h)
      fun s' t' ⟨_, σ₁, σ₂, _, L₁, L₂⟩ => ⟨(0, used), ⟨⟨σ₁, L₁⟩, N0, by simp⟩, ⟨σ₂, L₂⟩, N0, by simp⟩
    · obtain ⟨B, _, hS, hQ, _, hU, hu⟩ := h.1
      rw [← hR]; exact pInit_ok G v B hS hQ hU hu
    · obtain ⟨B, _, hS, hQ, _, hU, hu⟩ := h.2
      rw [← hR]; exact pInit_ok G v B hS hQ hU hu
  -- The counters.
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) N
  refine both_exists fun cu => ?_
  refine relct_of_fact (fun s t h => h.1.2.2) fun hcN => ?_
  let J : State → Prop := fun t => (∃ σ, PLoop E g k Q R σ cu.1 cu.2 t) ∧ cu.1 < N ∧ cu.1 + n = N
  obtain tr : RelCT isa (fun s t => J s ∧ J t) _ _ := (pBody_ct G v hq (R := R) (k := k) (Q := Q) hk hQ0).mono
    (fun s t h => by obtain ⟨⟨L₁, c₁, _⟩, L₂, _⟩ := h; exact ⟨cu, ⟨L₁, c₁⟩, L₂, c₁⟩) fun _ _ h => h
  refine (tr.wp (F₁ := fun (t' : State) => ∃ σ, (t'.zf = some false ∧ PKeep E g k Q σ t' ∧ PRes E g Q t'.mem R) ∨
      (t'.zf = some true ∧ cu.1 + 1 < 4 * (8 * g.pLen) ∧ ∃ u', PLoop E g k Q R σ (cu.1 + 1) u' t'))
    (F₂ := fun (t' : State) => ∃ σ, (t'.zf = some false ∧ PKeep E g k Q σ t' ∧ PRes E g Q t'.mem R) ∨
      (t'.zf = some true ∧ cu.1 + 1 < 4 * (8 * g.pLen) ∧ ∃ u', PLoop E g k Q R σ (cu.1 + 1) u' t'))
    fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, L⟩, hc, _⟩ := h.1
    exact WP.mono (pBody_ok G v hq hk hQ0 L hc) fun t' h' => ⟨σ, h'⟩
  · obtain ⟨⟨σ, L⟩, hc, _⟩ := h.2
    exact WP.mono (pBody_ok G v hq hk hQ0 L hc) fun t' h' => ⟨σ, h'⟩
  obtain ⟨⟨a', ψ₁, ψ₂⟩, ⟨σ₁, F₁⟩, ⟨σ₂, F₂⟩⟩ := H
  refine ⟨ψ₁.1.trans ψ₂.1.symm, fun _ => trivial, fun ht => ?_⟩
  change s'.zf = some true at ht
  obtain ht' : t'.zf = some true := by change isa.eval .e t' = _; rw [ψ₂.1, ← ψ₁.1]; exact ht
  rcases F₁ with ⟨z₁, _⟩ | ⟨_, hc₁, u₁, L₁⟩
  · rw [ht] at z₁; cases z₁
  rcases F₂ with ⟨z₂, _⟩ | ⟨_, _, u₂, L₂⟩
  · rw [ht'] at z₂; cases z₂
  obtain hu : u₁ = u₂ := by
    obtain e : BitVec.ofNat 32 u₁ = BitVec.ofNat 32 u₂ := by rw [← L₁.used, ← L₂.used, ψ₁.2, ψ₂.2]
    have := L₁.hu
    have := L₂.hu
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this
    exact this
  subst hu
  exact ⟨n - 1, by omega_using [hcN, hc₁], (cu.1 + 1, u₁), ⟨⟨σ₁, L₁⟩, hc₁, by omega_using [hcN, hc₁]⟩, ⟨σ₂, L₂⟩, hc₁, by omega_using [hcN, hc₁]⟩

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.GCT`, which only this module used -/

section

/-! # Two runs of the generator from the same `p` and `q` leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW slot stride contextBytes)

/-- `h` number `j` as a number. -/
abbrev hVal (E : Env) (j : Nat) : Nat := Spec.Dsa.decodeBE (hChunk E j)

/-- Before `h` number `a.1`, with `p`, `(p − 1)/q` and `fG` at `a.2`. -/
structure GSIn (E : Env) (g : Geo) (a : Nat × Nat × Nat × Nat) (s : State) : Prop where
  base : Base E s
  hj : (a.1 + 1) * E.pLen ≤ E.hsLen
  hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (a.1 * E.pLen)).setWidth 32
  hone : val32 s.mem E.base aOne g.n32 = 1
  hpm1 : val32 s.mem E.base aPm1 g.n32 = a.2.1 - 1
  hP : val32 s.mem E.base aP g.n32 = a.2.1
  hE : val32 s.mem E.base aE g.n32 = a.2.2.1
  hx : a.2.2.1 < 2 ^ (32 * g.e)
  hp1 : 1 < a.2.1
  hodd : a.2.1 % 2 = 1
  hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 a.2.2.2

/-- `h` loaded and compared: `h`'s address is the same in both runs. -/
theorem gHead_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) :
    RelCT isa (Both (GSIn E g)) (Prog.chain [.block [.mov .esi (.mem (sc fH)), .mov .ecx (.imm (BitVec.ofNat 32 g.pLen))],
      VG.Impl.Bignum.X86.loadBE g.n64 aH, chainW .sbb g.n32 aTmp aOne aH, .block [.store (sc fLo) .ecx],
      chainW .sbb g.n32 aTmp aH aPm1, .block [.alu .and .ecx (.mem (sc fLo)), .alu .cmp .ecx (.imm 0)]] (.block []))
      fun _ _ => True := by
  have sz := v.size_ge
  refine RelCT.seq (both_post (Ψ := fun a t => ∀ r ∈ [Reg.esp, .edi, .esi, .ecx],
      t.gpr r = if r = .esi then (E.hs + BitVec.ofNat 64 (a.1 * E.pLen)).setWidth 32
        else if r = .ecx then BitVec.ofNat 32 g.pLen else baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.base)
      (tcheckE _ _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0)]) rfl (by decide +kernel)
        (by decide +kernel))) fun a s h => ?_) ?_
  · refine ld_ok h.base.scr (d := fH) (by simp only [fH, hdr]; omega_using [sz]) fun t₁ u₁ => wp_movi fun t₂ u₂ =>
      WP.block_nil ?_
    obtain pins := base_pins h.base
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₂.other _ (by decide), u₁.gpr, h.hH]; rfl
    · rw [u₂.gpr]; rfl
  · refine both_agree [.esp, .edi, .esi, .ecx] _ (fun _ _ h => h) ?_
    unfold Geo.n64 Geo.n32
    rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)

/-- p, h and `(p − 1)/q` into the exponentiation's arrays. -/
theorem gSel_ct {g : Geo} (G : GeoOk g) {α : Type} {Φ : α → State → Prop} {E : Env}
    (hb : ∀ a s, Φ a s → Base E s) :
    RelCT isa (Both Φ) (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent] (.block []))
      fun _ _ => True := by
  refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h)) ?_
  rw [G.e]
  unfold Geo.n64 Geo.n32
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)

/-- What the exponentiation's timing needs of a run after the selections. -/
private theorem gPowCall_in {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} {p h x F : Nat}
    (hp1 : 1 < p) (hodd : p % 2 = 1) {s₆ : State} (S : SelPost E g p h x F s s₆) :
    VG.Proof.Dsa.X86.Pow.CallIn g.n64 s₆ := by
  have sz := v.size_ge
  have bd := G.bounds
  have n64 : g.n64 = g.pLen / 8 := rfl
  obtain cb : contextBytes g.n64 ≤ 7048 := by
    simp only [contextBytes, slot, stride]; omega_using [bd, n64]
  have low := v.low
  have ss := v.stackScratch
  refine ⟨E.base, E.size, S.scr, ?_, by omega_using [sz, cb], S.modv ▸ hp1, S.modv ▸ hodd⟩
  rw [S.sp]; exact ⟨by omega_using [low], ss.elim (fun h => .inl h) (fun h => .inr (by omega_using [h]))⟩

theorem gPow_dims {g : Geo} (G : GeoOk g) :
    2 ≤ g.n64 ∧ g.n64 ≤ 48 ∧ 1 < g.e ∧ g.e ≤ 2 * g.n64 := by
  rw [G.e]; unfold Geo.n64
  rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

/-- `g` and the check `g > 1`. -/
theorem gCall_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) :
    RelCT isa (Both fun (a : Nat × Nat × Nat × Nat) t => ∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧
        1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (Prog.chain [VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
        chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
        .block [.alu .cmp .ecx (.imm 0)]] (.block [])) fun _ _ => True := by
  have low := v.low
  obtain pinsOf : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧
      1 < a.2.1 ∧ a.2.1 % 2 = 1) → ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r := fun a t h => by
    obtain ⟨s, B, S, _⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact S.sp
    · rw [S.keeps.1 _ (by decide)]; exact B.edi
  let Pin : State → Prop := fun t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r
  refine RelCT.seq (R := fun t₁ t₂ => Pin t₁ ∧ Pin t₂) ?_ ?_
  · have D := gPow_dims G
    obtain call := (VG.Proof.Dsa.X86.Pow.call_relCT g.n64 g.e D.1 D.2.1 D.2.2.1 D.2.2.2).mono (P' := Both fun (a : Nat × Nat × Nat × Nat) t =>
        ∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧ 1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (fun s t h => by
        obtain ⟨a, h₁, h₂⟩ := h
        obtain p₁ := pinsOf a s h₁
        obtain p₂ := pinsOf a t h₂
        refine ⟨(p₁ _ (by simp)).trans (p₂ _ (by simp)).symm, (p₁ _ (by simp)).trans (p₂ _ (by simp)).symm, ?_⟩
        obtain ⟨s₀, _, S₁, hp1, hodd⟩ := h₁
        obtain ⟨t₀, _, S₂, _⟩ := h₂
        exact ⟨gPowCall_in G v hp1 hodd S₁, gPowCall_in G v hp1 hodd S₂⟩) (fun _ _ h => h)
    refine (call.wp (F₁ := Pin) (F₂ := Pin) fun s t h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    obtain ⟨a, ⟨s₀, _, S₁, hp1, hodd⟩, ⟨t₀, _, S₂, _⟩⟩ := h
    obtain p₁ := pinsOf a s ⟨s₀, ‹_›, S₁, hp1, hodd⟩
    obtain p₂ := pinsOf a t ⟨t₀, ‹_›, S₂, hp1, hodd⟩
    refine ⟨WP.mono (gPowCall_regs G v hp1 hodd S₁) fun u ⟨e₁, e₂⟩ r hr => ?_,
      WP.mono (gPowCall_regs G v hp1 hodd S₂) fun u ⟨e₁, e₂⟩ r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁]; exact p₁ _ (by simp)
      · rw [e₂]; exact p₁ _ (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁]; exact p₂ _ (by simp)
      · rw [e₂]; exact p₂ _ (by simp)
  · refine (show RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ _ from ?_).mono
      (fun s t h => agree_regs fun r hr => (h.1 r hr).trans (h.2 r hr).symm) fun _ _ h => h
    rw [show (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 from rfl]
    unfold Geo.n64 Geo.n32
    rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)

/-- One `h`. -/
theorem gStep_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    RelCT isa (Both (GSIn E g)) g.gStep fun _ _ => True := by
  have sz := v.size_ge
  unfold Geo.gStep
  show RelCT isa _ (Prog.chain [_, _, _, _, _, _] (.ite .e (.block []) _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a t => ∃ s, GSIn E g a s ∧ RangePost E g a.1 a.2.1 s t)
    (gHead_ct G v) fun a s h => gRange_ok G v hp h.base h.hj h.hH h.hone h.hpm1 (P := .block [])
      fun t R => WP.block_nil ⟨s, h, R⟩) ?_)
  refine both_ite (fun a => !decide (1 < hVal E a.1 ∧ hVal E a.1 < a.2.1 - 1))
    (fun a t h => by obtain ⟨s, _, R⟩ := h; exact R.zf) (RelCT.block_nil fun _ _ _ => trivial) ?_
  -- In range: `g`.
  show RelCT isa _ (Prog.chain [_, _, _, _, _, _, _, _, _] (.ite .e (.block []) _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a u => Base E u ∧
      isa.eval .e u = some (!decide (1 < gVal (hVal E a.1) a.2.1 a.2.2.1))) ?_
    fun a t h => by
      obtain ⟨⟨s, I, R⟩, _⟩ := h
      obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R I.hone I.hP I.hE I.hF
      exact gPowMid_ok G v R.base kP R.h kE I.hx kOne I.hp1 I.hodd fGR (P := .block [])
        fun u M => WP.block_nil ⟨M.base, M.zf⟩) ?_)
  · show RelCT isa _ (Prog.chain [_, _, _, _, _, _] (Prog.chain [_, _, _] (.block []))) _
    refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a t => ∃ s, Base E s ∧
        SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧ 1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (gSel_ct G fun a t h => by obtain ⟨⟨s, _, R⟩, _⟩ := h; exact R.base) fun a t h => ?_) (gCall_ct G v))
    obtain ⟨⟨s, I, R⟩, _⟩ := h
    obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R I.hone I.hP I.hE I.hF
    exact gPowSel_ok G v R.base kP R.h kE I.hx kOne fGR (P := .block [])
      fun u S => WP.block_nil ⟨t, R.base, S, I.hp1, I.hodd⟩
  refine both_ite (fun a => !decide (1 < gVal (hVal E a.1) a.2.1 a.2.2.1)) (fun a t h => h.2)
    (RelCT.block_nil fun _ _ _ => trivial) ?_
  -- `g` out.
  refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins h.1.1) ?_
  rw [show (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 from rfl]
  unfold Geo.n64
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)

/-- Before the generator, from `p` `a.1`, `q` `a.2.1` and `(p − 1)/q` `a.2.2`. -/
structure GPIn (E : Env) (g : Geo) (a : Nat × Nat × Nat) (s : State) : Prop where
  base : Base E s
  hsW : s.mem.readW (off E.base fHs) 32 = E.hs.setWidth 32
  hsLenW : s.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 E.hsLen
  hx' : a.2.2 = (a.1 - 1) / a.2.1
  hone : val32 s.mem E.base aOne g.n32 = 1
  hpm1 : val32 s.mem E.base aPm1 g.n32 = a.1 - 1
  hP : val32 s.mem E.base aP g.n32 = a.1
  hE : val32 s.mem E.base aE g.n32 = a.2.2
  hxl : a.2.2 < 2 ^ (32 * g.e)
  hp1 : 1 < a.1
  hodd : a.1 % 2 = 1
  hplt : a.1 < 2 ^ (8 * g.pLen)

theorem gPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    RelCT isa (Both (GPIn E g)) g.gPart fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.witLen32
  obtain hsl : E.hsLen < 2 ^ 32 := by have := v.hsIn; omega_using [lens, this]
  have pl := v.pLen_ge
  refine both_exists fun a => ?_
  obtain ⟨p, Q, x⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.hx', h.1.hxl, h.1.hp1, h.1.hodd, h.1.hplt⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _))
    fun ⟨hx', hxl, hp1, hodd, hplt⟩ => ?_
  unfold Geo.gPart
  show RelCT isa _ (.seq (.block _) (.loop _ .e)) _
  let N := E.hsLen / E.pLen + 1
  let GIn : State → Prop := fun σ => Base E σ ∧ val32 σ.mem E.base aOne g.n32 = 1 ∧
    val32 σ.mem E.base aPm1 g.n32 = p - 1 ∧ val32 σ.mem E.base aP g.n32 = p ∧ val32 σ.mem E.base aE g.n32 = x
  let I : Nat → State → State → Prop := fun n => Both fun (j : Nat) t =>
    (∃ σ, GIn σ ∧ GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t) ∧ j + n = N
  refine RelCT.seq (R := I N) ?_ ?_
  · -- The state words.
    obtain tr : RelCT isa (fun s t => GPIn E g (p, Q, x) s ∧ GPIn E g (p, Q, x) t)
        (.block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
          .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax]) fun _ _ => True :=
      (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (base_pins h.1.base r hr).trans (base_pins h.2.base r hr).symm) fun _ _ h => h
    refine (tr.wpDep (F := fun σ t => GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ 0 t)
      fun s t h => ⟨gInit_ok G v h.1.base p Q h.1.hsW h.1.hsLenW, gInit_ok G v h.2.base p Q h.2.hsW h.2.hsLenW⟩).mono (fun _ _ h => h)
      fun s' t' ⟨_, σ₁, σ₂, ⟨P₁, P₂⟩, L₁, L₂⟩ => ⟨0, ⟨⟨σ₁, ⟨P₁.base, P₁.hone, P₁.hpm1, P₁.hP, P₁.hE⟩, L₁⟩, by simp⟩,
        ⟨σ₂, ⟨P₂.base, P₂.hone, P₂.hpm1, P₂.hP, P₂.hE⟩, L₂⟩, by simp⟩
  -- The `h`s.
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) N
  refine both_exists fun j => ?_
  refine relct_of_fact (fun s t h => h.1.2) fun hjN => ?_
  let J : State → Prop := fun t => (∃ σ, GIn σ ∧ GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t) ∧ j + n = N
  obtain hbJ : ∀ (u : Unit) t, J t → Base E t := fun _ t h => by
    obtain ⟨⟨σ, _, L⟩, _⟩ := h; exact L.keep.base
  obtain tr : RelCT isa (fun s t => J s ∧ J t)
      (seqs [.block (cmpF fHLeft g.pLen),
        .ite .b (.block (stImm fG 2))
          (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fHLeft) .eax]]),
        .block (cmpF fG 4)]) fun _ _ => True := by
    refine (show RelCT isa (Both fun (_ : Unit) t => J t) _ _ from ?_).mono (fun s t h => ⟨(), h.1, h.2⟩)
      fun _ _ h => h
    simp only [seqs]
    refine RelCT.assoc (RelCT.seq (cmpFb_ct (o := fHLeft) (v := g.pLen) (by simp only [fHLeft, hdr]; omega_using [sz])
      (by have := G.bounds; omega_using [this]) (fun _ => E.hsLen - j * E.pLen) hbJ (fun _ t h => by obtain ⟨⟨σ, _, L⟩, _⟩ := h; exact L.left)
      (fun _ => by omega_using [hsl]) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ ?_)
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    · -- None left.
      exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (fun s t ⟨_, h₁, h₂⟩ => agree_regs fun r hr =>
        (base_pins (h₁.1.base hbJ) r hr).trans (base_pins (h₂.1.base hbJ) r hr).symm) fun _ _ h => h
    · -- `h` number `j`.
      obtain gs : ∀ (u : Unit) t, CmpAfter (fun (_ : Unit) t => J t) u t ∧
          decide (E.hsLen - j * E.pLen < g.pLen) = false → GSIn E g (j, p, x, 4) t := fun u t h => by
        obtain ⟨⟨s, ⟨⟨σ, ⟨_, hone, hpm1, hP, hE⟩, L⟩, _⟩, gr, m, rd, wr, sy⟩, hz⟩ := h
        obtain hne : ¬ E.hsLen - j * E.pLen < g.pLen := of_decide_eq_false hz
        obtain B : Base E t := L.keep.base.regs m (gr _ (by decide)) (gr _ (by decide)) rd wr sy
        obtain kept : ∀ {d : Nat}, 9728 ≤ d → d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d →
            d + 4 * g.n32 ≤ E.size → val32 t.mem E.base d g.n32 = val32 σ.mem E.base d g.n32 :=
          fun h₀ h₁ h₂ => by rw [m]; exact gkeep_arrs G v L.keep h₀ h₁ h₂
        have bd := G.bounds
        have n32 : g.n32 = g.pLen / 4 := rfl
        exact ⟨B, by show (j + 1) * E.pLen ≤ E.hsLen; rw [Nat.succ_mul]; omega_using [hp, pl, hne], by rw [m]; exact L.fh,
          by rw [kept (by simp only [aOne, arr]; omega_using []) (by simp only [aOne, arr]; omega_using [bd, n32])
            (by simp only [aOne, arr]; omega_using [sz, bd, n32]), hone],
          by rw [kept (by simp only [aPm1, arr]; omega_using []) (by simp only [aPm1, arr]; omega_using [bd, n32])
            (by simp only [aPm1, arr]; omega_using [sz, bd, n32]), hpm1],
          by rw [kept (by simp only [aP, arr]; omega_using []) (by simp only [aP, arr]; omega_using [])
            (by simp only [aP, arr]; omega_using [sz, bd, n32]), hP],
          by rw [kept (by simp only [aE, arr]; omega_using []) (by simp only [aE, arr]; omega_using [bd, n32])
            (by simp only [aE, arr]; omega_using [sz, bd, n32]), hE], hxl, hp1, hodd, by rw [m]; exact L.fg⟩
      refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
        (both_map (fun _ => (j, p, x, 4)) gs (gStep_ct G v hp)) fun u t h => ?_) ?_
      · have I := gs u t h
        exact WP.mono (gStep_ok G v hp I.base I.hj I.hH I.hone I.hpm1 I.hP I.hE I.hx I.hp1 I.hodd hplt I.hF)
          fun _ S => S.base
      · refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h) ?_
        rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;>
          exact tkeep _ _ (by decide +kernel)
  obtain post : ∀ (σ t : State), GIn σ → GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t →
      WP isa (seqs [.block (cmpF fHLeft g.pLen),
        .ite .b (.block (stImm fG 2))
          (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fHLeft) .eax]]),
        .block (cmpF fG 4)]) t fun t' => isa.eval .e t' = some (gCont E p x j) ∧
          (gCont E p x j = true → (j + 1) * E.pLen ≤ E.hsLen ∧
            GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ (j + 1) t') := fun σ t ⟨_, hone, hpm1, hP, hE⟩ L =>
    WP.mono (gBody_ok G v hp hx' hone hpm1 hP hE hxl hp1 hodd hplt L) fun t' h => by
      rcases h with ⟨z, c, _⟩ | ⟨z, c, hj1, L'⟩
      · exact ⟨by rw [c]; exact z, fun h => absurd (c.symm.trans h) (by decide)⟩
      · exact ⟨by rw [c]; exact z, fun _ => ⟨hj1, L'⟩⟩
  refine (tr.wpDep (F := fun s t' => ∃ σ, GIn σ ∧ isa.eval .e t' = some (gCont E p x j) ∧
      (gCont E p x j = true → (j + 1) * E.pLen ≤ E.hsLen ∧
        GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ (j + 1) t')) fun s t h => ⟨?_, ?_⟩).mono
    (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, hσ, L⟩, _⟩ := h.1
    exact WP.mono (post σ s hσ L) fun t' h' => ⟨σ, hσ, h'⟩
  · obtain ⟨⟨σ, hσ, L⟩, _⟩ := h.2
    exact WP.mono (post σ t hσ L) fun t' h' => ⟨σ, hσ, h'⟩
  obtain ⟨_, _, _, _, ⟨σ₁, hσ₁, z₁, c₁⟩, ⟨σ₂, hσ₂, z₂, c₂⟩⟩ := H
  refine ⟨z₁.trans z₂.symm, fun _ => trivial, fun ht => ?_⟩
  obtain hc : gCont E p x j = true := by rw [z₁] at ht; exact Option.some.inj ht
  obtain ⟨hj1, L₁⟩ := c₁ hc
  obtain ⟨_, L₂⟩ := c₂ hc
  have : j + 1 ≤ E.hsLen / E.pLen := (Nat.le_div_iff_mul_le (by omega_using [pl])).mpr hj1
  exact ⟨n - 1, by omega_using [hjN, this], j + 1, ⟨⟨σ₁, hσ₁, L₁⟩, by omega_using [hjN, this]⟩, ⟨σ₂, hσ₂, L₂⟩, by omega_using [hjN, this]⟩

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.CheckCT`, which only this module used -/

section

/-! # Two runs of the domain check of the same p||q||g leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

/-- The check's writable regions, at the generator's stack pointer. -/
def chkWrSp (E : Env) : List Region :=
  [⟨off E.base sChk, 16 * E.pLen * 8⟩, ⟨(E.sp - 24#32).setWidth 64, 24⟩]

theorem chkWr_sp {E : Env} {t : State} (h : t.gpr .esp = E.sp) : chkWr E t = chkWrSp E := by
  simp only [chkWr, chkWrSp, h]

/-- Before the check: p||q||g. -/
def CIn (E : Env) (g : Geo) (b : List Byte) (s : State) : Prop :=
  Base E s ∧ Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen) = b

theorem wp_of_seq_nil {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c (.block [])) s Q) :
    WP isa c s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨_, _, e₁, q⟩

/-- The check's call keeps `esp` and `edi`. -/
theorem chkCall_regs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s t : State} (B : Base E s) (A : ChkArgs E g s t) :
    WP isa (.frame (.push [.ebp, .esi, .ebx, .edx, .ecx, .eax]) (.call g.checkName g.checkCode) (.pop .ecx 6)) t
      fun u => u.gpr .esp = t.gpr .esp ∧ u.gpr .edi = t.gpr .edi := by
  have low := v.low
  have cs := G.cStack
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  exact WP.of_syms (WP.callWithReturn G.cv.1 G.cNoSp (by decide) (by decide)
    (by rw [spT]; simp only [List.length_cons, List.length_nil]; omega_using [low, cs]) (chk_callPre G v hp hq B A)
    fun u _ _ csu _ _ _ => ⟨csu .esp (by decide), csu .edi (by decide)⟩)

/-- What the check sees: its arguments and p||q||g. -/
theorem chkEntry_facts {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} (B : Base E s) (A : ChkArgs E g s t) :
    ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)).gpr .esp = E.sp - 28#32 ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 0 = s.gpr .edi + BitVec.ofNat 32 sPk ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 1 =
        BitVec.ofNat 32 (2 * g.pLen + g.qLen) ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 2 = BitVec.ofNat 32 g.pLen ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 3 = BitVec.ofNat 32 g.qLen ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 4 = s.gpr .edi + BitVec.ofNat 32 sChk ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 5 = BitVec.ofNat 32 (16 * g.pLen) ∧
      Spec.Rsa.bytesAt ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)).mem
        ((s.gpr .edi + BitVec.ofNat 32 sPk).setWidth 64) (2 * g.pLen + g.qLen) =
        Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen) := by
  have sz := v.size_ge
  have bd := G.bounds
  have low := v.low
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  obtain fitT : 28 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_using [low]
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := chkEntry_arg (E := E) (s := t) fitT
  obtain Fm := chkEntry_mem (E := E) (s := t) fitT
  simp only [chkEntry, chkWr_sp spT] at e0 e1 e2 e3 e4 e5 Fm
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.esi] at e4; rw [A.ebp] at e5
  refine ⟨?_, e0, e1, e2, e3, e4, e5, ?_⟩
  · change (pushed chkRegs t).callEntry.gpr .esp = _
    rw [callEntry_esp' chkRegs t, spT]; rfl
  · have pW := Scr.wide B.scr (d := sPk) (by simp only [sPk]; omega_using [sz])
    rw [pW, ← A.mem]
    rw [spT] at Fm
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨off E.base sPk, 2 * g.pLen + g.qLen⟩) ?_ (by show 2 * g.pLen + g.qLen ≤ 2 ^ 64; omega_using [bd]) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (v.scratchStack.sub_left (Offset.sub_base _ (by simp only [sPk]; omega_using [sz, bd]))).sub_right
      (below_sub (by decide) (by omega_using [low]))

theorem check_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (CIn E g)) (check g.pLen g.qLen (16 * g.pLen) g.checkName g.checkCode) fun _ _ => True := by
  have sz := v.size_ge
  have low := v.low
  unfold check
  show RelCT isa _ (Prog.chain [_, _, _] (.ite .e _ _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun b x => ∃ s, CIn E g b s ∧
      ChkMid E g (Spec.Dsa.checkParametersBytes g.pLen g.qLen b) s x) ?_
    fun b s h => checkMid_ok G v hp hq h.1 (P := .block []) fun x M => WP.block_nil ⟨s, h, by rw [← h.2]; exact M⟩) ?_)
  · -- The arguments.
    refine RelCT.seq (both_post (Ψ := fun b t => ∃ s, CIn E g b s ∧ ChkArgs E g s t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1) ?_)
      fun b s h => wp_of_seq_nil (chkArgs_ok (rest := .block []) fun t A => WP.block_nil ⟨s, h, A⟩)) ?_
    · rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)
    obtain pins : ∀ (b : List Byte) t, (∃ s, CIn E g b s ∧ ChkArgs E g s t) → ∀ r ∈ [Reg.esp, .edi],
        t.gpr r = baseVal E r := by
      rintro b t ⟨s, h, A⟩ r hr
      rw [A.other r (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide)]
      exact base_pins h.1 r hr
    let Pin : State → Prop := fun t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r
    refine RelCT.seq (R := fun u₁ u₂ => Pin u₁ ∧ Pin u₂) ?_ ?_
    · -- The call.
      refine both_exists fun b => ?_
      refine ((callWithPop (rs := chkRegs) G.cv.1 G.cv.2.1 (chkRd E) (chkWrSp E) fun t₁ t₂ hp => ?_).wp
        (F₁ := Pin) (F₂ := Pin) fun t₁ t₂ h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun _ _ h => h.2
      · obtain ⟨⟨s₁, h₁, A₁⟩, ⟨s₂, h₂, A₂⟩⟩ := hp
        obtain sp₁ : t₁.gpr .esp = E.sp := pins b t₁ ⟨s₁, h₁, A₁⟩ _ (by simp)
        obtain sp₂ : t₂.gpr .esp = E.sp := pins b t₂ ⟨s₂, h₂, A₂⟩ _ (by simp)
        obtain c₁ := chk_callPre G v hp hq h₁.1 A₁
        obtain c₂ := chk_callPre G v hp hq h₂.1 A₂
        rw [chkWr_sp sp₁] at c₁
        rw [chkWr_sp sp₂] at c₂
        refine ⟨c₁, c₂, sp₁.trans sp₂.symm, ?_⟩
        obtain ⟨esp₁, a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, by₁⟩ := chkEntry_facts G v h₁.1 A₁
        obtain ⟨esp₂, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, by₂⟩ := chkEntry_facts G v h₂.1 A₂
        generalize (pushed chkRegs t₁).callEntry.withRegions (chkRd E) (chkWrSp E) = w₁ at esp₁ a0₁ a1₁ a2₁ a3₁ a4₁ a5₁ by₁ ⊢
        generalize (pushed chkRegs t₂).callEntry.withRegions (chkRd E) (chkWrSp E) = w₂ at esp₂ a0₂ a1₂ a2₂ a3₂ a4₂ a5₂ by₂ ⊢
        sig_pub [chkContract, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal,
          argBytes]
        obtain l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
          have := G.bounds; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]
        refine ⟨by rw [esp₁, esp₂], ?_, by rw [a0₁, a0₂, h₁.1.edi, h₂.1.edi], by rw [a1₁, a1₂],
          by rw [a2₁, a2₂], by rw [a3₁, a3₂], by rw [a4₁, a4₂, h₁.1.edi, h₂.1.edi], by rw [a5₁, a5₂]⟩
        rw [a0₁, a1₁, l1, by₁, a0₂, a1₂, l1, by₂, h₁.2, h₂.2]
      · obtain ⟨⟨s, h, A⟩, _⟩ := h
        exact WP.mono (chkCall_regs G v hp hq h.1 A) fun u ⟨e₁, e₂⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [e₁]; exact pins b t₁ ⟨s, h, A⟩ _ (by simp)
          · rw [e₂]; exact pins b t₁ ⟨s, h, A⟩ _ (by simp)
      · obtain ⟨_, ⟨s, h, A⟩⟩ := h
        exact WP.mono (chkCall_regs G v hp hq h.1 A) fun u ⟨e₁, e₂⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [e₁]; exact pins b t₂ ⟨s, h, A⟩ _ (by simp)
          · rw [e₂]; exact pins b t₂ ⟨s, h, A⟩ _ (by simp)
    · exact (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (h.1 r hr).trans (h.2 r hr).symm) fun _ _ h => h
  refine both_ite (fun b => Spec.Dsa.checkParametersBytes g.pLen g.qLen b) (fun b x h => by
      obtain ⟨s, _, M⟩ := h; exact M.zf)
    (stImm_ct (fun b x h => by obtain ⟨⟨s, _, M⟩, _⟩ := h; exact M.base) _ _) (RelCT.block_nil fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Generation

end

end


/-! # Two runs of a seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation

/-- Before seed `a.1`, with the witness cursor at `a.2`. -/
def AIn (E : Env) (a : Nat × Nat) (s : State) : Prop :=
  QIn E a s ∧ s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0

/-- q of seed `a.1`. -/
abbrev qVal (E : Env) (g : Geo) (a : Nat × Nat) : Nat := Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1)

/-- q's test. -/
abbrev qRes (E : Env) (g : Geo) (a : Nat × Nat) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (qVal E g a) (E.witT.drop a.2)

/-- The witness cursor after q's test. -/
abbrev qUsed (E : Env) (g : Geo) (a : Nat × Nat) : Nat := nextUsed E.witLen a.2 (qRes E g a)

/-- p's search. -/
abbrev pRes (E : Env) (g : Geo) (a : Nat × Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) (qVal E g a) (chunk E a.1) (E.witT.drop (qUsed E g a))

/-- `fP` for p's search. -/
def fpOf : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (none, _) => 2
  | some (some _, _) => 1

/-- The p found. -/
def pOf : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | some (some p, _) => p
  | _ => 0

/-- The witnesses p's search left. -/
def pRest : Option (Option Nat × Spec.RsaKeyGen.Rand) → Spec.RsaKeyGen.Rand
  | some (_, r) => r
  | none => []

/-- The octets of `rand` read before the window of `h` candidates. -/
abbrev pUsed (E : Env) (g : Geo) (a : Nat × Nat) : Nat := E.witLen - (pRest (pRes E g a)).length

/-- The window's environment. -/
abbrev gEnv (E : Env) (g : Geo) (a : Nat × Nat) : Env := E.window (pUsed E g a)

/-- The generator's search. -/
abbrev gRes (E : Env) (g : Geo) (a : Nat × Nat) : Option Nat :=
  Spec.Dsa.generator (pOf (pRes E g a)) (qVal E g a) (hList (gEnv E g a))

/-- `fG` for the generator's search. -/
def fgOf : Option Nat → Nat
  | none => 2
  | some _ => 1

/-- The g found. -/
def gOf : Option Nat → Nat
  | none => 0
  | some g => g

theorem PRes.fp {E : Env} {g : Geo} {Q : Nat} {m : Mem} {R : Option (Option Nat × Spec.RsaKeyGen.Rand)}
    (h : PRes E g Q m R) : m.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpOf R) := by
  rcases R with _ | ⟨_ | p, rest⟩
  · exact h
  · exact h.1
  · exact h.1

theorem GRes.fg {E : Env} {g : Geo} {m : Mem} {R : Option Nat} (h : GRes E g m R) :
    m.readW (off E.base fG) 32 = BitVec.ofNat 32 (fgOf R) := by
  rcases R with _ | gv
  · exact h
  · exact h.1

/-- The state a comparison was made from. -/
theorem CmpAfter.elim {α : Type} {Φ : α → State → Prop} {a : α} {t : State} (h : CmpAfter Φ a t) :
    ∃ s, Φ a s ∧ t.mem = s.mem ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  obtain ⟨s, hs, g, m, rd, wr, sy⟩ := h
  exact ⟨s, hs, m, g _ (by decide), g _ (by decide), rd, wr, sy⟩

/-- After q. -/
def AQ (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop := ∃ s, AIn E a s ∧ QPost E g a.1 a.2 s t

/-- q a probable prime: before p. -/
def AQp (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  CmpAfter (fun a t => CmpAfter (AQ E g) a t ∧
    decide (Proof.Dsa.ProbablePrime.status (qRes E g a) = 0) = false) a t ∧
    decide (Proof.Dsa.ProbablePrime.status (qRes E g a) = 1) = true

/-- After p. -/
def AP (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AQp E g a s ∧ PKeep E g a.1 (qVal E g a) s t ∧ PRes E g (qVal E g a) t.mem (pRes E g a)

/-- p found: before g. -/
def APg (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  CmpAfter (fun a t => CmpAfter (AP E g) a t ∧ decide (fpOf (pRes E g a) = 0) = false) a t ∧
    decide (fpOf (pRes E g a) = 1) = true

/-- After the window. -/
def AW (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, APg E g a s ∧ Base E t ∧ E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.syms = s.syms ∧ t.mem.readW (off E.base fHs) 32 = (gEnv E g a).hs.setWidth 32 ∧
    t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (gEnv E g a).hsLen

/-- After g. -/
def AG (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AW E g a s ∧ GKeep (gEnv E g a) g s t ∧ GRes (gEnv E g a) g t.mem (gRes E g a)

/-- After the candidates read. -/
def AU (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AG E g a s ∧ (∃ x : BitVec 32, t.mem = s.mem.writeW (off E.base fUsed) x) ∧ t.gpr .edi = s.gpr .edi ∧
    t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms

theorem AQ.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AQ E g a t) : Base E t := by
  obtain ⟨_, _, Q⟩ := h; exact Q.base

theorem AP.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AP E g a t) : Base E t := by
  obtain ⟨_, _, P, _⟩ := h; exact P.base

theorem AG.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AG E g a t) : Base E t := by
  obtain ⟨_, _, K, _⟩ := h; exact K.base.ofWindow

theorem AU.base {E : Env} {g : Geo} (v : E.Valid) {a : Nat × Nat} {t : State} (h : AU E g a t) : Base E t := by
  obtain ⟨s, A, ⟨x, m⟩, e, p, r, w, y⟩ := h
  have := v.size_ge
  obtain C : E.Chg [(fUsed, 4)] s.mem t.mem := by
    rw [m]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact A.base.keep v C (fun o ho => by
    simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, fOut, fUsedP, fWitLen, hdr]; omega_using [this]) e p r w y

/-- The window's length, after the candidates read. -/
theorem AU.len {E : Env} {g : Geo} (G : GeoOk g) (v : E.Valid) {a : Nat × Nat} {t : State} (h : AU E g a t) :
    t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (gEnv E g a).hsLen := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain ⟨t₇, ⟨t₆, ⟨t₅, A, -, -, -, -, -, -, hl⟩, GK, _⟩, ⟨x, m⟩, -⟩ := h
  obtain gA := gRanges_apart G v
  rw [m, word_store_other v _ (by simp only [fHsLen, hdr]; omega_using [sz]) (by simp only [fUsed, hdr]; omega_using [sz])
    (by simp only [fUsed, fHsLen, hdr]; omega_using []),
    Env.Chg.word v (GK.chg : E.Chg _ _ _) (by simp only [fHsLen, hdr]; omega_using [sz]) (fun o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, fHsLen, hdr] <;> omega_using []⟩), hl]

/-- p's inputs, from q. -/
theorem aqp_ppIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {a : Nat × Nat}
    {t : State} (h : AQp E g a t) : PPIn E g (a.1, qVal E g a, qUsed E g a) t := by
  have bd := G.bounds
  obtain ⟨C₂, _⟩ := h
  obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
  obtain ⟨t₁, ⟨s, A, Q⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
  obtain K₁ : AKeep E g s t₁ := ⟨Q.base, Q.chg.widen fun o ho => ⟨o, by simp [atRanges, ho], Nat.le_refl _,
    Nat.le_refl _⟩, Q.rd, Q.wr, Q.syms⟩
  obtain K : AKeep E g s t := K₁.mem (m₂.trans m₁) (e₂.trans e₁) (p₂.trans p₁) (r₂.trans r₁) (w₂.trans w₁)
    (y₂.trans y₁)
  obtain qsh := qCandidate_shape (n := 8 * g.qLen) (by omega_using [bd]) (chunk E a.1)
  refine ⟨K.base, A.1.2.1, ?_, by rw [m₂, m₁]; exact Q.q, Nat.lt_of_lt_of_le (Nat.two_pow_pos _) qsh.2.1,
    by rw [m₂, m₁]; exact Q.used, ?_⟩
  · rw [K.word G v hp (by simp only [fSeed]; omega_using []) (by simp only [fSeed, fUsed, hdr]; omega_using [])]
    exact A.1.2.2.1
  · have := A.1.2.2.2.2
    show nextUsed E.witLen a.2 (qRes E g a) ≤ E.witLen
    generalize qRes E g a = r
    rcases r with _ | ⟨_, rest⟩
    · exact this
    · exact Nat.sub_le _ _

/-- The generator's inputs, from p and the window. -/
theorem aw_gpIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {a : Nat × Nat} {t : State} (h : AW E g a t) :
    GPIn (gEnv E g a) g (pOf (pRes E g a), qVal E g a, (pOf (pRes E g a) - 1) / qVal E g a) t := by
  have bd := G.bounds
  have sz := v.size_ge
  obtain ⟨s₀, ⟨C₂, h1⟩, B, CW, -, -, -, hsW, hsLenW⟩ := h
  obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
  obtain ⟨t₁, ⟨s, _, P, R⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
  obtain wV : ∀ d, fHsLen + 4 ≤ d → d + 4 * g.n32 ≤ E.size →
      val32 t.mem E.base d g.n32 = val32 t₁.mem E.base d g.n32 := fun d h h' => by
    rw [Env.Chg.val32 v CW h' fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega_using [sz], by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] at h ⊢ <;> omega_using [h]⟩, m₂, m₁]
  have n32 : g.n32 = g.pLen / 4 := rfl
  generalize pRes E g a = R' at R h1 hsW hsLenW ⊢
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at h1
  · simp [fpOf] at h1
  obtain ⟨_, plo, phi, podd, ⟨u, hu, fu, du⟩, _, pm, e, pv, one⟩ := R
  obtain qsh := qCandidate_shape (n := 8 * g.qLen) (by omega_using [bd]) (chunk E a.1)
  obtain hxl : (p - 1) / qVal E g a < 2 ^ (32 * g.e) := by
    obtain ex : 8 * g.pLen ≤ 32 * g.e + (8 * g.qLen - 1) := by
      rw [G.e]; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
    unfold qVal
    rw [Nat.div_lt_iff_lt_mul (by have := Nat.two_pow_pos (8 * g.qLen - 1); have := qsh.2.1; omega_using [qsh])]
    have := Nat.mul_le_mul_left (2 ^ (32 * g.e)) qsh.2.1
    rw [← Nat.pow_add] at this
    have := Nat.pow_le_pow_right (n := 2) (by decide) ex
    omega_arith
  obtain hp1 : 1 < p := by have := Nat.one_lt_two_pow (n := 8 * g.pLen - 1) (by omega_using [bd]); omega_using [plo, this]
  simp only [pOf]
  exact ⟨B.toWindow _, hsW, hsLenW, rfl,
    by show val32 t.mem E.base aOne g.n32 = _
       rw [wV _ (by simp only [aOne, arr, fHsLen, hdr]; omega_using []) (by simp only [aOne, arr]; omega_using [bd, sz, n32])]; exact one,
    by show val32 t.mem E.base aPm1 g.n32 = _
       rw [wV _ (by simp only [aPm1, arr, fHsLen, hdr]; omega_using []) (by simp only [aPm1, arr]; omega_using [bd, sz, n32])]; exact pm,
    by show val32 t.mem E.base aP g.n32 = _
       rw [wV _ (by simp only [aP, arr, fHsLen, hdr]; omega_using []) (by simp only [aP, arr]; omega_using [bd, sz, n32])]; exact pv,
    by show val32 t.mem E.base aE g.n32 = _
       rw [wV _ (by simp only [aE, arr, fHsLen, hdr]; omega_using []) (by simp only [aE, arr]; omega_using [bd, sz, n32])]; exact e,
    hxl, hp1, podd, phi⟩

/-- p||q||g, for the domain check. -/
theorem ag_cIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {a : Nat × Nat} {t : State}
    (h : CmpAfter (AU E g) a t ∧ decide (fgOf (gRes E g a) = 1) = true) :
    CIn E g (Spec.Dsa.encodeParams g.pLen g.qLen ⟨pOf (pRes E g a), qVal E g a, gOf (gRes E g a)⟩) t := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain ⟨C, h1⟩ := h
  obtain ⟨tU, AUh, m, e, p_, r, w, y⟩ := C.elim
  obtain BU := AUh.base v
  obtain ⟨t₇, ⟨t₆w, ⟨t₆, ⟨C₆, hf⟩, -, CW, -, -, -, -, -⟩, GK, GR⟩, ⟨x, mU⟩, -⟩ := AUh
  obtain ⟨t₅, ⟨C₅, _⟩, m₆, -, -, -, -, -⟩ := C₆.elim
  obtain ⟨t₄, ⟨t₃, _, PK, PR⟩, m₅, -, -, -, -, -⟩ := C₅.elim
  refine ⟨BU.regs m e p_ r w y, ?_⟩
  generalize gRes E g a = G' at GR h1 ⊢
  rcases G' with _ | gv
  · simp [fgOf] at h1
  generalize pRes E g a = R' at PR hf ⊢
  obtain gA := gRanges_apart G v
  obtain toU : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + 2 * g.pLen + g.qLen →
      Spec.Rsa.bytesAt t.mem (off E.base d) n = Spec.Rsa.bytesAt t₇.mem (off E.base d) n := fun h₁ h₂ => by
    rw [m, mU, Env.Chg.scratch v ((Env.Chg.refl [(fUsed, 4)] t₇.mem).store (List.mem_singleton_self _)
      (by decide) _) (by simp only [sPk] at h₂; omega_using [sz, bd, h₂]) (fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, sPk, hdr] at h₁ ⊢; omega_using [sz, h₁])]
  obtain to6 : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + g.pLen + g.qLen →
      Spec.Rsa.bytesAt t.mem (off E.base d) n = Spec.Rsa.bytesAt t₆.mem (off E.base d) n := fun h₁ h₂ => by
    rw [toU h₁ (by omega_using [h₂]), Env.Chg.scratch v (GK.chg : E.Chg _ _ _) (by simp only [sPk] at h₂; omega_using [sz, bd, h₂])
      (fun o ho => ⟨(gA o ho).1, by
        simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩),
      Env.Chg.scratch v CW (by simp only [sPk] at h₂; omega_using [sz, bd, h₂]) (fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega_using [sz], by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, sPk, hdr] at h₁ ⊢ <;> omega_using [h₁]⟩)]
  obtain mem : t₆.mem = t₄.mem := m₆.trans m₅
  obtain qk : Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen = Spec.Dsa.encodeBE g.qLen (qVal E g a) := by
    rw [to6 (by omega_using []) (by omega_using []), mem, ← PK.q]
    obtain h := encodeBE_decodeBE (Spec.Rsa.bytesAt t₄.mem (off E.base (sPk + g.pLen)) g.qLen)
    rw [VG.Proof.Bignum.bytesAt_length] at h
    exact h.symm
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at hf
  · simp [fpOf] at hf
  obtain ⟨_, _, _, _, _, pk, _⟩ := PR
  obtain pk' : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
    rw [to6 (Nat.le_refl _) (by omega_using []), mem, pk]
  obtain gk : Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv := by
    rw [toU (by omega_using []) (by omega_using [])]; exact GR.2
  simp only [pOf, gOf]
  rw [show 2 * g.pLen + g.qLen = g.pLen + (g.qLen + g.pLen) by omega_using [], bytesAt_append, bytesAt_append,
    show VG.Proof.Bignum.off (off E.base sPk) g.pLen = off E.base (sPk + g.pLen) from off_add_ofNat _ _ _,
    show VG.Proof.Bignum.off (off E.base (sPk + g.pLen)) g.qLen = off E.base (sPk + g.pLen + g.qLen)
      from off_add_ofNat _ _ _, pk', qk, gk, Spec.Dsa.encodeParams, List.append_assoc]

theorem attempt_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (AIn E)) g.attempt fun _ _ => True := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain fpLt : ∀ R : Option (Option Nat × Spec.RsaKeyGen.Rand), fpOf R < 2 ^ 32 := fun R => by
    rcases R with _ | ⟨_ | _, _⟩ <;> simp [fpOf]
  obtain fgLt : ∀ R : Option Nat, fgOf R < 2 ^ 32 := fun R => by rcases R with _ | _ <;> simp [fgOf]
  unfold Geo.attempt
  simp only [seqs]
  -- q.
  refine RelCT.seq (both_post (Ψ := AQ E g) (both_map id (fun a s h => h.1) (qPart_ct G v hq))
    fun a s h => WP.mono (qPart_ok G v hp hq h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2)
      fun t Q => ⟨s, h, Q⟩) ?_
  refine cmpF_ct (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega_using [sz]) (by decide)
    (fun a => Proof.Dsa.ProbablePrime.status (qRes E g a)) (fun a t h => h.base)
    (fun a t h => by obtain ⟨_, _, Q⟩ := h; exact Q.res) (fun a => status_lt _)
    (stImm_ct (fun a t h => h.1.base fun _ _ h => h.base) _ _) ?_
  refine cmpF_ct (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega_using [sz]) (by decide)
    (fun a => Proof.Dsa.ProbablePrime.status (qRes E g a)) (fun a t h => h.1.base fun _ _ h => h.base)
    (fun a t h => by obtain ⟨u, ⟨s₀, -, Q⟩, m, -⟩ := h.1.elim; rw [m]; exact Q.res) (fun a => status_lt _)
    ?_ (RelCT.block_nil fun _ _ _ => trivial)
  -- p.
  refine (show RelCT isa (Both (AQp E g)) _ _ from ?_)
  refine RelCT.seq (both_post (Ψ := AP E g)
    (both_map (fun a => (a.1, qVal E g a, qUsed E g a)) (fun a t h => aqp_ppIn G v hp h) (pPart_ct G v hq))
    fun a t h => ?_) ?_
  · have I := aqp_ppIn G v hp h
    exact WP.mono (pPart_ok G v hq I.1 I.2.1 I.2.2.1 I.2.2.2.1 I.2.2.2.2.1 I.2.2.2.2.2.1 I.2.2.2.2.2.2)
      fun u ⟨P, R⟩ => ⟨t, h, P, R⟩
  refine cmpF_ct (o := fP) (v := 0) (by simp only [fP, hdr]; omega_using [sz]) (by decide)
    (fun a => fpOf (pRes E g a)) (fun a t h => h.base) (fun a t h => by obtain ⟨_, _, _, R⟩ := h; exact R.fp)
    (fun a => fpLt _) (stImm_ct (fun a t h => h.1.base fun _ _ h => h.base) _ _) ?_
  refine cmpF_ct (o := fP) (v := 1) (by simp only [fP, hdr]; omega_using [sz]) (by decide)
    (fun a => fpOf (pRes E g a)) (fun a t h => h.1.base fun _ _ h => h.base)
    (fun a t h => by obtain ⟨u, ⟨s₀, -, -, R⟩, m, -⟩ := h.1.elim; rw [m]; exact R.fp) (fun a => fpLt _)
    ?_ (RelCT.block_nil fun _ _ _ => trivial)
  -- The window.
  refine (show RelCT isa (Both (APg E g)) _ _ from ?_)
  obtain apg_u : ∀ a t, APg E g a t → Base E t ∧
      t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (pUsed E g a) ∧ pUsed E g a ≤ E.witLen := by
    intro a t h
    obtain ⟨C₂, h1⟩ := h
    obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
    obtain ⟨t₁, ⟨s, _, P, R⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
    obtain B : Base E t := P.base.regs (m₂.trans m₁) (e₂.trans e₁) (p₂.trans p₁) (r₂.trans r₁) (w₂.trans w₁)
      (y₂.trans y₁)
    obtain wl : E.witT.length = E.witLen := by rw [← B.wit, VG.Proof.Bignum.bytesAt_length]
    refine ⟨B, ?_, Nat.sub_le _ _⟩
    show t.mem.readW _ 32 = BitVec.ofNat 32 (E.witLen - (pRest (pRes E g a)).length)
    generalize pRes E g a = R' at R h1 ⊢
    rcases R' with _ | ⟨_ | p, rest⟩
    · simp [fpOf] at h1
    · simp [fpOf] at h1
    obtain ⟨_, _, _, _, ⟨u, hu, fu, du⟩, _⟩ := R
    have : E.witLen - rest.length = u := by rw [← du, List.length_drop, wl]; omega_using [hu]
    rw [m₂, m₁]
    simp only [pRest, this]
    exact fu
  refine RelCT.seq (both_post (Ψ := AW E g) ?_ fun a t h => ?_) ?_
  · unfold Geo.gWindow
    refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, APg E g a s ∧ WinPost E g (pUsed E g a) s t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (apg_u a t h).1) ?_)
      fun a t h => WP.mono (gWinBlock_ok G v (apg_u a t h).1 (apg_u a t h).2.1 (apg_u a t h).2.2)
        fun u W => ⟨t, h, W⟩) ?_
    · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)
    · refine both_ite (fun a => decide (E.witLen - pUsed E g a < 128 * g.pLen))
        (fun a t h => by obtain ⟨_, _, W⟩ := h; exact W.cf) (RelCT.block_nil fun _ _ _ => trivial) ?_
      exact stImm_ct (fun a t h => by obtain ⟨_, _, W⟩ := h.1; exact W.base) _ _
  · exact WP.mono (gWindow_ok G v hp (apg_u a t h).1 (apg_u a t h).2.1 (apg_u a t h).2.2)
      fun u ⟨B, C, rd, wr, sy, hs, hl⟩ => ⟨t, h, B, C, rd, wr, sy, hs, hl⟩
  -- g.
  refine RelCT.seq (both_post (Ψ := AG E g) ?_ fun a t h => ?_) ?_
  · refine both_exists fun a => ?_
    exact (gPart_ct G (v.window (Nat.sub_le _ _)) hp).mono
      (fun s t h => ⟨_, aw_gpIn G v h.1, aw_gpIn G v h.2⟩) fun _ _ h => h
  · have I := aw_gpIn G v h
    exact WP.mono (gPart_ok G (v.window (Nat.sub_le _ _)) hp I.base I.hsW I.hsLenW I.hx' I.hone I.hpm1 I.hP I.hE
      I.hxl I.hp1 I.hodd I.hplt) fun u ⟨K, R, _⟩ => ⟨t, h, K, R⟩
  -- The candidates read.
  refine RelCT.seq (both_post (Ψ := AU E g)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.base) (tcheck _ _ (by decide +kernel)))
    fun a t h => WP.mono (gUsed_wp h.base.scr sz) fun u ⟨x, e, p_, r, w, y⟩ => ⟨t, h, x, e, p_, r, w, y⟩) ?_
  -- The domain check, or whether the window was short.
  refine cmpF_ct (o := fG) (v := 1) (by simp only [fG, hdr]; omega_using [sz]) (by decide)
    (fun a => fgOf (gRes E g a)) (fun a t h => h.base v) (fun a t h => ?_)
    (fun a => fgLt _) ?_ ?_
  · obtain ⟨t₇, ⟨_, _, _, R⟩, ⟨x, m⟩, -⟩ := h
    rw [m, word_store_other v _ (by simp only [fG, hdr]; omega_using [sz]) (by simp only [fUsed, hdr]; omega_using [sz])
      (by simp only [fUsed, fG, hdr]; omega_using [])]
    exact R.fg
  · exact both_map _ (fun a t h => ag_cIn G v h) (check_ct G v hp hq)
  · unfold Geo.gShort
    refine cmpFb_ct (o := fHsLen) (v := 128 * g.pLen) (by simp only [fHsLen, hdr]; omega_using [sz]) (by omega_using [bd])
      (fun a => (gEnv E g a).hsLen) (fun a t h => h.1.base fun _ _ h => h.base v)
      (fun a t h => by obtain ⟨u, hU, m, -⟩ := h.1.elim; rw [m]; exact hU.len G v) (fun a => ?_)
      (stImm_ct (fun a t h => h.1.base fun _ _ h => h.1.base fun _ _ h => h.base v) _ _)
      (RelCT.block_nil fun _ _ _ => trivial)
    simp only [Env.window, hp]
    omega_using [bd]

end VG.Proof.Dsa.X86.Generation

end

end

/-! # Two runs of the search over the seeds leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- Before the search: `state[0]` seeds left, the cursor at 0. -/
def SIn (E : Env) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.k0 ∧
    s.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 0 ∧
    s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0

/-- `fStatus` after the seed at the cursor. -/
def statusOf : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Nat
  | none => 2
  | some (none, _) => 0
  | some (some _, _) => 1

theorem ARes.status {E : Env} {g : Geo} {m : Mem} {R : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)}
    (h : ARes E g m R) : m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 (statusOf R) := by
  rcases R with _ | ⟨_ | _, _⟩
  · exact h
  · exact h.1
  · exact h.1

theorem search_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (_ : Unit) => SIn E) g.search fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.witLen32
  have bd := G.bounds
  let I : Nat → State → State → Prop := fun n => Both fun (a : Nat × Nat) t =>
    (∃ σ, SLoop E g σ a.1 a.2 t) ∧ a.1 = n
  have L₀ : ∀ s, SIn E s → SLoop E g s E.k0 0 s := fun s ⟨B, hL, hC, hst⟩ =>
    ⟨⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩, hL, hC, hst, Nat.zero_le _, v.k0le,
      by simp [Spec.Entropy.Result.consume], rfl⟩
  unfold Geo.search
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) E.k0).mono
    (fun s t ⟨_, h₁, h₂⟩ => ⟨(E.k0, 0), ⟨⟨s, L₀ s h₁⟩, rfl⟩, ⟨t, L₀ t h₂⟩, rfl⟩) fun _ _ h => h
  refine both_exists fun a => ?_
  obtain ⟨j, c⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.2, by obtain ⟨⟨σ, L⟩, _⟩ := h.1; exact L.hj,
    by obtain ⟨⟨σ, L⟩, _⟩ := h.1; exact L.hc⟩ : j = n ∧ j ≤ Spec.Dsa.parameterSeeds ∧ c ≤ E.witLen))
    fun ⟨hjn, hjs, hcw⟩ => ?_
  let J : State → Prop := fun t => (∃ σ, SLoop E g σ j c t) ∧ j = n
  have hbJ : ∀ (_ : Unit) t, J t → Base E t := fun _ t h => by
    obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.keep.base
  have jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hjs; omega_using [hjs]
  have pins : ∀ {Φ : Unit → State → Prop}, (∀ u t, Φ u t → Base E t) →
      ∀ s t, Both Φ s t → VG.X86.Taint.Agree (τr [.esp, .edi]) s t := fun hb s t ⟨u, h₁, h₂⟩ =>
    agree_regs fun r hr => (base_pins (hb u s h₁) r hr).trans (base_pins (hb u t h₂) r hr).symm
  have tr : RelCT isa (fun s t => J s ∧ J t)
      (seqs [.block (cmpF fSeedLeft 0),
        .ite .e (.block (stImm fStatus 3))
          (seqs [.block (Geo.avail ++ ([.alu .cmp .eax (.imm (BitVec.ofNat 32 g.qLen))] : List Instr)),
            .ite .b (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .e (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)]) fun _ _ => True := by
    refine (show RelCT isa (Both fun (_ : Unit) t => J t) _ _ from ?_).mono (fun s t h => ⟨(), h.1, h.2⟩)
      fun _ _ h => h
    simp only [seqs]
    refine RelCT.assoc (RelCT.seq (cmpF_ct (o := fSeedLeft) (v := 0) (by simp only [fSeedLeft, hdr]; omega_using [sz])
      (by decide) (fun _ => j) hbJ (fun _ t h => by obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.left)
      (fun _ => jl) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ ?_)
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    · -- None left.
      exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun _ t h => h.1.base hbJ) fun _ _ h => h
    -- The octets left.
    let Φ₁ : Unit → State → Prop := fun _ t => CmpAfter (fun (_ : Unit) t => J t) () t ∧ decide (j = 0) = false
    have b₁ : ∀ u t, Φ₁ u t → Base E t := fun _ t h => h.1.base hbJ
    have c₁ : ∀ u t, Φ₁ u t → t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c := fun _ t h => by
      obtain ⟨s, ⟨⟨σ, L⟩, _⟩, m, -⟩ := h.1.elim; rw [m]; exact L.cur
    let Ψ₁ : Unit → State → Prop := fun _ t => ∃ s, Φ₁ () s ∧ Base E t ∧ t.mem = s.mem ∧
      isa.eval .b t = some (decide (E.witLen - c < g.qLen))
    refine RelCT.seq (both_post (Ψ := Ψ₁) (both_agree [.esp, .edi] (fun _ => baseVal E)
      (fun u t h => base_pins (b₁ u t h)) ?_) fun u t h => ?_) ?_
    · rcases G.lengths with ⟨_, h₂⟩ | ⟨_, h₂⟩ | ⟨_, h₂⟩ <;> rw [h₂] <;> exact tcheck _ _ (by decide +kernel)
    · rw [← List.append_nil (Geo.avail ++ _), List.append_assoc]
      exact availCmp_ok v (b₁ u t h) (c₁ u t h) hcw (w := g.qLen) (by omega_using [bd])
        fun t' g' m' rd' wr' sy' _ cf' => WP.block_nil ⟨t, h, (b₁ u t h).regs m' (g' _ (by decide) (by decide))
          (g' _ (by decide) (by decide)) rd' wr' sy', m', cf'⟩
    have b₂ : ∀ u t, Ψ₁ u t → Base E t := fun _ t h => by obtain ⟨_, _, B, _⟩ := h; exact B
    refine both_ite (fun _ => decide (E.witLen - c < g.qLen)) (fun u t h => by obtain ⟨_, _, _, _, e⟩ := h; exact e)
      ((tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => b₂ u t h.1) fun _ _ h => h) ?_
    -- A seed.
    by_cases short : E.witLen - c < g.qLen
    · exact relct_of_fact (P := False) (fun s t ⟨_, h, _⟩ => by simp [short] at h) fun f => f.elim
    have hcq : c + E.qLen ≤ E.witLen := by omega_arith
    let Φ₂ : Unit → State → Prop := fun u t => Ψ₁ u t ∧ decide (E.witLen - c < g.qLen) = false
    have hS₂ : ∀ u t, Φ₂ u t → t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c ∧
        t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := fun _ t h => by
      obtain ⟨⟨s, h₁, _, m, _⟩, _⟩ := h
      obtain ⟨s', ⟨⟨σ, L⟩, _⟩, m', -⟩ := h₁.1.elim
      exact ⟨by rw [m, m']; exact L.cur, by rw [m, m']; exact L.status⟩
    let Ψ₂ : Unit → State → Prop := fun _ t => AIn (E.atSeed c) (0, c + E.qLen) t
    have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
        (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega_using [sz, h₁])
        (by simp only [sState] at h₂; omega_using [sz, h₂]) h y
    refine RelCT.seq (both_post (Ψ := Ψ₂) (both_agree [.esp, .edi] (fun _ => baseVal E)
      (fun u t h => base_pins (b₂ u t h.1)) ?_) fun u t h => ?_) ?_
    · unfold Geo.seedStart
      rcases G.lengths with ⟨_, h₂⟩ | ⟨_, h₂⟩ | ⟨_, h₂⟩ <;> rw [h₂] <;> exact tcheck _ _ (by decide +kernel)
    · obtain ⟨hc, hst⟩ := hS₂ u t h
      have B := b₂ u t h.1
      refine WP.mono (seedStart_ok v hq B hc) fun t₃ ⟨m₃, g₃, rd₃, wr₃, sy₃⟩ => ?_
      have C₃ : E.Chg [(fSeed, 4), (fUsed, 4)] t.mem t₃.mem := by
        rw [m₃]
        exact ((Env.Chg.refl _ _).store (d := fSeed) (n := 4) (by simp) (by decide) _).store (d := fUsed)
          (n := 4) (by simp) (by decide) _
      have B₃ := B.keep v C₃ (fun o ho => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fSeed, fUsed, fOut, fUsedP, fWitLen, hdr] <;> omega_using [sz])
        (g₃ _ (by decide) (by decide)) (g₃ _ (by decide) (by decide)) rd₃ wr₃ sy₃
      refine ⟨⟨B₃.toSeed c, by simp only [Env.atSeed]; omega_using [], ?_, ?_, hcq⟩, ?_⟩
      · show t₃.mem.readW (off E.base fSeed) 32 =
          ((E.atSeed c).seeds + BitVec.ofNat 64 (0 * (E.atSeed c).qLen)).setWidth 32
        rw [m₃, ws _ (by simp only [fSeed, sState, hdr]; omega_using []) (by simp only [fUsed, sState, hdr]; omega_using [])
          (by simp only [fSeed, fUsed, hdr]; omega_using []), Mem.readW_writeW_self32, Nat.zero_mul, BitVec.add_zero]
        rfl
      · show t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (c + E.qLen)
        rw [m₃, Mem.readW_writeW_self32]
      · show t₃.mem.readW (off E.base fStatus) 32 = _
        rw [m₃, ws _ (by simp only [fStatus, sState, hdr]; omega_using []) (by simp only [fUsed, sState, hdr]; omega_using [])
          (by simp only [fStatus, fUsed, hdr]; omega_using []), ws _ (by simp only [fStatus, sState, hdr]; omega_using [])
          (by simp only [fSeed, sState, hdr]; omega_using []) (by simp only [fStatus, fSeed, hdr]; omega_using []), hst]
    -- The attempt.
    have v' := v.atSeed hcq
    let Ψ₃ : Unit → State → Prop := fun _ t => ∃ s, Ψ₂ () s ∧ AKeep (E.atSeed c) g s t ∧
      ARes (E.atSeed c) g t.mem (sR E c)
    have b₃ : ∀ u t, Ψ₃ u t → Base E t := fun _ t h => by obtain ⟨_, _, K, _⟩ := h; exact K.base.ofSeed
    have eR : refillAttempt g.pLen g.qLen (chunk (E.atSeed c) 0) ((E.atSeed c).witT.drop (c + E.qLen)) = sR E c := by
      simp only [chunk, Env.seedT, Env.atSeed, sR, hp, hq, Nat.zero_mul, List.drop_zero, List.take_take, Nat.min_self]
    refine RelCT.seq (both_post (Ψ := Ψ₃) (both_map (fun _ => (0, c + E.qLen)) (fun _ t h => h)
      (attempt_ct G v' hp hq)) fun u t h => ?_) ?_
    · exact WP.mono (attempt_ok G v' hp hq h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2)
        fun t' ⟨K, R⟩ => ⟨t, h, K, by rw [← eR]; exact R⟩
    refine cmpF_ct (o := fStatus) (v := 0) (by simp only [fStatus, hdr]; omega_using [sz]) (by decide)
      (fun _ => statusOf (sR E c)) b₃ (fun _ t h => by obtain ⟨_, _, _, R⟩ := h; exact R.status)
      (fun _ => by rcases sR E c with _ | ⟨_ | _, _⟩ <;> simp [statusOf]) ?_ ?_
    · exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => h.1.base b₃) fun _ _ h => h
    · exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => h.1.base b₃) fun _ _ h => h
  refine (tr.wpDep (F := fun _ t' => ∃ σ, isa.eval .e t' = some (sStep E j c).isSome ∧
      (∀ j' c', sStep E j c = some (j', c') → j' < j ∧ SLoop E g σ j' c' t'))
    fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, L⟩, _⟩ := h.1
    exact WP.mono (sBody_ok G v hp hq L) fun t' ⟨z, _, h'⟩ => ⟨σ, z, h'⟩
  · obtain ⟨⟨σ, L⟩, _⟩ := h.2
    exact WP.mono (sBody_ok G v hp hq L) fun t' ⟨z, _, h'⟩ => ⟨σ, z, h'⟩
  obtain ⟨_, _, _, _, ⟨σ₁, z₁, c₁⟩, ⟨σ₂, z₂, c₂⟩⟩ := H
  refine ⟨z₁.trans z₂.symm, fun _ => trivial, fun ht => ?_⟩
  rw [z₁] at ht
  rcases hs : sStep E j c with _ | ⟨j', c'⟩
  · rw [hs] at ht; simp at ht
  obtain ⟨hj, L₁⟩ := c₁ j' c' hs
  obtain ⟨_, L₂⟩ := c₂ j' c' hs
  exact ⟨j', by omega_arith, (j', c'), ⟨⟨σ₁, L₁⟩, rfl⟩, ⟨σ₂, L₂⟩, rfl⟩

end VG.Proof.Dsa.X86.Generation
