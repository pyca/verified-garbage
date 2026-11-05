module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTop
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
import VerifiedGarbage.Proof.Ffdh.X86.Ops
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
meta import VerifiedGarbage.Proof.Ffdh.X86.Ops
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTop
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.ScanTiming
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
meta import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key_precompute` on i686 in time that depends on the domain only

The contract releases the domain. The recognition's scan branches on the
domain and the table (`VettedValidation.scan_ct`); the width's loop and
branches, and the table's squares, are related by their public counts; the
rest the taint analysis checks from the arguments.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Ffdh.X86 (tbOff ldOff tOff)

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {sp : BitVec 32}

/-! ## The recognition -/

/-- A run the recognition starts from, with the public domain `D` and the table at `T`. -/
structure RP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (dlen : Nat) (D : List Byte) (T : BitVec 32) (x : State) : Prop where
  inp : In Ex base bytes len args x
  geo : DomGeo args base bytes len dlen x.rd x.wr
  b40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  sym : x.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T
  tfit : T.toNat + 17744 ≤ 2 ^ 32
  tread : InRegions (x.rd ++ x.wr) (byteAddr T) 17744
  tbytes : Spec.Rsa.bytesAt x.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes
  tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩
  t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below sp 96)
  esp : x.gpr .esp = sp
  dom : Spec.Rsa.bytesAt x.mem (byteAddr (args 2)) dlen = D

theorem recognize_trace {dlen : Nat} {D : List Byte} {T : BitVec 32} :
    RelCT isa (Both (RP Ex base bytes len args sp dlen D T)) recognize fun _ _ => True := by
  unfold recognize
  -- `ebx := edi`.
  let PA : State → Prop := fun x => ∃ s, RP Ex base bytes len args sp dlen D T s ∧ Upd s x .ebx (s.gpr .edi)
  have A : RelCT isa (Both (RP Ex base bytes len args sp dlen D T)) (.block [.mov .ebx (.reg .edi)]) (Both PA) :=
    relCT_both (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block []) (by rfl))
      fun x hx => wp_movS rfl fun x' U _ => WP.block_nil ⟨x, hx, U⟩
  -- The table's address.
  let PB : State → Prop := fun x => ∃ s y, RP Ex base bytes len args sp dlen D T s ∧ Upd s y .ebx (s.gpr .edi) ∧
    SymAddrPost VG.Impl.Ffdh.X86.VettedValidation.tableSym y x
  have low : ∀ {x : State}, PA x → 4 ≤ (x.gpr .esp).toNat := fun ⟨s, P, U⟩ => by
    rw [U.other _ (by decide)]; have := P.inp.room.low; omega
  have B : RelCT isa (Both PA) VG.Impl.Ffdh.X86.VettedValidation.tableAddress (Both PB) := by
    refine relCT_both (fun x y tx ty x' y' h ex ey => ?_) fun x hx => ?_
    · obtain ⟨⟨s₁, P₁, U₁⟩, ⟨s₂, P₂, U₂⟩⟩ := h
      rw [symFrame_trace (low ⟨s₁, P₁, U₁⟩) ex, symFrame_trace (low ⟨s₂, P₂, U₂⟩) ey, U₁.other _ (by decide),
        U₂.other _ (by decide), P₁.esp, P₂.esp]
      exact ⟨rfl, trivial⟩
    · obtain ⟨s, P, U⟩ := hx
      exact WP.mono (symFrame_ok _ x (low ⟨s, P, U⟩)) fun x' R => ⟨s, x, P, U, R⟩
  -- To the header.
  let PC : State → Prop := fun x => ∃ s, RP Ex base bytes len args sp dlen D T s ∧ RH Ex base bytes len args T s x
  have C : RelCT isa (Both PB) (.block VG.Impl.Ffdh.X86.VettedValidation.saveTable) (Both PC) := by
    refine relCT_both (RelCT.taint (A := taint) (τr [.ebx]) (fun x y h => agree_regs fun r hr => ?_)
      (hc := .block []) (by rfl)) fun x ⟨s, y, P, U, R⟩ => WP.mono (saveTable_ok P.inp U R) fun x' M =>
        ⟨s, P, rh_of P.inp P.sym U R M⟩
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨⟨s₁, y₁, P₁, U₁, R₁⟩, ⟨s₂, y₂, P₂, U₂, R₂⟩⟩ := h
    rw [R₁.gpr _ (by decide), R₂.gpr _ (by decide), U₁.gpr, U₂.gpr, ← P₁.inp.edi_eq, ← P₂.inp.edi_eq]
  -- The scan, in its frame.
  have fit : 0 + (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, VG.Impl.Ffdh.VettedGroups.tableBytes] using
      Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  have valid : ∀ g ∈ VG.Impl.Ffdh.VettedGroups.groups, g.len < 2 ^ 32 := by
    intro g hg
    simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let SC : State → Prop := fun w =>
    VettedValidation.Context (args 16) (args 2) (sp - BitVec.ofNat 32 16) T len D w ∧
      VettedValidation.TableAt (byteAddr T + BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups w
  have scanArgsCT : RelCT isa (fun a b => ∃ s₁ s₂, Both PC s₁ s₂ ∧ a = allocFrame 16 s₁ ∧ b = allocFrame 16 s₂)
      (.block scanArgs) (Both SC) := by
    refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
      (by rfl)).wp (F₁ := SC) (F₂ := SC) fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain rfl := List.mem_singleton.mp hr
      obtain ⟨s₁, s₂, ⟨⟨x₁, P₁, H₁⟩, ⟨x₂, P₂, H₂⟩⟩, rfl, rfl⟩ := h
      rw [allocFrame_esp, allocFrame_esp, H₁.sp, H₂.sp, P₁.esp, P₂.esp]
    · obtain ⟨s₁, s₂, ⟨⟨x₁, P₁, H₁⟩, ⟨x₂, P₂, H₂⟩⟩, rfl, rfl⟩ := h
      have w : ∀ {x s : State}, RP Ex base bytes len args sp dlen D T x → RH Ex base bytes len args T x s →
          WP isa (.block scanArgs) (allocFrame 16 s) SC := fun {x s} P H => by
        have e := P.esp
        refine WP.mono (scanCtx_ok P.inp P.geo (by rw [e]; exact P.b40) P.tfit P.tread P.tbytes P.tws
          (by rw [e]; exact P.t40) H) fun w ⟨Cw, TA, _⟩ => ?_
        rw [e, P.dom] at Cw
        exact ⟨Cw, TA⟩
      exact ⟨w P₁ H₁, w P₂ H₂⟩
  have scanCT : RelCT isa (Both SC) (VG.Impl.Ffdh.X86.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0)
      fun _ _ => True :=
    VettedValidation.scan_ct (base := args 16) (src := args 2) (sp := sp - BitVec.ofNat 32 16) (table := T)
      (k := len) (dom := D) _ 0 fit valid
  let PD : State → Prop := fun t => ∃ s x, RP Ex base bytes len args sp dlen D T s ∧ RH Ex base bytes len args T s x ∧
    Keeps [.eax, .ecx, .edx, .esi, .edi, .ebp] x t
  have Dct : RelCT isa (Both PC) (.frame (.alloc 16) (.seq (.block scanArgs)
      (VG.Impl.Ffdh.X86.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0)) (.free 16)) (Both PD) :=
    relCT_both (RelCT.frameAlloc (R := fun _ _ => True) (VG.RelCT.seq scanArgsCT scanCT)) fun x ⟨s, P, H⟩ => by
      have e := P.esp
      exact WP.mono (recScan_ok P.inp P.geo (by rw [e]; exact P.b40) P.tfit P.tread P.tbytes P.tws
        (by rw [e]; exact P.t40) H) fun t ⟨_, _, _, _, _, K⟩ => ⟨s, x, P, H, K⟩
  -- `edi` back, the width to the header.
  have E : RelCT isa (Both PD) (.block [.mov .edi (.reg .ebx), .store (sc recOff) .eax]) fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebx]) (fun x y h => agree_regs fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      obtain ⟨⟨s₁, x₁, P₁, H₁, K₁⟩, ⟨s₂, x₂, P₂, H₂, K₂⟩⟩ := h
      rw [K₁.1 _ (by decide), K₂.1 _ (by decide), H₁.ebx, H₂.ebx, ← P₁.inp.edi_eq, ← P₂.inp.edi_eq])
      (hc := .block []) (by rfl)
  exact VG.RelCT.seq A (VG.RelCT.seq B (VG.RelCT.seq C (VG.RelCT.seq Dct E)))

/-! ## The table -/

/-- `f 0`, …, `f (n − 1)` in order, related at each. -/
theorem relCT_seqs_range (f : Nat → Prog isa) (I : Nat → State → Prop) :
    ∀ (n a : Nat), (∀ e, a ≤ e → e < a + n → RelCT isa (Both (I e)) (f e) (Both (I (e + 1)))) →
      RelCT isa (Both (I a)) (seqs ((List.range' a n).map f)) (Both (I (a + n)))
  | 0, a, _ => RelCT.block_nil fun _ _ h => h
  | n + 1, a, h => by
    rw [List.range'_succ, List.map_cons, seqs_cons]
    refine VG.RelCT.seq (h a (by omega) (by omega)) ?_
    have := relCT_seqs_range f I n (a + 1) fun e h₁ h₂ => h e (by omega) (by omega)
    rwa [show a + 1 + n = a + (n + 1) by omega] at this

section
variable {P G bits : Nat}

/-- A run of the table from `s₀`, its first `n` entries written, and `X`. -/
def TR (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P G bits n : Nat) (X : State → Prop) (u : State) : Prop :=
  ∃ s₀, ArgsOk s₀ ∧ s₀.gpr .esp = sp ∧ TS Ex base bytes len args P G bits s₀ n u ∧ X u

theorem TR.run {n : Nat} {X : State → Prop} {u : State} (h : TR Ex base bytes len args sp P G bits n X u) :
    Run Ex base bytes len args sp u :=
  let ⟨_, A, e, S, _⟩ := h
  ⟨S.inp, A.keep S.keeps, S.esp.trans e⟩

/-- A stage the taint analysis checks, which keeps the table. -/
theorem tr_lift {c : Prog isa} (hc : ACheck c) {n n' : Nat} {X X' : State → Prop}
    (hw : ∀ s₀ u, TS Ex base bytes len args P G bits s₀ n u → X u →
      WP isa c u fun t => TS Ex base bytes len args P G bits s₀ n' t ∧ X' t) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits n X)) c (Both (TR Ex base bytes len args sp P G bits n' X')) :=
  taint_both (fun _ _ h₁ h₂ => h₁.run.agree h₂.run) _ hc fun u ⟨s₀, A, e, S, x⟩ =>
    WP.mono (hw s₀ u S x) fun _ ⟨S', x'⟩ => ⟨s₀, A, e, S', x'⟩

/-- A product, which keeps the table. -/
theorem tr_mul {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hT : MulCheck .wide o a b) {n : Nat} {X X' : State → Prop}
    (hB : ∀ u, X u → sv u.mem base len .wide b < P)
    (hw : ∀ s₀ u, TS Ex base bytes len args P G bits s₀ n u → X u →
      WP isa (mul .wide o a b) u fun t => TS Ex base bytes len args P G bits s₀ n t ∧ X' t) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits n X)) (mul .wide o a b)
      (Both (TR Ex base bytes len args sp P G bits n X')) :=
  mul_both sp ho3 ho ha3 ha hb3 hb hT (fun u h => let ⟨_, _, _, S, x⟩ := h
      ⟨⟨P, S.ctx, hB u x⟩, h.run.2.1, h.run.2.2⟩)
    fun u ⟨s₀, A, e, S, x⟩ => WP.mono (hw s₀ u S x) fun _ ⟨S', x'⟩ => ⟨s₀, A, e, S', x'⟩

/-- `τA`, and `eax` public. -/
def τAx : VG.X86.Taint.T := { regs := .ofList [.edi, .esp, .eax], flags := false, argLen := 76 }

theorem τAx_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τAx s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeAx {s₁ s₂ : State} (h₁ : In Ex base bytes len args s₁) (h₂ : In Ex base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) (ea : s₁.gpr .eax = s₂.gpr .eax) :
    VG.X86.Taint.Agree τAx s₁ s₂ := by
  have G := agreeA h₁ h₂ A₁ A₂ sp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τAx_wf A₁, τAx_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => G.argMem k h4 hk⟩
  simp only [τAx, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact G.rf.1 _ (by simp [τA])
  · exact sp
  · exact ea

/-- Code the taint analysis checks with `eax` public. -/
abbrev XACheck (p : Prog isa) : Prop := (VG.Taint.check taint τAx p (VG.Taint.hintOf taint τAx p)).isSome = true

/-- A block, its first part then its rest, before `c`. -/
theorem relCT_seq_block_append {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ c₁ =>
    cases e₂ with
    | seq b₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨x₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨x₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-- `eax :=` an index, in both runs. -/
theorem idx_trace {P : State → Prop} (k : Nat) :
    RelCT isa (Both P) (.block (rowImm k)) fun x y => ∃ x₀ y₀, P x₀ ∧ P y₀ ∧
      Upd x₀ x .eax (BitVec.ofNat 32 k) ∧ Upd y₀ y .eax (BitVec.ofNat 32 k) := by
  refine ((RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    (by rfl)).wp (F₁ := fun x => ∃ x₀, P x₀ ∧ Upd x₀ x .eax (BitVec.ofNat 32 k))
      (F₂ := fun x => ∃ x₀, P x₀ ∧ Upd x₀ x .eax (BitVec.ofNat 32 k)) fun x y h =>
      ⟨wp_movS rfl fun x' U _ => WP.block_nil ⟨x, h.1, U⟩, wp_movS rfl fun y' U _ => WP.block_nil ⟨y, h.2, U⟩⟩).mono
    (fun _ _ h => h) fun _ _ ⟨_, ⟨x₀, P₁, U₁⟩, ⟨y₀, P₂, U₂⟩⟩ => ⟨x₀, y₀, P₁, P₂, U₁, U₂⟩

/-- The rest of a row's copy, after its index, checked with `eax` public. -/
theorem rowRest_trace {P : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x) {k : Nat}
    {c : Prog isa} (hc : XACheck c) :
    RelCT isa (fun x y => ∃ x₀ y₀, P x₀ ∧ P y₀ ∧ Upd x₀ x .eax (BitVec.ofNat 32 k) ∧
      Upd y₀ y .eax (BitVec.ofNat 32 k)) c fun _ _ => True :=
  RelCT.taint (A := taint) τAx (fun x y ⟨x₀, y₀, P₁, P₂, U₁, U₂⟩ => by
    have R₁ := hP _ P₁
    have R₂ := hP _ P₂
    exact agreeAx (R₁.1.regs U₁.keeps U₁.mem) (R₂.1.regs U₂.keeps U₂.mem) (R₁.2.1.keep U₁.keeps)
      (R₂.2.1.keep U₂.keeps) (by rw [U₁.other _ (by decide), U₂.other _ (by decide), R₁.2.2, R₂.2.2])
      (by rw [U₁.gpr, U₂.gpr])) hc

/-- A slot to a row. -/
theorem storeRow_trace {P F : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x) (k a : Nat)
    (hc : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
      (ptrTo (.slot .wide a) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))))
    (hw : ∀ x, P x → WP isa (storeRow (rowImm k) a) x F) : RelCT isa (Both P) (storeRow (rowImm k) a) (Both F) := by
  refine relCT_both ?_ hw
  unfold storeRow
  simp only [List.append_assoc]
  exact relCT_seq_block_append (VG.RelCT.seq (idx_trace k) (rowRest_trace hP hc))

/-- A row to a slot. -/
theorem loadRow_trace {P F : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x) (k a : Nat)
    (hc : XACheck (.seq (.block (rowAt .ebp ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
      (ptrTo (.slot .wide a) .ebx .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))))
    (hw : ∀ x, P x → WP isa (loadRow (rowImm k) a) x F) : RelCT isa (Both P) (loadRow (rowImm k) a) (Both F) := by
  refine relCT_both ?_ hw
  unfold loadRow
  simp only [List.append_assoc]
  exact relCT_seq_block_append (VG.RelCT.seq (idx_trace k) (rowRest_trace hP hc))

theorem store9_check : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 9) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem store4_check : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 4) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem store6_check : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 6) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem store7_check : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 7) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem store8_check : XACheck (.seq (.block (rowAt .ebx ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 8) .ebp .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem load5_check : XACheck (.seq (.block (rowAt .ebp ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] ++
    (ptrTo (.slot .wide 5) .ebx .edx ++ cntTo (one .wide) .edi)))) (.seq selectLoop (.block restoreEdi))) := by
  dsimp only [XACheck]; taint_decide

theorem m754_check : MulCheck .wide 7 5 4 := by dsimp only [MulCheck]; taint_decide
theorem m777_check : MulCheck .wide 7 7 7 := by dsimp only [MulCheck]; taint_decide
theorem m857_check : MulCheck .wide 8 5 7 := by dsimp only [MulCheck]; taint_decide
theorem copy105_check : ACheck (copy (.slot .wide 10) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem sqHead_check : ACheck (.block [.mov .eax (.mem (sc rowsOff)), .store (sc iOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

/-- Entry 0, Montgomery one, and entry 1, `g R mod P`. -/
theorem initial_trace (hP1 : 1 < P) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits 0 fun u => sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧ sv u.mem base len .wide 10 = G)) (seqs initial)
      (Both (TR Ex base bytes len args sp P G bits 2 fun u =>
        sv u.mem base len .wide 7 = entV len P G bits (2 ^ 0))) := by
  have hc := winChecks .wide
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  have e0 : Spec.Rsa.FixedBaseComb.exponent bits 0 = 0 := VG.Proof.Rsa.FixedBaseComb.exponent_zero bits
  have e1 : Spec.Rsa.FixedBaseComb.exponent bits 1 = 1 := by
    simpa using VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits 0 (by decide)
  show RelCT isa _ (.seq (mul .wide 6 4 3) (.seq (storeRow (rowImm 2) 6) (.seq (copy (.slot .wide 10) (.slot .wide 5)
    (one .wide)) (.seq (mul .wide 7 5 4) (.seq (storeRow (rowImm 3) 7) (.block [])))))) _
  refine VG.RelCT.seq (tr_mul (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m643 (X' := fun u => sv u.mem base len .wide 6 = entV len P G bits 0 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧ sv u.mem base len .wide 10 = G)
    (fun u x => by rw [x.1]; exact hP1) fun s₀ u S ⟨h3, h4, h10⟩ => ?_) ?_
  · have cp := S.ctx.coprime
    refine WP.mono (S.mul (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [h3]; exact hP1)) fun t₁ ⟨S₁, L₁, V₁, K₁, _, H₁⟩ => ⟨S₁, ?_, ?_, ?_⟩
    · have v := VG.Proof.Bignum.mont_cancel cp (o := sv t₁.mem base len .wide 6) (c := 2 ^ (8 * bc len .wide))
        (by rw [V₁, h4, h3, Nat.mul_one, Nat.mod_mod, RR])
      rw [Nat.mod_eq_of_lt L₁] at v
      show _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits 0)
      rw [v, e0, enc, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hP1, Nat.one_mul]
    · rw [K₁ 4 (by decide) (by decide) (by decide)]; exact h4
    · rw [H₁ 10 (by decide) (by decide)]; exact h10
  refine VG.RelCT.seq (storeRow_trace (fun _ h => h.run) 2 6 store6_check
    (F := TR Ex base bytes len args sp P G bits 1 fun u => sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧
      sv u.mem base len .wide 10 = G) fun u ⟨s₀, A, e, S, x⟩ =>
    WP.mono (S.store (n := 0) (by decide) (a := 6) (by decide) x.1) fun t ⟨S₂, K₂, _⟩ =>
      ⟨s₀, A, e, S₂, by show sv _ _ _ _ _ = _; rw [K₂ 4 (by decide)]; exact x.2.1,
        by show sv _ _ _ _ _ = _; rw [K₂ 10 (by decide)]; exact x.2.2⟩) ?_
  refine VG.RelCT.seq (tr_lift copy105_check (X' := fun u => sv u.mem base len .wide 5 = G ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P) fun s₀ u S ⟨h4, h10⟩ =>
    WP.mono S.copy fun t ⟨S₃, V₃, K₃⟩ => ⟨S₃, by rw [V₃]; exact h10, by rw [K₃ 4 (by decide) (by decide)]; exact h4⟩) ?_
  refine VG.RelCT.seq (tr_mul (o := 7) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m754_check (X' := fun u => sv u.mem base len .wide 7 = entV len P G bits 1)
    (fun u x => by rw [x.2]; exact Nat.mod_lt _ (by omega)) fun s₀ u S ⟨g₃, r₃⟩ => ?_) ?_
  · have cp := S.ctx.coprime
    refine WP.mono (S.mul (o := 7) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [r₃]; exact Nat.mod_lt _ (by omega))) fun t₄ ⟨S₄, L₄, V₄, _, _, _⟩ => ⟨S₄, ?_⟩
    have v := VG.Proof.Bignum.mont_cancel cp (o := sv t₄.mem base len .wide 7) (c := G * 2 ^ (8 * bc len .wide))
      (by rw [V₄, g₃, r₃, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rw [Nat.mod_eq_of_lt L₄] at v
    show _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits 1)
    rw [v, e1, enc, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod]
  refine VG.RelCT.seq (storeRow_trace (fun _ h => h.run) 3 7 store7_check
    (F := TR Ex base bytes len args sp P G bits 2 fun u => sv u.mem base len .wide 7 = entV len P G bits (2 ^ 0))
    fun u ⟨s₀, A, e, S, x⟩ => WP.mono (S.store (n := 1) (by decide) (a := 7) (by decide) x) fun t ⟨S₅, K₅, _⟩ =>
      ⟨s₀, A, e, S₅, by show sv _ _ _ _ _ = _; rw [K₅ 7 (by decide)]; exact x⟩) ?_
  exact RelCT.block_nil fun _ _ h => h

end

end

end VG.Proof.Ffdh.X86.Cached
