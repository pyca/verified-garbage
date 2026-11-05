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
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
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

/-- Slot 7 to the power `2^rows`: the runs related square by square. -/
theorem squares_trace {n E : Nat} (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) (hP1 : 1 < P) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits n fun u => sv u.mem base len .wide 7 = enc len P G E))
      squares (Both (TR Ex base bytes len args sp P G bits n fun u =>
        sv u.mem base len .wide 7 = enc len P G (E * 2 ^ Spec.Rsa.FixedBaseComb.rows bits))) := by
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have bw := bc_eq_cwc len .wide
  unfold squares
  refine VG.RelCT.seq (tr_lift sqHead_check (n' := n) (X' := fun u => sv u.mem base len .wide 7 = enc len P G E ∧
      w32 u.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits) fun s₀ u S s7 => ?_) ?_
  · have bl := S.inp.bytes_lt
    have f7 := S.inp.slot_fit .wide (j := 7) (by decide)
    refine wp_movS (readW_ok S.inp (d := rowsOff) (by simp only [rowsOff]; omega) S.rows (by omega)) fun s₁ U₁ _ => ?_
    refine WP.mono (counter_store (S.inp.regs U₁.keeps U₁.mem) (d := iOff) (.inr rfl) .eax)
      fun s₂ ⟨I₂, O₂, W₂, K₂, _⟩ => ?_
    have S₁ := S.step (Step.regs S.inp U₁.mem U₁.keeps) (S.ctx.regs U₁.keeps U₁.mem) (by rw [U₁.mem])
    refine ⟨S₁.iword I₂ O₂ K₂, ?_, ?_⟩
    · simp only [sv]; rw [O₂.val32 (.inr (by simp only [iOff]; omega)) (by omega), U₁.mem]; exact s7
    · rw [W₂, U₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (relCT_countLoop (I := fun j => TR Ex base bytes len args sp P G bits n fun u =>
      sv u.mem base len .wide 7 = enc len P G (E * 2 ^ j) ∧
        w32 u.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits - j) hR fun j hj => ?_).mono
    (fun _ _ ⟨⟨s₀, A, e, S, v, w⟩, ⟨s₀', A', e', S', v', w'⟩⟩ =>
      ⟨⟨s₀, A, e, S, by rw [Nat.pow_zero, Nat.mul_one]; exact v, by rw [Nat.sub_zero]; exact w⟩,
        ⟨s₀', A', e', S', by rw [Nat.pow_zero, Nat.mul_one]; exact v', by rw [Nat.sub_zero]; exact w'⟩⟩)
    fun _ _ ⟨⟨s₀, A, e, S, v, _⟩, ⟨s₀', A', e', S', v', _⟩⟩ => ⟨⟨s₀, A, e, S, v⟩, ⟨s₀', A', e', S', v'⟩⟩
  refine VG.RelCT.seq (tr_mul (o := 7) (a := 7) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m777_check (X' := fun u => sv u.mem base len .wide 7 = enc len P G (E * 2 ^ (j + 1)) ∧
      w32 u.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits - j)
    (fun u x => by rw [x.1]; exact enc_lt (by omega)) fun s₀ u S ⟨V, W⟩ => ?_) ?_
  · have cp := S.ctx.coprime
    refine WP.mono (S.mul (o := 7) (a := 7) (b := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [V]; exact enc_lt (by omega))) fun t₁ ⟨S₁', L₁, V₁, _, H₁, _⟩ => ⟨S₁', ?_, ?_⟩
    · rw [VG.Proof.Rsa.FixedBaseComb.mont_square_encoded cp L₁ V V₁,
        show 2 * (E * 2 ^ j) = E * 2 ^ (j + 1) by rw [Nat.pow_succ]; ac_rfl]
    · rw [H₁ iOff (by simp only [iOff]; omega), W]
  refine taint_both (F := fun u => TR Ex base bytes len args sp P G bits n (fun u =>
      sv u.mem base len .wide 7 = enc len P G (E * 2 ^ (j + 1)) ∧
        w32 u.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits - (j + 1)) u ∧
      u.zf = some (decide (j + 1 = Spec.Rsa.FixedBaseComb.rows bits)))
    (fun _ _ h₁ h₂ => h₁.run.agree h₂.run) _ dec_check fun u ⟨s₀, A, e, S, V, W⟩ => ?_
  have bl := S.inp.bytes_lt
  have f7 := S.inp.slot_fit .wide (j := 7) (by decide)
  refine WP.mono (dec_ok S.inp (i := Spec.Rsa.FixedBaseComb.rows bits - j) (by omega) (by omega) W)
    fun t₂ ⟨I, O, W₂, K, z⟩ => ⟨⟨s₀, A, e, S.iword I O K, ?_, ?_⟩, ?_⟩
  · simp only [sv]; rw [O.val32 (.inr (by simp only [iOff]; omega)) (by omega)]; exact V
  · rw [W₂]; omega
  · rw [z]; congr 1; exact decide_eq_decide.mpr (by omega)

/-- Entry `d + j`, entry `j` times entry `d`. -/
theorem product_trace {k d j : Nat} (hk : k < 4) (hd : d = 2 ^ (k + 1)) (hj1 : 1 ≤ j) (hj : j < d) (hP1 : 1 < P) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits (d + j) fun u =>
      sv u.mem base len .wide 7 = entV len P G bits d)) (product d j)
      (Both (TR Ex base bytes len args sp P G bits (d + j + 1) fun u =>
        sv u.mem base len .wide 7 = entV len P G bits d)) := by
  have p16 : 2 ^ (k + 1) ≤ 16 := (Nat.pow_le_pow_right (show 0 < 2 by decide) (show k + 1 ≤ 4 by omega) :
    2 ^ (k + 1) ≤ 2 ^ 4)
  unfold product
  refine VG.RelCT.seq (loadRow_trace (fun _ h => h.run) (j + 2) 5 load5_check
    (F := TR Ex base bytes len args sp P G bits (d + j) fun u => sv u.mem base len .wide 7 = entV len P G bits d ∧
      sv u.mem base len .wide 5 = entV len P G bits j) fun u ⟨s₀, A, e, S, s7⟩ =>
    WP.mono (S.load (e := j) (a := 5) (by omega) (by decide) (by decide)) fun t₁ ⟨S₁, V₁, O₁⟩ =>
      ⟨s₀, A, e, S₁, by rw [slotKeep S.inp (a := 5) (b := 7) (by decide) (by decide) O₁]; exact s7, V₁⟩) ?_
  refine VG.RelCT.seq (tr_mul (o := 8) (a := 5) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m857_check (X' := fun u => sv u.mem base len .wide 7 = entV len P G bits d ∧
      sv u.mem base len .wide 8 = entV len P G bits (d + j))
    (fun u x => by rw [x.1]; exact enc_lt (by omega)) fun s₀ u S ⟨s7, V₁⟩ => ?_) ?_
  · have cp := S.ctx.coprime
    refine WP.mono (S.mul (o := 8) (a := 5) (b := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [s7]; exact enc_lt (by omega))) fun t₂ ⟨S₂, L₂, V₂, K₂, _, _⟩ => ⟨S₂, ?_, ?_⟩
    · rw [K₂ 7 (by decide) (by decide) (by decide)]; exact s7
    · have v₂ := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded cp L₂ V₁ s7 V₂
      have ex : Spec.Rsa.FixedBaseComb.exponent bits j + Spec.Rsa.FixedBaseComb.exponent bits d =
          Spec.Rsa.FixedBaseComb.exponent bits (d + j) := by
        subst hd
        rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits (k + 1) (by omega), Nat.add_comm (2 ^ (k + 1)) j,
          show j + 2 ^ (k + 1) = 2 ^ (k + 1) + j by omega,
          VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth bits (k + 1) j (by omega) hj]
      rw [ex] at v₂
      exact v₂
  exact storeRow_trace (fun _ h => h.run) (d + j + 2) 8 store8_check fun u ⟨s₀, A, e, S, s7, v8⟩ =>
    WP.mono (S.store (n := d + j) (by omega) (a := 8) (by decide) v8) fun t ⟨St, Kt, _⟩ =>
      ⟨s₀, A, e, St, by show sv _ _ _ _ _ = _; rw [Kt 7 (by decide)]; exact s7⟩

/-- The tooth `2^(k+1)`. -/
theorem column_trace {k : Nat} (hk : k < 4) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) (hP1 : 1 < P) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits (2 ^ (k + 1)) fun u =>
      sv u.mem base len .wide 7 = entV len P G bits (2 ^ k))) (column k)
      (Both (TR Ex base bytes len args sp P G bits (2 ^ (k + 2)) fun u =>
        sv u.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)))) := by
  have p16 : 2 ^ (k + 1) ≤ 16 := (Nat.pow_le_pow_right (show 0 < 2 by decide) (show k + 1 ≤ 4 by omega) :
    2 ^ (k + 1) ≤ 2 ^ 4)
  have p1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have pk2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have et : enc len P G (Spec.Rsa.FixedBaseComb.exponent bits (2 ^ k) * 2 ^ Spec.Rsa.FixedBaseComb.rows bits) =
      entV len P G bits (2 ^ (k + 1)) := by
    show _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits (2 ^ (k + 1)))
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k (by omega),
      VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits (k + 1) (by omega), ← Nat.pow_add, Nat.succ_mul]
  unfold column
  have sq : RelCT isa (Both (TR Ex base bytes len args sp P G bits (2 ^ (k + 1)) fun u =>
      sv u.mem base len .wide 7 = entV len P G bits (2 ^ k))) squares
      (Both (TR Ex base bytes len args sp P G bits (2 ^ (k + 1)) fun u =>
        sv u.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)))) :=
    (squares_trace (n := 2 ^ (k + 1)) (E := Spec.Rsa.FixedBaseComb.exponent bits (2 ^ k)) hR hR' hP1).mono
      (fun _ _ h => h) fun _ _ ⟨⟨s₀, A, e, S, v⟩, ⟨s₀', A', e', S', v'⟩⟩ =>
        ⟨⟨s₀, A, e, S, v.trans et⟩, ⟨s₀', A', e', S', v'.trans et⟩⟩
  refine VG.RelCT.seq sq ?_
  refine VG.RelCT.seq (storeRow_trace (fun _ h => h.run) (2 ^ (k + 1) + 2) 7 store7_check
    (F := TR Ex base bytes len args sp P G bits (2 ^ (k + 1) + 0 + 1) fun u =>
      sv u.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1))) fun u ⟨s₀, A, e, S, v⟩ =>
    WP.mono (S.store (n := 2 ^ (k + 1)) (by omega) (a := 7) (by decide) v) fun t ⟨S₂, K₂, _⟩ =>
      ⟨s₀, A, e, S₂, by show sv _ _ _ _ _ = _; rw [K₂ 7 (by decide)]; exact v⟩) ?_
  rw [List.range_eq_range']
  refine (relCT_seqs_range (fun j => product (2 ^ (k + 1)) (j + 1)) (fun j => TR Ex base bytes len args sp P G bits
      (2 ^ (k + 1) + j + 1) fun u => sv u.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)))
    (2 ^ (k + 1) - 1) 0 fun j _ hj => ?_).mono (fun _ _ h => h) fun _ _ h => ?_
  · have := product_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)
      (P := P) (G := G) (bits := bits) (k := k) (d := 2 ^ (k + 1)) (j := j + 1) hk rfl (by omega) (by omega) hP1
    rwa [show 2 ^ (k + 1) + (j + 1) = 2 ^ (k + 1) + j + 1 by omega,
      show 2 ^ (k + 1) + j + 1 + 1 = 2 ^ (k + 1) + (j + 1) + 1 by omega] at this
  · rwa [show 2 ^ (k + 1) + (0 + (2 ^ (k + 1) - 1)) + 1 = 2 ^ (k + 2) by omega] at h

/-- The table: the runs with the same modulus, generator and width leak the same traces. -/
theorem table_trace (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits) (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639)
    (hP1 : 1 < P) :
    RelCT isa (Both (TR Ex base bytes len args sp P G bits 0 fun u => sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧ sv u.mem base len .wide 10 = G)) table
      (Both (TR Ex base bytes len args sp P G bits 32 fun _ => True)) := by
  unfold table
  refine VG.RelCT.seq (initial_trace hP1) ?_
  rw [List.range_eq_range']
  refine (relCT_seqs_range column (fun k => TR Ex base bytes len args sp P G bits (2 ^ (k + 1)) fun u =>
      sv u.mem base len .wide 7 = entV len P G bits (2 ^ k)) 4 0 fun k _ hk => ?_).mono
    (fun _ _ h => h) fun _ _ ⟨⟨s₀, A, e, S, _⟩, ⟨s₀', A', e', S', _⟩⟩ => ⟨⟨s₀, A, e, S, trivial⟩, ⟨s₀', A', e', S', trivial⟩⟩
  exact column_trace (k := k) (by omega) hR hR' hP1

end

/-! ## The width -/

theorem scan_check : ACheck VG.Impl.Ffdh.X86.GenerateKey.scan := by dsimp only [ACheck]; taint_decide
theorem mbHead_check : ACheck (.block [.mov .eax (.imm 0), .mov .ecx (.mem (sc tOff))]) := by
  dsimp only [ACheck]; taint_decide
theorem boundBits_check : ACheck (.block boundBits) := by dsimp only [ACheck]; taint_decide
theorem capHead_check : ACheck (.block [.mov .edx (.mem (sc recOff)), .alu .test .edx (.reg .edx)]) := by
  dsimp only [ACheck]; taint_decide
theorem metadata_check : ACheck (.block metadata) := by dsimp only [ACheck]; taint_decide
theorem pSetup_check' : ACheck VG.Impl.Ffdh.X86.pSetup := by dsimp only [ACheck]; taint_decide
theorem loadG_check' : ACheck (load (.slot .wide 10) (one .wide) 4 5) := by dsimp only [ACheck]; taint_decide
theorem ret1_check : ACheck (VG.Impl.Ffdh.X86.ret 1) := by dsimp only [ACheck]; taint_decide

section
variable {dlen : Nat} {D : List Byte} {T : BitVec 32}

/-- The body's start, with the public domain `D` and the table at `T`. -/
structure PE (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (dlen : Nat) (D : List Byte) (T : BitVec 32) (x : State) : Prop where
  rp : RP Ex base bytes len args sp dlen D T x
  ok : ArgsOk x
  domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)
  cw : CtxW base bytes len args x
  dv : Spec.Ffdh.domainValid len D = true

/-- A stage of the body from its start, with `X`. -/
def SQ (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (dlen : Nat) (D : List Byte) (T : BitVec 32) (X : State → State → Prop) (u : State) : Prop :=
  ∃ x₀, PE Ex base bytes len args sp dlen D T x₀ ∧ Step Ex base bytes len args x₀ u ∧ X x₀ u

theorem SQ.run {X : State → State → Prop} {u : State} (h : SQ Ex base bytes len args sp dlen D T X u) :
    Run Ex base bytes len args sp u :=
  let ⟨_, P, S, _⟩ := h
  ⟨S.inp, P.ok.keep S.keeps, S.esp.trans P.rp.esp⟩

/-- The bound's octets, its first significant one and its bit length. -/
abbrev pBnd (len : Nat) (D : List Byte) : List Byte := VG.Proof.Ffdh.KeyScalar.bnd len D
abbrev pLd (len : Nat) (D : List Byte) : Nat := VG.Proof.Ffdh.lead (pBnd len D)
abbrev pN (len : Nat) (D : List Byte) : Nat :=
  Spec.RsaKeyGen.bitLength ((pBnd len D).getD (pLd len D) 0).toNat
abbrev pRec (len : Nat) (D : List Byte) : Nat :=
  VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len D
abbrev pW (len : Nat) (D : List Byte) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len D)

/-- The width's stages, with the start's public values. -/
theorem front_trace {Q : State → State → Prop} {rest : Prog isa}
    (hrest : RelCT isa (Both (SQ Ex base bytes len args sp dlen D T fun _ u =>
      u.gpr .eax = BitVec.ofNat 32 (pW len D))) rest Q) :
    RelCT isa (Both (PE Ex base bytes len args sp dlen D T)) (.seq recognize (.seq VG.Impl.Ffdh.X86.GenerateKey.scan
      (.seq maskBits (.seq (.block boundBits) (.seq cap rest))))) Q := by
  -- The recognized width.
  refine VG.RelCT.seq (relCT_both (F := SQ Ex base bytes len args sp dlen D T fun _ u =>
      w32 u.mem base recOff = pRec len D)
    ((recognize_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)).mono
      (fun _ _ h => ⟨h.1.rp, h.2.rp⟩) fun _ _ h => h) fun x P => ?_) ?_
  · have e := P.rp.esp
    exact WP.mono (recognize_ok P.rp.inp P.rp.geo (by rw [e]; exact P.rp.b40) P.rp.sym P.rp.tfit P.rp.tread
      P.rp.tbytes P.rp.tws (by rw [e]; exact P.rp.t40)) fun u ⟨S, _, r⟩ => ⟨x, P, S, by show w32 _ _ _ = _; rw [r, P.rp.dom]⟩
  -- The bound's first significant byte and its mask.
  refine VG.RelCT.seq (aRel (fun _ h => h.run) scan_check (F := SQ Ex base bytes len args sp dlen D T fun _ u =>
      w32 u.mem base recOff = pRec len D ∧ w32 u.mem base ldOff = pLd len D ∧
        w32 u.mem base tOff = 2 ^ pN len D - 1) fun u ⟨x₀, P, S, r⟩ => ?_) ?_
  · have e := P.rp.esp
    have G₁ := P.rp.geo.keep ⟨rfl, rfl⟩ S.keeps
    have hb := P.rp.b40
    rw [← e] at hb
    refine WP.mono (KeyScan.scan_ok S.inp P.rp.geo.e3 (KeyGen.bound_geo G₁ (by rw [S.esp]; exact hb))) fun t Sc => ?_
    have bs : Spec.Rsa.bytesAt u.mem (byteAddr (KeyScan.boundAt args)) len = pBnd len D := by
      rw [KeyGen.bound_bytes P.rp.geo, dom_keep P.rp.inp P.rp.geo hb S.frame, P.rp.dom]
    rw [bs] at Sc
    refine ⟨x₀, P, S.trans Sc.step, by rw [Sc.kept.word_eq (by simp only [recOff, numBase]; decide)]; exact r, Sc.ld, ?_⟩
    rw [Sc.t, VG.Proof.Ffdh.KeyScalar.smearN_eq _ (BitVec.isLt _)]
  -- The bit length of its first significant byte.
  have hn8 : pN len D ≤ 8 := by
    have := ((pBnd len D).getD (pLd len D) 0).isLt
    by_cases hz : ((pBnd len D).getD (pLd len D) 0).toNat = 0
    · show Spec.RsaKeyGen.bitLength _ ≤ 8; rw [hz]; decide
    · have hb : 2 ^ (pN len D - 1) ≤ ((pBnd len D).getD (pLd len D) 0).toNat :=
        (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hz).1
      by_contra hc
      have : 2 ^ 8 ≤ 2 ^ (pN len D - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  let M : Nat → State → Prop := fun j u => ∃ u₂, SQ Ex base bytes len args sp dlen D T (fun _ u =>
      w32 u.mem base recOff = pRec len D ∧ w32 u.mem base ldOff = pLd len D ∧
        w32 u.mem base tOff = 2 ^ pN len D - 1) u₂ ∧
    u.gpr .eax = BitVec.ofNat 32 j ∧ u.gpr .ecx = BitVec.ofNat 32 (2 ^ (pN len D - j) - 1) ∧ u.mem = u₂.mem ∧
      Keeps [.eax, .ecx] u₂ u
  have Mrun : ∀ {j u}, M j u → Run Ex base bytes len args sp u := fun ⟨u₂, Q₂, _, _, m, K⟩ => by
    have R := Q₂.run
    exact ⟨R.1.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
  have Mpos : ∀ {j u}, M j u → 1 ≤ pN len D := fun ⟨u₂, ⟨x₀, P, _, _⟩, _⟩ => by
    have hz := lead_ne P.dv P.rp.geo.lower (by rw [← P.rp.dom, VG.Proof.Bignum.bytesAt_length]; exact P.rp.geo.dl)
    have bt : ((pBnd len D).getD (pLd len D) 0).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq e)
    show 1 ≤ Spec.RsaKeyGen.bitLength _
    simp only [Spec.RsaKeyGen.bitLength, bt, ↓reduceIte]; omega
  have half : ∀ m < 9, 1 ≤ m → (2 ^ m - 1) / 2 = 2 ^ (m - 1) - 1 := by decide
  have zero : ∀ m < 9, (BitVec.ofNat 32 (2 ^ m - 1) == 0) = decide (m = 0) := by decide
  have mb : RelCT isa (Both (SQ Ex base bytes len args sp dlen D T fun _ u =>
      w32 u.mem base recOff = pRec len D ∧ w32 u.mem base ldOff = pLd len D ∧
        w32 u.mem base tOff = 2 ^ pN len D - 1)) maskBits (Both (M (pN len D))) := by
    unfold maskBits
    refine VG.RelCT.seq (aRel (fun _ h => h.run) mbHead_check (F := M 0) fun u Q => ?_) ?_
    · have nb : numBase = 3336 := rfl
      obtain ⟨x₀, P, S, r, l, t⟩ := Q
      refine wp_movS rfl fun s₁ U₁ _ => wp_movS (readW_ok (S.inp.regs U₁.keeps U₁.mem) (d := tOff)
        (v := 2 ^ pN len D - 1) (by decide) (by rw [U₁.mem]; exact t)
        (by have : 2 ^ pN len D ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hn8; omega)) fun s₂ U₂ _ =>
          WP.block_nil ⟨u, ⟨x₀, P, S, r, l, t⟩, by rw [U₂.other _ (by decide), U₁.gpr]; rfl,
            by rw [U₂.gpr, Nat.sub_zero], by rw [U₂.mem, U₁.mem], (U₁.keeps.mono (by decide)).widen U₂.keeps⟩
    by_cases hz : pN len D = 0
    · -- No run has a bound of bit length zero.
      exact fun x y _ _ _ _ h => absurd hz (by have := Mpos h.1; omega)
    refine relCT_countLoop (I := M) (by omega) fun j hj => relCT_both (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs (by simp)) (hc := .block []) (by rfl)) fun u ⟨u₂, Q₂, ea, ec, mt, Kt⟩ => ?_
    have pj : 2 ^ (pN len D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have sh : BitVec.ofNat 32 (2 ^ (pN len D - j) - 1) >>> 1 = BitVec.ofNat 32 (2 ^ (pN len D - (j + 1)) - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.shiftRight_eq_div_pow, Nat.pow_one, half (pN len D - j) (by omega) (by omega),
        show pN len D - j - 1 = pN len D - (j + 1) by omega]
      have : 2 ^ (pN len D - (j + 1)) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.mod_eq_of_lt (by omega)]
    refine wp_addS rfl fun t₁ V₁ _ => wp_shr (by decide) fun t₂ V₂ _ => wp_testS rfl fun t₃ V₃ z₃ =>
      WP.block_nil ⟨⟨u₂, Q₂, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [V₃.gpr, V₂.other _ (by decide), V₁.gpr, ea, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_add_ofNat]
    · rw [V₃.gpr, V₂.gpr, V₁.other _ (by decide), ec, sh]
    · rw [V₃.mem, V₂.mem, V₁.mem, mt]
    · exact Kt.trans (((V₁.keeps.mono (by decide)).widen V₂.keeps).trans ((V₃.keeps []).mono (by decide)))
    · rw [z₃, V₂.gpr, V₁.other _ (by decide), ec, sh, BitVec.and_self, zero _ (by omega)]
      congr 1
      exact decide_eq_decide.mpr (by omega)
  refine VG.RelCT.seq (mb.mono (fun _ _ h => h) (Q' := Both (SQ Ex base bytes len args sp dlen D T fun _ u =>
      w32 u.mem base recOff = pRec len D ∧ w32 u.mem base ldOff = pLd len D ∧
        u.gpr .eax = BitVec.ofNat 32 (pN len D))) fun _ _ h => ⟨?_, ?_⟩) ?_
  rotate_left
  · obtain ⟨u₂, ⟨x₀, P, S, r, l, _⟩, ea, _, mt, Kt⟩ := h.1
    exact ⟨x₀, P, S.trans (Step.regs S.inp mt Kt), by rw [mt]; exact r, by rw [mt]; exact l, ea⟩
  · obtain ⟨u₂, ⟨x₀, P, S, r, l, _⟩, ea, _, mt, Kt⟩ := h.2
    exact ⟨x₀, P, S.trans (Step.regs S.inp mt Kt), by rw [mt]; exact r, by rw [mt]; exact l, ea⟩
  -- The bound's bit length.
  refine VG.RelCT.seq (aRel (fun _ h => h.run) boundBits_check (F := SQ Ex base bytes len args sp dlen D T fun _ u =>
      w32 u.mem base recOff = pRec len D ∧
        u.gpr .eax = BitVec.ofNat 32 (pN len D + 8 * (len - 1 - pLd len D))) fun u ⟨x₀, P, S, r, l, ea⟩ => ?_) ?_
  · have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length (k := len) (dom := D)
      (by rw [← P.rp.dom, VG.Proof.Bignum.bytesAt_length]; exact P.rp.geo.dl)
    have hne : VG.Proof.Ffdh.KeyScalar.bnd len D ≠ [] := by
      intro he; rw [he] at hbl; simp at hbl; have := P.rp.geo.lower; omega
    have hld : pLd len D < len := by have := VG.Proof.Ffdh.lead_lt hne; rwa [hbl] at this
    exact WP.mono (boundBits_ok S.inp P.rp.geo.e3 l hld ea) fun t ⟨e, m, K⟩ =>
      ⟨x₀, P, S.trans (Step.regs S.inp m K), by rw [m]; exact r, e⟩
  -- The width.
  refine VG.RelCT.seq (relCT_both (F := SQ Ex base bytes len args sp dlen D T fun _ u =>
      u.gpr .eax = BitVec.ofNat 32 (pW len D)) ?_ fun u ⟨x₀, P, S, r, ea⟩ => ?_) hrest
  · have nb : numBase = 3336 := rfl
    unfold cap
    let bl := pN len D + 8 * (len - 1 - pLd len D)
    let C1 : State → Prop := fun u => ∃ x₀, PE Ex base bytes len args sp dlen D T x₀ ∧
      Run Ex base bytes len args sp u ∧ u.zf = some (decide (pRec len D = 0)) ∧
      u.gpr .edx = BitVec.ofNat 32 (pRec len D) ∧ u.gpr .eax = BitVec.ofNat 32 bl
    refine VG.RelCT.seq (aRel (fun _ h => h.run) capHead_check (F := C1) fun u h => ?_) ?_
    · obtain ⟨x₀, P, S, r, ea⟩ := h
      have up := P.rp.geo.upper
      have rl := recognize_lt len D
      refine wp_movS (readW_ok S.inp (d := recOff) (by simp only [recOff]; omega) r rl) fun s₁ U₁ _ =>
        wp_testS rfl fun s₂ V₂ z₂ => WP.block_nil ⟨x₀, P, ?_, ?_, by rw [V₂.gpr, U₁.gpr],
          by rw [V₂.gpr, U₁.other _ (by decide)]; exact ea⟩
      · have R : Run Ex base bytes len args sp u := ⟨S.inp, P.ok.keep S.keeps, S.esp.trans P.rp.esp⟩
        have K : Keeps [.edx] u s₂ := U₁.keeps.trans ((V₂.keeps []).mono (by decide))
        exact ⟨R.1.regs K (by rw [V₂.mem, U₁.mem]), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
      · rw [z₂, U₁.gpr, BitVec.and_self]
        congr 1
        by_cases e : pRec len D = 0
        · rw [e]; rfl
        · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
          intro c
          have := congrArg BitVec.toNat c
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt rl] at this
          exact e this
    refine VG.RelCT.ite (fun x y h => by
      obtain ⟨⟨_, _, _, z₁, _⟩, ⟨_, _, _, z₂, _⟩⟩ := h
      show x.zf = y.zf; rw [z₁, z₂]) (RelCT.block_nil fun _ _ _ => trivial) ?_
    let C2 : State → Prop := fun u => ∃ v, C1 v ∧ u.cf = some (decide (pRec len D < bl))
    refine VG.RelCT.seq ((relCT_both (P := C1) (F := C2) (c := .block [.alu .cmp .edx (.reg .eax)])
      (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs (by simp)) (hc := .block []) (by rfl)) fun u h => wp_cmp fun t V c _ =>
        WP.block_nil ⟨u, h, ?_⟩).mono (P' := fun x y => Both C1 x y ∧ isa.eval .e x = some false)
          (fun _ _ h => h.1) fun _ _ h => h) ?_
    · obtain ⟨x₀, P, _, _, ed, ea⟩ := h
      have up := P.rp.geo.upper
      have hn8' := hn8
      rw [c, ed, ea, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (recognize_lt _ _),
        Nat.mod_eq_of_lt (show bl < 2 ^ 32 by omega)]
    exact VG.RelCT.ite (fun x y h => by
      obtain ⟨⟨_, _, c₁⟩, ⟨_, _, c₂⟩⟩ := h
      show x.cf = y.cf; rw [c₁, c₂]) (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp))
        (hc := .block []) (by rfl)) (RelCT.block_nil fun _ _ _ => trivial)
  · have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length (k := len) (dom := D)
      (by rw [← P.rp.dom, VG.Proof.Bignum.bytesAt_length]; exact P.rp.geo.dl)
    have up := P.rp.geo.upper
    have size : D.length = 2 * len ∨ D.length = 3 * len := by
      rw [← P.rp.dom, VG.Proof.Bignum.bytesAt_length]; exact P.rp.geo.dl
    refine WP.mono (cap_ok S.inp r (recognize_lt _ _) ea (by omega)) fun t ⟨e, m, K⟩ =>
      ⟨x₀, P, S.trans (Step.regs S.inp m K), ?_⟩
    show t.gpr .eax = _
    rw [e, show pN len D + 8 * (len - 1 - pLd len D) = Spec.RsaKeyGen.bitLength ((pBnd len D).getD (pLd len D) 0).toNat +
      8 * (len - 1 - pLd len D) from rfl, width_spec P.dv P.rp.geo.lower size]

/-- The context's stages, with the start's public values. -/
def MQ (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (dlen : Nat) (D : List Byte) (T : BitVec 32) (X : State → Prop) (u : State) : Prop :=
  ∃ x₀, PE Ex base bytes len args sp dlen D T x₀ ∧ In Ex base bytes len args u ∧ CtxW base bytes len args u ∧
    Frame (ctxR args len :: frameR base sp (fR len)) x₀.mem u.mem ∧
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] x₀ u ∧
    w32 u.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows (pW len D) ∧ X u

theorem MQ.run {X : State → Prop} {u : State} (h : MQ Ex base bytes len args sp dlen D T X u) :
    Run Ex base bytes len args sp u :=
  let ⟨_, P, I, _, _, K, _⟩ := h
  ⟨I, P.ok.keep K, (K.1 _ (by decide)).trans P.rp.esp⟩

/-- p's context and the rows, with the start's public values. -/
def CQ (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  CtxOk Ex base bytes len args .wide (Spec.Ffdh.domainOf len D).p u ∧ CtxW base bytes len args u ∧ ArgsOk u ∧
    u.gpr .esp = sp ∧ w32 u.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows (pW len D) ∧
    sv u.mem base len .wide 3 = 1 ∧ sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % (Spec.Ffdh.domainOf len D).p ∧
    sv u.mem base len .wide 10 = (Spec.Ffdh.domainOf len D).g

theorem CQ.run {u : State} (h : CQ Ex base bytes len args sp D u) : Run Ex base bytes len args sp u :=
  ⟨h.1.inp, h.2.2.1, h.2.2.2.1⟩

/-- The stages after the width. -/
theorem middle_trace (dv : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both (SQ Ex base bytes len args sp dlen D T fun _ u => u.gpr .eax = BitVec.ofNat 32 (pW len D)))
      (.seq (.block metadata) (.seq VG.Impl.Ffdh.X86.pSetup (.seq (load (.slot .wide 10) (one .wide) 4 5)
        (.seq VG.Impl.Ffdh.X86.ctxP (.seq (storeRow (rowImm 0) 9) (.seq (storeRow (rowImm 1) 4)
          (.seq table (VG.Impl.Ffdh.X86.ret 1)))))))) fun _ _ => True := by
  have upB : ∀ {m m' : Mem}, Frame (frameR base sp (fR len)) m m' →
      Frame (ctxR args len :: frameR base sp (fR len)) m m' :=
    fun F => F.mono fun r hr => List.mem_cons_of_mem _ hr
  -- The metadata.
  refine VG.RelCT.seq (aRel (fun _ h => h.run) metadata_check (F := MQ Ex base bytes len args sp dlen D T fun _ => True)
    fun u ⟨x₀, P, S, ea⟩ => ?_) ?_
  · have bf := VG.Proof.Ffdh.ContextRows.genBits_facts P.dv
    have up := P.rp.geo.upper
    refine WP.mono (metadata_ok S.inp (P.cw.keep S.keeps) ea (by have := bf.2; unfold pW; omega))
      fun t ⟨I, C, F, K, _, wr, _⟩ => ?_
    have e : u.gpr .esp = sp := S.esp.trans P.rp.esp
    rw [e] at F
    have Fs := S.frame
    rw [P.rp.esp] at Fs
    exact ⟨x₀, P, I, C, (upB Fs).trans F, S.keeps.trans (K.mono (by decide)), wr, trivial⟩
  -- p, one and `p − 1`.
  refine VG.RelCT.seq (aRel (fun _ h => h.run) pSetup_check' (F := MQ Ex base bytes len args sp dlen D T fun u =>
      sv u.mem base len .wide 9 = (Spec.Ffdh.domainOf len D).p) fun u ⟨x₀, P, I, C, F, K, wr, _⟩ => ?_) ?_
  · have G := P.rp.geo
    have dl := G.dl
    have lw := G.lower
    have dfit := G.fit
    have G₆ := G.keep ⟨rfl, rfl⟩ K
    have hb := P.rp.b40
    rw [← P.rp.esp] at hb F
    refine WP.mono (pSetup_ok I G.e3 (by omega)
      (by have := VG.CallLay.inRegions_sub G₆.rd (off := 0) (l := len) (by omega) (by omega)
          rwa [BitVec.add_zero] at this)
      (G.apart.sub_left (Region.sub_prefix (by omega)))) fun t ⟨I₇, F₇, k₇, v9, _, _, K₇⟩ => ?_
    rw [CheckDomain.argNum_comp, comp_keepC P.rp.inp G hb P.domC F (by omega), comp_p x₀.mem args (dlen := dlen) (by omega),
      P.rp.dom] at v9
    have e : u.gpr .esp = sp := (K.1 _ (by decide)).trans P.rp.esp
    rw [e] at F₇
    rw [P.rp.esp] at F
    exact ⟨x₀, P, I₇, C.keep K₇, F.trans (upB F₇), K.trans K₇,
      by rw [k₇.word_eq (by simp only [rowsOff, numBase]; decide)]; exact wr, v9⟩
  -- g.
  refine VG.RelCT.seq (aRel (fun _ h => h.run) loadG_check' (F := MQ Ex base bytes len args sp dlen D T fun u =>
      sv u.mem base len .wide 9 = (Spec.Ffdh.domainOf len D).p ∧
        sv u.mem base len .wide 10 = (Spec.Ffdh.domainOf len D).g) fun u ⟨x₀, P, I, C, F, K, wr, v9⟩ => ?_) ?_
  · have G := P.rp.geo
    have dl := G.dl
    have hb := P.rp.b40
    rw [← P.rp.esp] at hb F
    refine WP.mono (loadComp_ok I (G.keep ⟨rfl, rfl⟩ K) (k := 1) (j := 10) (by decide) (by omega) (by decide))
      fun t ⟨v10, O, K₈⟩ => ?_
    rw [comp_keepC P.rp.inp G hb P.domC F (by omega), comp_g x₀.mem args (dlen := dlen) (by omega), P.rp.dom] at v10
    have S₈ : Step Ex base bytes len args u t := Step.slot I (by decide) O K₈
    have e : u.gpr .esp = sp := (K.1 _ (by decide)).trans P.rp.esp
    have F₈ := S₈.frame
    rw [e] at F₈
    rw [P.rp.esp] at F
    exact ⟨x₀, P, S₈.inp, C.keep S₈.keeps, F.trans (upB F₈), K.trans S₈.keeps,
      by rw [(kept_slot I (a := 10) O).word_eq (by simp only [rowsOff, numBase]; decide)]; exact wr,
      by rw [(kept_slot I (a := 10) O).slot_eq]; exact v9, v10⟩
  -- p's context.
  refine VG.RelCT.seq (relCT_both (F := CQ Ex base bytes len args sp D)
    ((VG.Proof.Ffdh.X86.ctxP_relCT (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args)
      (sp := sp)).mono (fun _ _ h => ⟨h.1.run, h.2.run⟩) fun _ _ _ => trivial)
    fun u ⟨x₀, P, I, C, F, K, wr, v9, v10⟩ => ?_) ?_
  · obtain ⟨hodd, h1p, -⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod P.dv) P.rp.geo.lower
    refine WP.mono (ctxP_ok I (P := (Spec.Ffdh.domainOf len D).p) (by rw [v9]; exact safeM_of h1p hodd))
      fun t ⟨Cx, s3, s4, _, k₉, K₉⟩ => ⟨Cx, C.keep K₉, P.ok.keep (K.trans K₉),
        ((K.trans K₉).1 _ (by decide)).trans P.rp.esp,
        by rw [k₉.word_eq (by simp only [rowsOff, numBase]; decide)]; exact wr, s3, s4,
        by rw [k₉.slot_eq]; exact v10⟩
  -- Rows 0 and 1.
  have keepCQ : ∀ {u t : State}, CQ Ex base bytes len args sp D u →
      CtxOk Ex base bytes len args .wide (Spec.Ffdh.domainOf len D).p t → CtxW base bytes len args t →
      (∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 u.mem base d N) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u t → CQ Ex base bytes len args sp D t :=
    fun {u t} Q Cx C W K => by
      have bl := Q.1.inp.bytes_lt
      have nd := Q.1.inp.need
      have nb : numBase = 3336 := rfl
      have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
      have est : st len .wide = 2 * bc len .wide + 32 := rfl
      have bw := bc_eq_cwc len .wide
      have sl : ∀ j, j ≤ 27 → sv t.mem base len .wide j = sv u.mem base len .wide j := fun j hj => by
        have := Q.1.inp.slot_fit .wide (j := j) hj
        exact W (by omega)
      refine ⟨Cx, C, Q.2.2.1.keep K, (K.1 _ (by decide)).trans Q.2.2.2.1, ?_, by rw [sl 3 (by decide)]; exact Q.2.2.2.2.2.1,
        by rw [sl 4 (by decide)]; exact Q.2.2.2.2.2.2.1, by rw [sl 10 (by decide)]; exact Q.2.2.2.2.2.2.2⟩
      rw [← w32_val32_one, W (by simp only [rowsOff]; omega), w32_val32_one]; exact Q.2.2.2.2.1
  refine VG.RelCT.seq (storeRow_trace (fun _ h => h.run) 0 9 store9_check (F := CQ Ex base bytes len args sp D)
    fun u Q => WP.mono (storePre_ok Q.1 Q.2.1 (j := 0) (a := 9) (by decide) (by decide))
      fun t ⟨Cx, C, _, _, W, _, K⟩ => keepCQ Q Cx C W K) ?_
  refine VG.RelCT.seq (storeRow_trace (fun _ h => h.run) 1 4 store4_check (F := CQ Ex base bytes len args sp D)
    fun u Q => WP.mono (storePre_ok Q.1 Q.2.1 (j := 1) (a := 4) (by decide) (by decide))
      fun t ⟨Cx, C, _, _, W, _, K⟩ => keepCQ Q Cx C W K) ?_
  -- The table.
  refine VG.RelCT.seq (P := Both (CQ Ex base bytes len args sp D)) ?_
    (aEnd (P := TR Ex base bytes len args sp (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (pW len D) 32
      fun _ => True) (fun _ h => h.run) ret1_check)
  intro x y tx ty x' y' h ex ey
  obtain ⟨Q₁, Q₂⟩ := h
  have P1 := Q₁.1.gt
  have bf' := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  have bf : pW len D ≤ 8192 := by unfold pW; omega
  have hR := VG.Proof.Rsa.FixedBaseComb.rows_small bf
  have rp : 0 < Spec.Rsa.FixedBaseComb.rows (pW len D) := VG.Proof.Rsa.FixedBaseComb.rows_pos (by unfold pW; omega)
  have toTR : ∀ {u : State}, CQ Ex base bytes len args sp D u → TR Ex base bytes len args sp
      (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (pW len D) 0 (fun u =>
        sv u.mem base len .wide 3 = 1 ∧ sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) %
          (Spec.Ffdh.domainOf len D).p ∧ sv u.mem base len .wide 10 = (Spec.Ffdh.domainOf len D).g) u :=
    fun {u} Q => ⟨u, Q.2.2.1, Q.2.2.2.1, ⟨Q.1, Q.2.1, by omega, fun e he => absurd he (Nat.not_lt_zero _),
      Q.2.2.2.2.1, rfl, Frame.refl _ _, Keeps.refl _ _⟩, Q.2.2.2.2.2⟩
  exact table_trace rp hR.1 P1 x y tx ty x' y' ⟨toTR Q₁, toTR Q₂⟩ ex ey

/-- The precomputation's body: runs from the same public start leak the same traces. -/
theorem pcBody_trace (dv : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both (PE Ex base bytes len args sp dlen D T)) Precompute.body fun _ _ => True := by
  unfold Precompute.body
  exact front_trace (middle_trace dv hl)

end

end

end VG.Proof.Ffdh.X86.Cached
