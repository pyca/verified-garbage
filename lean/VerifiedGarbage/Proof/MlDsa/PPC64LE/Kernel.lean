module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Saving
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Sha3.PPC64LE.PiecesCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny

/-!
# ML-DSA on PPC64LE: the kernels' frames

A kernel with a cache (`vg_mldsa*_sign_with_cache`,
`vg_mldsa*_verify_with_cache`) is `saving (mov r14, a; mov r15, b; body)`:
the frames saving `r14` and `r15` (`Arith.saving`), the cache's pointer (in
`a`) and length (in `b`) moved there, and the function's body, which runs
from `kSt a b σ₀`. If the body keeps the registers our caller expects us to
keep, for that state, so does the kernel, and its result and memory are the
body's (`kernel_wp`). Two runs of the kernel leak the same if the runs of
the body from those states do (`kernel_tr`): a frame's push makes its
16 bytes writable, which the body's runs from the states without them
(`framed`) do not need, and a run with more permissions leaks the same
(`relct_frameN`, by `Exec.widen` and determinism).

An entry (`vg_mldsa*_sign`, `vg_mldsa*_sign_prepared`, …) is `entryCode mv
name code`: the link register saved in a frame (through `r0`), the moves
`mv` of the kernel's extra arguments, a call of the kernel, and the link
register restored. With the kernel verified, the entry keeps what our caller
expects and has the kernel's result and memory (`entry_wp`), and two runs
leak the same if the kernel's preconditions and public data hold of the
calls (`entry_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Arith (saving)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- The state the body starts in, for a kernel entered in `σ₀`. -/
def kSt (a b : Reg) (σ₀ : State) : State :=
  ((framed .r15 (framed .r14 σ₀)).write .r14 (σ₀.gpr a)).write .r15 (σ₀.gpr b)

/-- The moves of the cache's pointer and length. -/
abbrev kMovs (a b : Reg) : List Instr := [mov .r14 a, mov .r15 b]

theorem kMovs_ok {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb14 : b ≠ .r14) (s : State) :
    WP isa (.block (kMovs a b)) s (· = (s.write .r14 (s.gpr a)).write .r15 (s.gpr b)) := by
  refine WP.cons (exec_addi ha (by decide)) (WP.cons (exec_addi hb (by decide)) (WP.block_nil ?_))
  rw [RegUpd.gpr_write_of_ne _ _ hb14, BitVec.add_zero, BitVec.add_zero]

theorem kSt_gpr {a b : Reg} (σ₀ : State) {r : Reg} (h14 : r ≠ .r14) (h15 : r ≠ .r15) :
    (kSt a b σ₀).gpr r = σ₀.gpr r := by
  unfold kSt; rw [RegUpd.gpr_write_of_ne _ _ h15, RegUpd.gpr_write_of_ne _ _ h14]; rfl

theorem kSt_r14 {a b : Reg} (σ₀ : State) : (kSt a b σ₀).gpr .r14 = σ₀.gpr a := by
  unfold kSt; rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self]
theorem kSt_r15 {a b : Reg} (σ₀ : State) : (kSt a b σ₀).gpr .r15 = σ₀.gpr b := by
  unfold kSt; rw [RegUpd.gpr_write_self]
theorem kSt_sp {a b : Reg} (σ₀ : State) : (kSt a b σ₀).sp = σ₀.sp - 96 := Arith.body_state.sp
theorem kSt_rd {a b : Reg} (σ₀ : State) : (kSt a b σ₀).rd = σ₀.rd := rfl
theorem kSt_wr {a b : Reg} (σ₀ : State) : (kSt a b σ₀).wr = σ₀.wr := rfl
theorem kSt_lr {a b : Reg} (σ₀ : State) : (kSt a b σ₀).lr = σ₀.lr := rfl
theorem kSt_mem {a b : Reg} (σ₀ : State) : Frame [below σ₀.sp 96] σ₀.mem (kSt a b σ₀).mem :=
  Arith.body_state.frame

/-- Two runs of a frame saving `r` leak the same if the runs of its body
from the states without the frame's region do, and those runs exist. -/
theorem relct_frameN {r : Reg} {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → (∃ Q, WP isa body (framed r s₁) Q) ∧ ∃ Q, WP isa body (framed r s₂) Q)
    (hb : RelCT isa (fun u v => ∃ s₁ s₂, P s₁ s₂ ∧ u = framed r s₁ ∧ v = framed r s₂) body fun _ _ => True) :
    RelCT isa P (.frame (.push r) body (.pop r)) fun _ _ => True := by
  refine RelCT.mono (RelCT.frame (R := fun _ _ => True) hsp ?_) (fun _ _ h => h) fun _ _ _ => trivial
  intro u v t₁ t₂ u' v' ⟨s₁, s₂, hp, eu, ev⟩ e₁ e₂
  subst eu ev
  obtain ⟨⟨_, _, _, f₁, _⟩, ⟨_, _, _, f₂, _⟩⟩ := hw s₁ s₂ hp
  have wid : ∀ (s : State) {t : List Leak} {s' : State}, Exec isa body (framed r s) t s' →
      Exec isa body (pushed r s) t (s'.withRegions (pushed r s).rd (pushed r s).wr) := fun s t s' h => by
    have := Exec.widen h (rd := (pushed r s).rd) (wr := (pushed r s).wr)
      (fun a n hi => by
        simp only [framed, pushed] at hi ⊢
        exact InRegions_append_cons (xs := s.rd).mpr (.inr hi))
      (fun a n hi => by
        simp only [framed, pushed] at hi ⊢
        exact InRegions_append_cons (xs := []).mpr (.inr hi))
    exact this
  obtain ⟨rfl, -⟩ := Exec.det e₁ (wid s₁ f₁)
  obtain ⟨rfl, -⟩ := Exec.det e₂ (wid s₂ f₂)
  exact ⟨(hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩


section
variable {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb14 : b ≠ .r14)
include ha hb hb14

/-- The frame saving `r15` around the moves and the body, from the state
after the frame saving `r14`. -/
theorem inner_wp {body : Prog isa} {σ₀ : State} {Q : State → Prop}
    (hsp : 96 ≤ σ₀.sp.toNat) (hd : ∀ X ∈ σ₀.wr, (below σ₀.sp 96).Disjoint X) (hn : sdepth body + 96 < 2 ^ 64)
    (hbody : WP isa body (kSt a b σ₀) fun s' => Q { s'.write .r15 ((framed .r14 σ₀).gpr .r15) with
      sp := (framed .r14 σ₀).sp }) :
    WP isa (.frame (.push .r15) (.seq (.block (kMovs a b)) body) (.pop .r15)) (framed .r14 σ₀) Q := by
  have hsp1 : 48 ≤ (σ₀.sp - 48).toNat := by bv_omega
  refine WP.frameRegAny (r := .r15) hsp1 (fun R hR => ?_)
    (WP.seq (WP.mono (kMovs_ok ha hb hb14 _) fun s e => by subst e; exact hbody))
    (by simp only [sdepth, Nat.zero_max]; omega)
  have : (framed .r14 σ₀).sp = σ₀.sp - 48 := rfl
  rw [this, show σ₀.sp - 48 - 48 = σ₀.sp - BitVec.ofNat 64 96 by bv_omega]
  exact (hd R hR).sub_left (Arith.frame_slot_sub σ₀.sp (.inr rfl))

/-- A kernel: the body's result and memory, and the registers kept. -/
theorem kernel_wp {body : Prog isa} {σ₀ : State} {R : Mem → BitVec 64 → Prop}
    (hsp : 96 ≤ σ₀.sp.toNat) (hd : ∀ X ∈ σ₀.wr, (below σ₀.sp 96).Disjoint X) (hn : sdepth body + 96 < 2 ^ 64)
    (hbody : WP isa body (kSt a b σ₀) fun s' =>
      PPC64LE.target.abiPreserved (kSt a b σ₀) s' ∧ R s'.mem (s'.gpr .r3)) :
    WP isa (saving (.seq (.block (kMovs a b)) body)) σ₀ fun s' =>
      PPC64LE.target.abiPreserved σ₀ s' ∧ R s'.mem (s'.gpr .r3) := by
  refine WP.frameRegAny (r := .r14) (by omega)
    (fun R hR => (hd R hR).sub_left (Arith.frame_slot_sub σ₀.sp (.inl rfl))) ?_
    (by simp only [sdepth, Instr.frameBytes, Nat.zero_max]; omega)
  refine inner_wp ha hb hb14 hsp hd hn (WP.mono hbody fun s' ⟨⟨hk, hsp', hlr⟩, hR⟩ => ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
  · simp only [State.write]
    by_cases h14 : r = .r14
    · subst h14; simp
    · by_cases h15 : r = .r15
      · subst h15; simp [framed]
      · simp only [h14, h15, ite_false]
        rw [hk r hr, kSt_gpr σ₀ h14 h15]
  · show s'.lr = σ₀.lr
    rw [hlr]; rfl
  · exact hR

/-- Two runs of a kernel leak the same if the runs of its body do, and the
body runs from the state each starts in. -/
theorem kernel_tr {body : Prog isa} {P : State → State → Prop} (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hsp' : ∀ x y, P x y → 96 ≤ x.sp.toNat ∧ 96 ≤ y.sp.toNat ∧ (∀ X ∈ x.wr, (below x.sp 96).Disjoint X) ∧
      ∀ X ∈ y.wr, (below y.sp 96).Disjoint X)
    (hn : sdepth body + 96 < 2 ^ 64)
    (hw : ∀ x y, P x y → (∃ Q, WP isa body (kSt a b x) Q) ∧ ∃ Q, WP isa body (kSt a b y) Q)
    (hbody : RelCT isa (fun u v => ∃ x y, P x y ∧ u = kSt a b x ∧ v = kSt a b y) body fun _ _ => True) :
    RelCT isa P (saving (.seq (.block (kMovs a b)) body)) fun _ _ => True := by
  have hwb : ∀ x, 96 ≤ x.sp.toNat → (∀ X ∈ x.wr, (below x.sp 96).Disjoint X) → (∃ Q, WP isa body (kSt a b x) Q) →
      ∃ Q, WP isa (.frame (.push .r15) (.seq (.block (kMovs a b)) body) (.pop .r15)) (framed .r14 x) Q :=
    fun x h1 h2 ⟨Q, hq⟩ => ⟨_, inner_wp ha hb hb14 h1 h2 hn (Q := fun _ => True) (WP.mono hq fun _ _ => trivial)⟩
  refine relct_frameN hsp (fun x y h => ?_) (relct_frameN (fun u v ⟨x, y, h, eu, ev⟩ => by
    subst eu ev; show x.sp - 48 = y.sp - 48; rw [hsp x y h]) (fun u v ⟨x, y, h, eu, ev⟩ => ?_) ?_)
  · obtain ⟨a1, a2, a3, a4⟩ := hsp' x y h
    exact ⟨hwb x a1 a3 (hw x y h).1, hwb y a2 a4 (hw x y h).2⟩
  · subst eu ev
    obtain ⟨⟨Q₁, h₁⟩, ⟨Q₂, h₂⟩⟩ := hw x y h
    exact ⟨⟨_, WP.seq (WP.mono (kMovs_ok ha hb hb14 _) fun s e => by subst e; exact h₁)⟩,
      ⟨_, WP.seq (WP.mono (kMovs_ok ha hb hb14 _) fun s e => by subst e; exact h₂)⟩⟩
  · refine RelCT.seq (RelCT.wpDep (F := fun u u' => u' = (u.write .r14 (u.gpr a)).write .r15 (u.gpr b))
      (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem rfl)
      fun u v _ => ⟨kMovs_ok ha hb hb14 u, kMovs_ok ha hb hb14 v⟩) (RelCT.mono hbody ?_ fun _ _ h => h)
    rintro u' v' ⟨-, u, v, ⟨u₀, v₀, ⟨x, y, h, ex, ey⟩, eu, ev⟩, e₁, e₂⟩
    subst ex ey eu ev e₁ e₂
    exact ⟨x, y, h, rfl, rfl⟩

end

/-! ## Entries -/

/-- An entry: the moves `mv`, then a call of `code` named `name`, in a frame
saving the link register (in `r0`). -/
abbrev entryCode (mv : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (.seq (.block mv) (.call name code)) (.pop .r0))
    (.block [.mtlr .r0]))

/-- The state an entry's moves start in. -/
def eSt (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem eSt_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (eSt s₀).gpr r = s₀.gpr r :=
  RegUpd.gpr_write_of_ne _ _ h
theorem eSt_sp (s₀ : State) : (eSt s₀).sp = s₀.sp - 48 := rfl
theorem eSt_rd (s₀ : State) : (eSt s₀).rd = s₀.rd := rfl
theorem eSt_wr (s₀ : State) : (eSt s₀).wr = s₀.wr := rfl

theorem eSt_mem (s₀ : State) : Frame [below s₀.sp 48] s₀.mem (eSt s₀).mem := by
  show Frame _ s₀.mem ((s₀.mem.write (s₀.sp - 48) 8 s₀.sp).write (s₀.sp - 48 + 32) 8 s₀.lr)
  have c : ∀ d : Nat, d + 8 ≤ 48 → (below s₀.sp 48).Contains (s₀.sp - 48 + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base _ hd (by omega)
  have e1 : s₀.sp - 48 = s₀.sp - 48 + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  have e2 : s₀.sp - 48 + 32 = s₀.sp - 48 + BitVec.ofNat 64 32 := rfl
  rw [e2]
  conv => rhs; arg 1; rw [e1]
  exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (c 0 (by omega))).write
    (List.mem_singleton_self _) _ (c 32 (by omega))

/-- What an entry's moves keep. -/
structure MvOk (F : State → State) : Prop where
  mem : ∀ u, (F u).mem = u.mem
  rd : ∀ u, (F u).rd = u.rd
  wr : ∀ u, (F u).wr = u.wr
  sp : ∀ u, (F u).sp = u.sp
  pres : ∀ u, ∀ r ∈ preserved, (F u).gpr r = u.gpr r

section
variable {mv : List Instr} {name : String} {code : Prog isa} {k : Contract isa}
  (hv : ∀ s, k.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ k.post s s')
  (hdc : sdepth code + 48 < 2 ^ 64)
  {F : State → State} (hmv : ∀ u, WP isa (.block mv) u (· = F u)) (hF : MvOk F)
include hv hdc hmv hF

/-- The frame of an entry, from the state after `mflr`. -/
theorem entry_inner {s₀ : State} {rd wr : List Region} {R : Mem → BitVec 64 → Prop}
    (hpre : k.pre ((F (eSt s₀)).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s₀.rd ++ s₀.wr)) (hw : Covers wr s₀.wr)
    (hQ : ∀ s' : State, k.post ((F (eSt s₀)).callEntry.withRegions rd wr) (s'.withRegions rd wr) →
      R s'.mem (s'.gpr .r3)) :
    WP isa (.seq (.block mv) (.call name code)) (eSt s₀) fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ R s'.mem (s'.gpr .r3) := by
  refine WP.seq (WP.mono (hmv _) fun u e => ?_)
  subst e
  refine WP.callAny hv hpre (by rw [hF.rd, hF.wr]; exact hc) (by rw [hF.wr]; exact hw)
    (fun s' _ _ _ _ hcs hp => ⟨fun r hr => ?_, hQ s' hp⟩) (by omega)
  rw [hcs r hr, hF.pres _ r hr, eSt_gpr s₀ (fun e => by subst e; simp [preserved] at hr)]

/-- An entry: the kernel's result and memory, and the registers kept. -/
theorem entry_wp {s₀ : State} {rd wr : List Region} {R : Mem → BitVec 64 → Prop}
    (hsp : 48 ≤ s₀.sp.toNat) (hd : ∀ X ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 48 + 32, 16⟩ X)
    (hpre : k.pre ((F (eSt s₀)).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s₀.rd ++ s₀.wr)) (hw : Covers wr s₀.wr)
    (hQ : ∀ s' : State, k.post ((F (eSt s₀)).callEntry.withRegions rd wr) (s'.withRegions rd wr) →
      R s'.mem (s'.gpr .r3)) :
    WP isa (entryCode mv name code) s₀ fun s' => PPC64LE.target.abiPreserved s₀ s' ∧ R s'.mem (s'.gpr .r3) := by
  refine WP.seq (WP.cons exec_mflr (WP.block_nil ?_))
  refine WP.seq (WP.frameRegAny (r := .r0) hsp hd (WP.mono (entry_inner hv hdc hmv hF hpre hc hw hQ)
    fun s' ⟨hp, hR⟩ => ?_) (by simp only [sdepth, Nat.zero_max]; omega))
  refine WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
  · show (s'.write .r0 _).gpr r = s₀.gpr r
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => by subst e; simp [preserved] at hr), hp r hr]
  · show (s'.write .r0 ((s₀.write .r0 s₀.lr).gpr .r0)).gpr .r0 = s₀.lr
    rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self]
  · show R s'.mem ((s'.write .r0 ((s₀.write .r0 s₀.lr).gpr .r0)).gpr .r3)
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hR

/-- Two runs of an entry leak the same if the kernel's preconditions and
public data hold of their calls. -/
theorem entry_tr (hct : ConstantTime isa k.pre k.pub code) (hnm : mv.all VG.Proof.Sha3.PPC64LE.Pieces.noMem = true)
    {P : State → State → Prop} {rd wr : State → List Region} (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hok : ∀ x : State, (∃ y, P x y ∨ P y x) → 48 ≤ x.sp.toNat ∧ (∀ X ∈ x.wr, Region.Disjoint ⟨x.sp - 48 + 32, 16⟩ X) ∧
      k.pre ((F (eSt x)).callEntry.withRegions (rd x) (wr x)) ∧ Covers (rd x ++ wr x) (x.rd ++ x.wr) ∧
      Covers (wr x) x.wr)
    (hpub : ∀ x y, P x y → k.pub ((F (eSt x)).callEntry.withRegions (rd x) (wr x))
      ((F (eSt y)).callEntry.withRegions (rd y) (wr y))) :
    RelCT isa P (entryCode mv name code) fun _ _ => True := by
  have inner (x : State) (h : (∃ y, P x y ∨ P y x)) :
      ∃ Q, WP isa (.seq (.block mv) (.call name code)) (eSt x) Q := by
    obtain ⟨_, _, a, b, c⟩ := hok x h
    exact ⟨_, entry_inner hv hdc hmv hF (R := fun _ _ => True) a b c fun _ _ => trivial⟩
  refine RelCT.seq (RelCT.wpDep (F := fun (x x1 : State) => x1 = x.write .r0 x.lr)
    (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem rfl)
    fun x y _ => ⟨WP.cons exec_mflr (WP.block_nil rfl), WP.cons exec_mflr (WP.block_nil rfl)⟩)
    (RelCT.seq (Q := fun _ _ => True) ?_ (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem (P := fun _ _ => True) rfl))
  refine relct_frameN (P := fun a b => True ∧ ∃ x y, P x y ∧ a = x.write .r0 x.lr ∧ b = y.write .r0 y.lr)
    (fun a b ⟨_, x, y, h, ea, eb⟩ => by subst ea eb; exact hsp x y h)
    (fun a b ⟨_, x, y, h, ea, eb⟩ => by
      subst ea eb; exact ⟨inner x ⟨y, .inl h⟩, inner y ⟨x, .inr h⟩⟩) ?_
  refine RelCT.seq (RelCT.wpDep (F := fun (u u' : State) => u' = F u) (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem hnm)
    fun u v _ => ⟨hmv u, hmv v⟩) (RelCT.callEx hv hct fun a b h => ?_)
  obtain ⟨-, u, v, ⟨a', b', ⟨-, x, y, hxy, ea, eb⟩, eu, ev⟩, e₁, e₂⟩ := h
  subst ea eb eu ev e₁ e₂
  obtain ⟨_, _, px, cx, wx⟩ := hok x ⟨y, .inl hxy⟩
  obtain ⟨_, _, py, cy, wy⟩ := hok y ⟨x, .inr hxy⟩
  exact ⟨rd x, wr x, rd y, wr y, px, py, hpub x y hxy, by rw [hF.rd, hF.wr]; exact cx, by rw [hF.wr]; exact wx,
    by rw [hF.rd, hF.wr]; exact cy, by rw [hF.wr]; exact wy⟩

end


/-! ## The frames of the key preparations -/

/-- The link register saved in a frame (through `r0`), then frames saving
`r30` and `r31`, around `body`. -/
abbrev frames3 (body : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (.frame (.push .r30) (.frame (.push .r31) body (.pop .r31))
    (.pop .r30)) (.pop .r0)) (.block [.mtlr .r0]))

/-- The state `frames3`'s body starts in. -/
def f3St (s₀ : State) : State := framed .r31 (framed .r30 (eSt s₀))

theorem f3St_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (f3St s₀).gpr r = s₀.gpr r := eSt_gpr s₀ h
theorem f3St_sp (s₀ : State) : (f3St s₀).sp = s₀.sp - 48 - 48 - 48 := rfl
theorem f3St_rd (s₀ : State) : (f3St s₀).rd = s₀.rd := rfl
theorem f3St_wr (s₀ : State) : (f3St s₀).wr = s₀.wr := rfl

theorem f3St_mem (s₀ : State) (_h : 144 ≤ s₀.sp.toNat) : Frame [below s₀.sp 144] s₀.mem (f3St s₀).mem := by
  have c : ∀ d : Nat, d + 8 ≤ 144 → (below s₀.sp 144).Contains (s₀.sp - 144 + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base _ hd (by omega)
  have e : ∀ d : Nat, d < 144 → s₀.sp - 144 + BitVec.ofNat 64 d = s₀.sp - BitVec.ofNat 64 (144 - d) := fun d hd => by
    bv_omega
  refine Frame.trans (eSt_mem s₀ |>.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) ?_
  · rw [List.mem_singleton] at hr; subst hr
    exact below_sub (by omega) (by omega)
  · show Frame _ _ ((((((eSt s₀).mem.write ((eSt s₀).sp - 48) 8 (eSt s₀).sp).write ((eSt s₀).sp - 48 + 32) 8
      ((eSt s₀).gpr .r30)).write ((eSt s₀).sp - 48 - 48) 8 ((eSt s₀).sp - 48)).write ((eSt s₀).sp - 48 - 48 + 32) 8
      ((framed .r30 (eSt s₀)).gpr .r31)))
    rw [eSt_sp]
    have e1 : s₀.sp - 48 - 48 = s₀.sp - 144 + BitVec.ofNat 64 48 := by bv_omega
    have e2 : s₀.sp - 48 - 48 + 32 = s₀.sp - 144 + BitVec.ofNat 64 80 := by bv_omega
    have e3 : s₀.sp - 48 - 48 - 48 = s₀.sp - 144 + BitVec.ofNat 64 0 := by bv_omega
    have e4 : s₀.sp - 48 - 48 - 48 + 32 = s₀.sp - 144 + BitVec.ofNat 64 32 := by bv_omega
    rw [e4, e3, e2, e1]
    exact ((((Frame.refl _ _).write (List.mem_singleton_self _) _ (c 48 (by omega))).write
      (List.mem_singleton_self _) _ (c 80 (by omega))).write (List.mem_singleton_self _) _ (c 0 (by omega))).write
      (List.mem_singleton_self _) _ (c 32 (by omega))

theorem frames3_slots (sp : Addr) (_h : 144 ≤ sp.toNat) :
    Region.Sub ⟨sp - 48 + 32, 16⟩ (below sp 144) ∧ Region.Sub ⟨sp - 48 - 48 + 32, 16⟩ (below sp 144) ∧
      Region.Sub ⟨sp - 48 - 48 - 48 + 32, 16⟩ (below sp 144) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [Region.Contains] at hx ⊢ <;> bv_omega

/-- `frames3`: the body's memory, and the registers our caller expects us to keep. -/
theorem frames3_wp {body : Prog isa} {s₀ : State} {R : Mem → Prop}
    (hsp : 144 ≤ s₀.sp.toNat) (hd : ∀ X ∈ s₀.wr, (below s₀.sp 144).Disjoint X) (hn : sdepth body + 144 < 2 ^ 64)
    (hb : WP isa body (f3St s₀) fun s' => (∀ r ∈ preserved, r ≠ .r30 → r ≠ .r31 → s'.gpr r = s₀.gpr r) ∧
      R s'.mem) :
    WP isa (frames3 body) s₀ fun s' => PPC64LE.target.abiPreserved s₀ s' ∧ R s'.mem := by
  obtain ⟨sl1, sl2, sl3⟩ := frames3_slots s₀.sp hsp
  have h1 : 48 ≤ (s₀.sp - 48).toNat := by bv_omega
  have h2 : 48 ≤ (s₀.sp - 48 - 48).toNat := by bv_omega
  refine WP.seq (WP.cons exec_mflr (WP.block_nil ?_))
  refine WP.seq (WP.frameRegAny (r := .r0) (s₀ := s₀.write .r0 s₀.lr) (by show 48 ≤ s₀.sp.toNat; omega)
    (fun X hX => (hd X hX).sub_left sl1) ?_ (by simp only [sdepth, Instr.frameBytes]; omega))
  refine WP.frameRegAny (r := .r30) (by exact h1) (fun X hX => (hd X hX).sub_left sl2) ?_
    (by simp only [sdepth, Instr.frameBytes]; omega)
  refine WP.frameRegAny (r := .r31) (by exact h2) (fun X hX => (hd X hX).sub_left sl3) ?_ (by omega)
  refine WP.mono hb fun s' ⟨hk, hR⟩ => WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, hR⟩)
  · simp only [State.write]
    by_cases h0 : r = .r0
    · subst h0; simp [preserved] at hr
    · by_cases h30 : r = .r30
      · subst h30; simp [framed]
      · by_cases h31 : r = .r31
        · subst h31; simp [framed]
        · simp only [h0, h30, h31, ite_false]
          exact hk r hr h30 h31
  · simp [State.write, framed]

/-- Two runs of `frames3` leak the same if the runs of its body do, and the
body runs from the states each starts in. -/
theorem frames3_tr {body : Prog isa} {P : State → State → Prop} (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hok : ∀ x : State, (∃ y, P x y ∨ P y x) → 144 ≤ x.sp.toNat ∧ (∀ X ∈ x.wr, (below x.sp 144).Disjoint X) ∧
      ∃ Q, WP isa body (f3St x) Q)
    (hn : sdepth body + 144 < 2 ^ 64)
    (hb : RelCT isa (fun u v => ∃ x y, P x y ∧ u = f3St x ∧ v = f3St y) body fun _ _ => True) :
    RelCT isa P (frames3 body) fun _ _ => True := by
  have w31 (x : State) (hx : ∃ y, P x y ∨ P y x) :
      ∃ Q, WP isa (.frame (.push .r31) body (.pop .r31)) (framed .r30 (eSt x)) Q := by
    obtain ⟨hsp, hd, Q, hq⟩ := hok x hx
    obtain ⟨-, -, sl3⟩ := frames3_slots x.sp hsp
    exact ⟨_, WP.frameRegAny (r := .r31) (Q := fun _ => True) (by show 48 ≤ (x.sp - 48 - 48).toNat; bv_omega)
      (fun X hX => (hd X hX).sub_left sl3) (WP.mono hq fun _ _ => trivial) (by omega)⟩
  have w30 (x : State) (hx : ∃ y, P x y ∨ P y x) :
      ∃ Q, WP isa (.frame (.push .r30) (.frame (.push .r31) body (.pop .r31)) (.pop .r30)) (eSt x) Q := by
    obtain ⟨hsp, hd, -⟩ := hok x hx
    obtain ⟨-, sl2, -⟩ := frames3_slots x.sp hsp
    obtain ⟨Q, hq⟩ := w31 x hx
    exact ⟨_, WP.frameRegAny (r := .r30) (Q := fun _ => True) (by show 48 ≤ (x.sp - 48).toNat; bv_omega)
      (fun X hX => (hd X hX).sub_left sl2) (WP.mono hq fun _ _ => trivial)
      (by simp only [sdepth, Instr.frameBytes]; omega)⟩
  refine RelCT.seq (RelCT.wpDep (F := fun (x x1 : State) => x1 = x.write .r0 x.lr)
    (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem rfl)
    fun x y _ => ⟨WP.cons exec_mflr (WP.block_nil rfl), WP.cons exec_mflr (WP.block_nil rfl)⟩)
    (RelCT.seq (Q := fun _ _ => True) ?_ (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem (P := fun _ _ => True) rfl))
  refine relct_frameN (P := fun a b => True ∧ ∃ x y, P x y ∧ a = x.write .r0 x.lr ∧ b = y.write .r0 y.lr)
    (fun a b ⟨_, x, y, h, ea, eb⟩ => by subst ea eb; exact hsp x y h)
    (fun a b ⟨_, x, y, h, ea, eb⟩ => by subst ea eb; exact ⟨w30 x ⟨y, .inl h⟩, w30 y ⟨x, .inr h⟩⟩) ?_
  refine relct_frameN (fun u v ⟨a, b, ⟨_, x, y, h, ea, eb⟩, eu, ev⟩ => by
      subst ea eb eu ev; show x.sp - 48 = y.sp - 48; rw [hsp x y h])
    (fun u v ⟨a, b, ⟨_, x, y, h, ea, eb⟩, eu, ev⟩ => by
      subst ea eb eu ev; exact ⟨w31 x ⟨y, .inl h⟩, w31 y ⟨x, .inr h⟩⟩) ?_
  refine relct_frameN (fun u v ⟨a, b, ⟨c, d, ⟨_, x, y, h, ea, eb⟩, ec, ed⟩, eu, ev⟩ => by
      subst ea eb ec ed eu ev; show x.sp - 48 - 48 = y.sp - 48 - 48; rw [hsp x y h])
    (fun u v ⟨a, b, ⟨c, d, ⟨_, x, y, h, ea, eb⟩, ec, ed⟩, eu, ev⟩ => by
      subst ea eb ec ed eu ev; exact ⟨(hok x ⟨y, .inl h⟩).2.2, (hok y ⟨x, .inr h⟩).2.2⟩)
    (RelCT.mono hb (fun u v ⟨a, b, ⟨c, d, ⟨e, f, ⟨_, x, y, h, ea, eb⟩, ec, ed⟩, ee, ef⟩, eu, ev⟩ => by
      subst ea eb ec ed ee ef eu ev; exact ⟨x, y, h, rfl, rfl⟩) fun _ _ h => h)

end VG.Proof.MlDsa.PPC64LE
