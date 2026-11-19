module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Sse2.Columns
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Mont.X86.Sse2
meta import VerifiedGarbage.Impl.Mont.X86.Sse2
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! ### `Mont.X86.Sse2.TimeTaint`, which this module and modules that import it used -/

section

/-! # The columns and the reduction leak only public data

Each runs with the parameters read-only: the columns inside the MCDT frame,
the parameters 12 bytes above `esp` (`colTaint`), and the reduction after it,
the parameters at `esp` (`argTaint [] 28`).
-/

@[expose] public section
namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86.Sse2

/-- Inside the MCDT frame: `esp` public, and the 28 bytes of parameters, 12
bytes above `esp`, public and never written (after 8 bytes treated as two
return addresses). -/
def colTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, stk := [none, none], argLen := 32 }

theorem columns_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree colTaint) columns :=
  VG.Taint.constantTime (A := sseTaint) colTaint (fun _ _ _ _ H => H) (by taint_decide)

/-- The reduction after the columns. -/
def rest : Prog isa := seqs [subM, .block mask, select]

theorem rest_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (argTaint [] 28)) rest :=
  VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 28) (fun _ _ _ _ H => H) (by taint_decide)

/-- The callee-saved registers' loads, at `esp`. -/
theorem restore_relCT :
    RelCT isa (fun x y => x.gpr .esp = y.gpr .esp) (.block restoreRegs) fun _ _ => True :=
  VG.RelCT.taint (A := VG.X86.taint) (VG.X86.τr [.esp]) (fun _ _ h => VG.X86.agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

/-- `vg_rsa_mont_mul_at`'s parameters, from the arguments above `esp`. -/
theorem atParams_relCT :
    RelCT isa (fun x y => x.gpr .esp = y.gpr .esp) (.block atParams) fun _ _ => True :=
  VG.RelCT.taint (A := VG.X86.taint) (VG.X86.τr [.esp]) (fun _ _ h => VG.X86.agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

/-- After the callee-saved registers' push: `esp` public, and the 20 bytes of
arguments above the return address, 16 bytes above `esp`, public and never
written. -/
def prTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, stk := [none, none, none, none], argLen := 24 }

/-- `vg_rsa_mont_mul`'s parameters, from the arguments and the header. -/
theorem preparedParams_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree prTaint) (.block preparedParams) :=
  VG.Taint.constantTime (A := VG.X86.taint) prTaint (fun _ _ _ _ H => H) (by taint_decide)

end VG.Proof.Mont.X86.Sse2

end

end

/-! ### `Mont.X86.Sse2.Time`, which this module and modules that import it used -/

section

/-! # `body params` leaks only public data

Two runs from states with the same numbers (`BPair`) leak the same
(`body_relCT`): the frames' pushes and pops leak addresses of `esp`; the
columns and the reduction, which write only the working space, leak the same
as they do with the rest read-only (`relCT_nar`), where the taint analysis
reads the parameters as public (`columns_constantTime`, `rest_constantTime`);
the parameters, from the numbers, are the same in both runs.
-/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Sse2/RelFrame.lean`, which only this module imported.
section

/-! # Relating two runs through frames and narrowed permissions

`relCT_of_wp`: two runs leak the same, and their final states are related by
what each satisfies by correctness. `RelCT.frameOf`: a frame whose push and pop
leak only addresses of `esp`, around a body whose runs leak the same, leaves
`esp` the same (frames of registers, `push_frame`, and MCDT frames,
`mcdt_frame`). `relCT_nar`: code that writes only the working space `⟨W, L⟩`
leaks the same as it does with only that region writable and every other
readable (`nar`), where a taint analysis can treat the rest as read-only.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86

/-- Two runs leak the same (`h`); their final states are related by what each
satisfies by correctness. -/
theorem relCT_of_wp {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hw : ∀ s₁ s₂, P s₁ s₂ → ∃ F₁ F₂ : State → Prop, WP isa c s₁ F₁ ∧ WP isa c s₂ F₂ ∧
      ∀ u₁ u₂, F₁ u₁ → F₂ u₂ → Q u₁ u₂) :
    RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨F₁, F₂, ⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩, hq⟩ := hw _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht, hq _ _ g₁ g₂⟩

/-- A frame of registers' push, for runs with the same `esp`. -/
theorem push_frame {rs : List Reg} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp) :
    ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push (.push rs) s₁ = some a₁ → isa.push (.push rs) s₂ = some a₂ →
      isa.addrs (.push rs) s₁ = isa.addrs (.push rs) s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len := by
  intro s₁ s₂ a₁ a₂ hp h₁ h₂
  obtain ⟨-, -, -, rfl⟩ := push_some h₁
  obtain ⟨-, -, -, rfl⟩ := push_some h₂
  have e := hsp _ _ hp
  exact ⟨by simp only [addrs, e], by rw [pushed_esp, pushed_esp, e], by rw [pushed_wr, pushed_wr]; rfl⟩

theorem pop_addrs (r : Reg) (k : Nat) : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp →
    isa.addrs (.pop r k) b₁ = isa.addrs (.pop r k) b₂ := by
  intro b₁ b₂ h; simp only [addrs, h]

/-- `s` with only the working space `⟨W, L⟩` writable, and every region readable. -/
def nar (s : State) (W : Addr) (L : Nat) : State := s.withRegions (s.rd ++ s.wr) [⟨W, L⟩]

theorem nar_gpr (s : State) (W : Addr) (L : Nat) : (nar s W L).gpr = s.gpr := rfl
theorem nar_mem (s : State) (W : Addr) (L : Nat) : (nar s W L).mem = s.mem := rfl
theorem nar_wr (s : State) (W : Addr) (L : Nat) : (nar s W L).wr = [⟨W, L⟩] := rfl
theorem nar_rdwr (s : State) (W : Addr) (L : Nat) :
    (nar s W L).rd ++ (nar s W L).wr = s.rd ++ s.wr ++ [⟨W, L⟩] := rfl

/-- A run from `s` is one from `nar s W L` when the code runs from there. -/
theorem nar_trace {c : Prog isa} {s t : State} {W : Addr} {L : Nat} (hw : (⟨W, L⟩ : Region) ∈ s.wr)
    {Q : State → Prop} (H : WP isa c (nar s W L) Q) {tr : List Leak} (E : Exec isa c s tr t) :
    ∃ u, Exec isa c (nar s W L) tr u := by
  obtain ⟨tr', u, EU, _⟩ := H
  have read : Covers ((s.rd ++ s.wr) ++ [⟨W, L⟩]) (s.rd ++ s.wr) := fun a n ⟨r, hr, hc⟩ =>
    ⟨r, by
      rcases List.mem_append.mp hr with h | h
      · exact h
      · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ hw, hc⟩
  have write : Covers [⟨W, L⟩] s.wr := fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hw, hc⟩
  have EW := VG.X86.Exec.widen EU read write
  simp only [nar, State.withRegions_withRegions, State.withRegions_self] at EW
  obtain ⟨rfl, _⟩ := Exec.det E EW
  exact ⟨u, EU⟩

/-- Code that runs from the narrowed states leaks the same from the states,
when it is constant-time from the narrowed states. -/
theorem relCT_nar {c : Prog isa} {P Pub : State → State → Prop} {W : Addr} {L : Nat}
    (hct : ConstantTime isa (fun _ => True) Pub c)
    (h : ∀ s₁ s₂, P s₁ s₂ → (⟨W, L⟩ : Region) ∈ s₁.wr ∧ (⟨W, L⟩ : Region) ∈ s₂.wr ∧
      (∃ Q, WP isa c (nar s₁ W L) Q) ∧ (∃ Q, WP isa c (nar s₂ W L) Q) ∧ Pub (nar s₁ W L) (nar s₂ W L)) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨w₁, w₂, ⟨_, H₁⟩, ⟨_, H₂⟩, hpub⟩ := h _ _ hp
  obtain ⟨_, E₁⟩ := nar_trace w₁ H₁ e₁
  obtain ⟨_, E₂⟩ := nar_trace w₂ H₂ e₂
  exact ⟨hct _ _ _ _ _ _ trivial trivial hpub E₁ E₂, trivial⟩

end VG.Proof.Mont.X86.Sse2
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar)

theorem pvals_eq {V V' : Nat → BitVec 32} {W : Addr} {N S mo inv o a b : Nat}
    (h : PVals V W N S mo inv o a b) (h' : PVals V' W N S mo inv o a b) : ∀ i < 7, V i = V' i := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  match i, hi with
  | 0, _ => exact h.a.trans h'.a.symm
  | 1, _ => exact h.b.trans h'.b.symm
  | 2, _ => exact h.mo.trans h'.mo.symm
  | 3, _ => exact h.o.trans h'.o.symm
  | 4, _ => exact h.s.trans h'.s.symm
  | 5, _ => exact h.inv.trans h'.inv.symm
  | 6, _ => exact h.n4.trans h'.n4.symm

/-- `n` bytes past the working space are apart from it. -/
theorem disjoint_ws {base W : Addr} {n L : Nat} (h : ∀ d < n, L ≤ ofs W (base + BitVec.ofNat 64 d)) :
    Region.Disjoint ⟨base, n⟩ ⟨W, L⟩ := by
  intro x hx hw
  have e : base + BitVec.ofNat 64 (x - base).toNat = x := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [Region.Contains] at hx hw
  have := h (x - base).toNat (by omega_arith)
  rw [e] at this
  simp only [ofs] at this
  omega_arith

/-- The address of a parameter's byte. -/
theorem param_addr {sp : BitVec 32} {d i j : Nat} (hfit : sp.toNat + d + 28 ≤ 2 ^ 32) (hi : i < 7) (hj : j < 4) :
    (sp + BitVec.ofNat 32 (d + 4 * i)).setWidth 64 + BitVec.ofNat 64 j =
      sp.setWidth 64 + BitVec.ofNat 64 (d + 4 * i + j) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- A byte of a parameter. -/
theorem Params.byte {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (P : Params s W L V d)
    (hfit : (s.gpr .esp).toNat + d + 28 ≤ 2 ^ 32) {i j : Nat} (hi : i < 7) (hj : j < 4) :
    s.mem ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (d + 4 * i + j)) = (V i).extractLsb' (8 * j) 8 := by
  have h := P.read i hi
  simp only [readSrc, State.load32] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h, ← Mem.readW_byte _ _ hj]
    simp only [State.ea, prm, at_]
    rw [param_addr hfit hi hj]
  · cases h

/-- The parameters past the working space. -/
theorem Params.disjoint {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} (P : Params s W L V 0)
    (hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨W, L⟩ := by
  refine disjoint_ws fun d hd => ?_
  have h := P.far (d / 4) (by omega_arith) (d % 4) (Nat.mod_lt _ (by decide))
  simp only [State.ea, prm, at_] at h
  rw [param_addr (d := 0) (by omega_arith) (by omega_arith) (Nat.mod_lt _ (by decide))] at h
  rwa [show 0 + 4 * (d / 4) + d % 4 = d by omega_arith] at h

/-- The argument `i` of the frame of parameters, the parameter `i + 1`. -/
theorem Params.argWord {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} (P : Params s W L V 0) {i : Nat}
    (hi : i < 6) : arg s i = V (i + 1) := by
  have h := P.read (i + 1) (by omega_arith)
  simp only [readSrc, State.load32] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only [X86.arg, X86.argAddr, State.ea, prm, at_]
    rw [show 0 + 4 * (i + 1) = 4 + 4 * i by omega_arith]
  · cases h

theorem narWs {s : State} {W : Addr} {L : Nat} (h : Ws s W L) : Ws (nar s W L) W L :=
  ⟨List.mem_singleton_self _, h.nowrap⟩

theorem narParams {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (P : Params s W L V d) :
    Params (nar s W L) W L V d :=
  P.transport (fun _ _ => rfl) (fun _ _ _ _ => rfl) fun _ ⟨r, hr, hc⟩ => ⟨r, by rw [nar_rdwr]; exact List.mem_append_left _ hr, hc⟩

/-! ## The columns -/

theorem agree_col {x y : State} (sp : x.gpr .esp = y.gpr .esp) (fx : (x.gpr .esp).toNat + 40 ≤ 2 ^ 32)
    (fy : (y.gpr .esp).toNat + 40 ≤ 2 ^ 32)
    (dx : ∀ r ∈ x.wr, Region.Disjoint ⟨X86.Taint.argByte x 8, 32⟩ r)
    (dy : ∀ r ∈ y.wr, Region.Disjoint ⟨X86.Taint.argByte y 8, 32⟩ r)
    (hm : ∀ k, 12 ≤ k → k < 40 → x.mem (X86.Taint.argByte x k) = y.mem (X86.Taint.argByte y k)) :
    X86.Taint.Agree colTaint x y := by
  have wf : ∀ z : State, (z.gpr .esp).toNat + 40 ≤ 2 ^ 32 →
      (∀ r ∈ z.wr, Region.Disjoint ⟨X86.Taint.argByte z 8, 32⟩ r) → X86.Taint.Wf colTaint z := fun z hz dz =>
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨by show _ + 8 + 32 ≤ _; omega_arith, dz⟩, fun _ h => (List.not_mem_nil h).elim,
      by show _ + 8 < _; omega_arith, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0)⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf x fx dx, wf y fy dy,
    X86.Taint.slotsOk_empty, X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [colTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · have hk' : k < 32 := hk
    exact hm (8 + k) (by omega_arith) (by omega_arith)

section
variable {W : Addr} {L N S mo inv o a b : Nat}

/-- The kernel's entry in two runs. -/
def KPair (W : Addr) (L N S mo inv o a b : Nat) (s₁ s₂ : State) : Prop :=
  ∃ V V', KReady s₁ W L N S mo inv o a b V ∧ KReady s₂ W L N S mo inv o a b V' ∧ s₁.gpr .esp = s₂.gpr .esp

/-- A byte of the parameters, from the MCDT frame's bottom. -/
theorem pushed_byte {s : State} {V : Nat → BitVec 32} (K : KReady s W L N S mo inv o a b V) {k : Nat}
    (h12 : 12 ≤ k) (hk : k < 40) :
    (mcdtPushed .eax s).mem (X86.Taint.argByte (mcdtPushed .eax s) k) =
      (V ((k - 12) / 4)).extractLsb' (8 * ((k - 12) % 4)) 8 := by
  have hlo := K.lo
  have hhi := K.hi
  have hs := (s.gpr .esp).isLt
  have e : X86.Taint.argByte (mcdtPushed .eax s) k = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 k := by
    simp only [X86.Taint.argByte, mcdtPushed_esp .eax s (by decide)]
  have e' : (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 k =
      (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (0 + 4 * ((k - 12) / 4) + (k - 12) % 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl]
    omega_arith
  rw [e, pushed_other s hlo (fun j hj h => ?_), e', K.prm.byte (by omega_arith) (by omega_arith) (Nat.mod_lt _ (by decide))]
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
  rw [show (12 : BitVec 32).toNat = 12 from rfl] at h'
  omega_arith

/-- The columns, from the MCDT frame's push in two runs. -/
theorem columns_relCT :
    RelCT isa (fun x y => ∃ s₁ s₂, KPair W L N S mo inv o a b s₁ s₂ ∧ isa.push (.mcdtEnter .eax) s₁ = some x ∧
      isa.push (.mcdtEnter .eax) s₂ = some y) columns fun _ _ => True := by
  refine relCT_nar (W := W) (L := L) columns_constantTime ?_
  rintro x y ⟨s₁, s₂, ⟨V, V', K₁, K₂, sp⟩, h₁, h₂⟩
  obtain ⟨-, rfl⟩ := mcdt_push_eq h₁
  obtain ⟨-, rfl⟩ := mcdt_push_eq h₂
  obtain ⟨w₁, P₁, i₁, -⟩ := pushed_ready K₁
  obtain ⟨w₂, P₂, i₂, -⟩ := pushed_ready K₂
  have e₁ := mcdtPushed_esp .eax s₁ (by decide)
  have e₂ := mcdtPushed_esp .eax s₂ (by decide)
  have fit : ∀ {s : State} {V : Nat → BitVec 32}, KReady s W L N S mo inv o a b V →
      ((mcdtPushed .eax s).gpr .esp).toNat + 40 ≤ 2 ^ 32 := fun {s} _ K => by
    have := K.lo; have := K.hi
    rw [mcdtPushed_esp .eax s (by decide), BitVec.toNat_sub, show (12 : BitVec 32).toNat = 12 from rfl]
    omega_arith
  have dis : ∀ {s : State} {V : Nat → BitVec 32}, KReady s W L N S mo inv o a b V →
      ∀ r ∈ (nar (mcdtPushed .eax s) W L).wr, Region.Disjoint ⟨X86.Taint.argByte (nar (mcdtPushed .eax s) W L) 8, 32⟩ r :=
    fun {s} _ K r hr => by
      rw [nar_wr, List.mem_singleton] at hr; subst hr
      refine disjoint_ws fun d hd => ?_
      simp only [X86.Taint.argByte, nar_gpr, mcdtPushed_esp .eax s (by decide)]
      rw [Offset.add_add]
      exact K.far _ (by omega_arith)
  refine ⟨w₁.wr, w₂.wr, ⟨_, columns_ok K₁.ly K₁.pv i₁ (by show 0 < (mcdtPushed .eax s₁).mcdt; rw [mcdtPushed_mcdt]; omega_arith) (narWs w₁) (narParams P₁)⟩,
    ⟨_, columns_ok K₂.ly K₂.pv i₂ (by show 0 < (mcdtPushed .eax s₂).mcdt; rw [mcdtPushed_mcdt]; omega_arith) (narWs w₂) (narParams P₂)⟩,
    agree_col (by rw [nar_gpr, nar_gpr, e₁, e₂, sp]) (fit K₁) (fit K₂) (dis K₁) (dis K₂) fun k h12 hk => ?_⟩
  show (mcdtPushed .eax s₁).mem (X86.Taint.argByte (mcdtPushed .eax s₁) k) =
    (mcdtPushed .eax s₂).mem (X86.Taint.argByte (mcdtPushed .eax s₂) k)
  rw [pushed_byte K₁ h12 hk, pushed_byte K₂ h12 hk, pvals_eq K₁.pv K₂.pv _ (by omega_arith)]

/-- After the MCDT frame, in two runs. -/
def MPair (W : Addr) (L N S mo inv o a b : Nat) (v₁ v₂ : State) : Prop :=
  ∃ s₁ s₂ V V', KReady s₁ W L N S mo inv o a b V ∧ KReady s₂ W L N S mo inv o a b V' ∧
    s₁.gpr .esp = s₂.gpr .esp ∧ Mid s₁ W L N S mo inv o a b V v₁ ∧ Mid s₂ W L N S mo inv o a b V' v₂

theorem frame_relCT :
    RelCT isa (KPair W L N S mo inv o a b) (.frame (.mcdtEnter .eax) columns .mcdtLeave)
      (MPair W L N S mo inv o a b) := by
  refine relCT_of_wp ((RelCT.frameOf (mcdt_frame fun _ _ h => ?_) mcdtLeave_addrs columns_relCT).mono
    (fun _ _ h => h) fun _ _ _ => trivial) ?_
  · obtain ⟨_, _, _, _, h⟩ := h; exact h
  · rintro s₁ s₂ ⟨V, V', K₁, K₂, sp⟩
    exact ⟨_, _, frame_ok K₁, frame_ok K₂, fun _ _ M₁ M₂ => ⟨s₁, s₂, V, V', K₁, K₂, sp, M₁, M₂⟩⟩

theorem rest_relCT : RelCT isa (MPair W L N S mo inv o a b) rest fun _ _ => True := by
  refine relCT_nar (W := W) (L := L) rest_constantTime ?_
  rintro v₁ v₂ ⟨s₁, s₂, V, V', K₁, K₂, sp, M₁, M₂⟩
  have out : ∀ {s v : State} {V : Nat → BitVec 32}, KReady s W L N S mo inv o a b V →
      Mid s W L N S mo inv o a b V v → ArgsOut 6 (nar v W L) := fun {s v} _ K M => by
    have hhi := K.hi
    refine ⟨by rw [nar_gpr, M.esp]; omega_arith, fun r hr => ?_⟩
    rw [nar_wr, List.mem_singleton] at hr; subst hr
    exact M.prm.disjoint (by rw [M.esp]; omega_arith)
  refine ⟨M₁.ws.wr, M₂.ws.wr,
    ⟨_, reduction_ok K₁.ly K₁.pv (narWs M₁.ws) (narParams M₁.prm) (by rw [nar_mem, M₁.modulus]; exact M₁.bound)⟩,
    ⟨_, reduction_ok K₂.ly K₂.pv (narWs M₂.ws) (narParams M₂.prm) (by rw [nar_mem, M₂.modulus]; exact M₂.bound)⟩,
    agree_argTaint (fun _ h => (List.not_mem_nil h).elim) (by rw [nar_gpr, nar_gpr, M₁.esp, M₂.esp, sp])
      (out K₁ M₁) (out K₂ M₂) fun i hi => ?_⟩
  have hfit : ∀ {s v : State} {V : Nat → BitVec 32}, KReady s W L N S mo inv o a b V →
      Mid s W L N S mo inv o a b V v → (v.gpr .esp).toNat + 28 ≤ 2 ^ 32 := fun {s v} _ K M => by
    rw [M.esp]; exact K.hi
  rw [show arg (nar v₁ W L) i = arg v₁ i from rfl, show arg (nar v₂ W L) i = arg v₂ i from rfl,
    M₁.prm.argWord hi, M₂.prm.argWord hi, pvals_eq K₁.pv K₂.pv _ (by omega_arith)]

theorem kernel_relCT : RelCT isa (KPair W L N S mo inv o a b) kernel fun _ _ => True :=
  RelCT.seq frame_relCT rest_relCT

/-! ## The function -/

/-- What `body params` takes of a state, at fixed numbers. -/
structure Ready (params : List Instr) (W : Addr) (L N S mo inv o a b : Nat) (s : State) : Prop where
  entry : Entry s W L
  ly : Lay L N S mo inv o a b
  par : WP isa (.block params) (pushed rs4 s) (ParamsPost s W N S mo inv o a b)
  inv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0
  bLt : val32 s.mem W b N < val32 s.mem W mo N

/-- Two runs of `body params` with the same numbers and `esp`. -/
def BPair (params : List Instr) (W : Addr) (L N S mo inv o a b : Nat) (s₁ s₂ : State) : Prop :=
  Ready params W L N S mo inv o a b s₁ ∧ Ready params W L N S mo inv o a b s₂ ∧ s₁.gpr .esp = s₂.gpr .esp

/-- After `params`, in two runs. -/
def PPair (params : List Instr) (W : Addr) (L N S mo inv o a b : Nat) (u₁ u₂ : State) : Prop :=
  ∃ s₁ s₂, BPair params W L N S mo inv o a b s₁ s₂ ∧ ParamsPost s₁ W N S mo inv o a b u₁ ∧
    ParamsPost s₂ W N S mo inv o a b u₂

theorem body_relCT {params : List Instr} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BPair params W L N S mo inv o a b s₁ s₂)
    (hpar : RelCT isa (fun x y => ∃ s₁ s₂, P s₁ s₂ ∧ x = pushed rs4 s₁ ∧ y = pushed rs4 s₂)
      (.block params) fun _ _ => True) :
    RelCT isa P (body params) fun _ _ => True := by
  unfold body
  refine (RelCT.frameOf (R := fun _ _ => True) (push_frame fun _ _ h => (hP _ _ h).2.2) (pop_addrs .ebx 4) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  simp only [seqs]
  refine RelCT.seq (R := PPair params W L N S mo inv o a b) ?_
    (RelCT.seq (R := fun (x y : State) => x.gpr .esp = y.gpr .esp) ?_ restore_relCT)
  · refine relCT_of_wp (hpar.mono ?_ fun _ _ _ => trivial) ?_
    · rintro x y ⟨s₁, s₂, B, h₁, h₂⟩
      exact ⟨s₁, s₂, B, (push_some h₁).2.2.2, (push_some h₂).2.2.2⟩
    · rintro x y ⟨s₁, s₂, B', h₁, h₂⟩
      have B := hP _ _ B'
      rw [(push_some h₁).2.2.2, (push_some h₂).2.2.2]
      exact ⟨_, _, B.1.par, B.2.1.par, fun _ _ H₁ H₂ => ⟨s₁, s₂, B, H₁, H₂⟩⟩
  · refine RelCT.frameOf (push_frame ?_) (pop_addrs .eax 7)
      ((kernel_relCT (W := W) (L := L) (N := N) (S := S) (mo := mo) (inv := inv) (o := o) (a := a) (b := b)).mono ?_
        fun _ _ _ => trivial)
    · rintro u₁ u₂ ⟨s₁, s₂, B, H₁, H₂⟩
      rw [H₁.2.1, H₂.2.1, B.2.2]
    · rintro x y ⟨u₁, u₂, ⟨s₁, s₂, B, H₁, H₂⟩, h₁, h₂⟩
      rw [(push_some h₁).2.2.2, (push_some h₂).2.2.2]
      exact ⟨_, _, kernel_ready B.1.entry B.1.ly B.1.inv B.1.bLt H₁,
        kernel_ready B.2.1.entry B.1.ly B.2.1.inv B.2.1.bLt H₂,
        by rw [pushed_esp, pushed_esp, H₁.2.1, H₂.2.1, B.2.2]⟩

end

end VG.Proof.Mont.X86.Sse2

end

end

/-! ### `Mont.X86.Sse2.At`, which only this module used -/

section

/-! ### `Mont.X86.Sse2.AtABI`, which only this module used -/

section

/-! # `vg_rsa_mont_mul_at`'s entry

`AtABI s`: the facts of `mulContract abi 56`'s precondition; from them, the
stack (`Entry`), the layout (`Lay`) and the parameters `atParams` computes
(`atParams_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

structure AtABI (s : State) : Prop where
  stackLo : 56 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 36⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  argScratch : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  stkScratch : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  stkArgs : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  pos : 0 < (arg s 2).toNat
  mo_le : (arg s 3).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  inv_le : (arg s 4).toNat + 4 ≤ 8 * (arg s 1).toNat
  s_le : (arg s 5).toNat + scratchBytes (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  o_le : (arg s 6).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  a_le : (arg s 7).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  b_le : (arg s 8).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  smo : Apart (arg s 3).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sinv : Apart (arg s 4).toNat 4 ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  so : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sa : Apart (arg s 7).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sb : Apart (arg s 8).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  omo : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 3).toNat, 8 * (arg s 2).toNat)
  oinv : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 4).toNat, 4)
  inv : (numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat) *
    numAt s.mem (wsOf s) (arg s 4).toNat 4 + 1) % 2 ^ 32 = 0
  bLt : numAt s.mem (wsOf s) (arg s 8).toNat (8 * (arg s 2).toNat) <
    numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat)

theorem atAbi_of {s : State} (h : (Proof.Rsa.MontMul.mulContract abi 56).pre s) : AtABI s := by
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem AtABI.ws_toNat {s : State} (_ : AtABI s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem AtABI.ws {s : State} (A : AtABI s) : Ws s (wsOf s) (lenOf s) :=
  ⟨by rw [A.wr]; exact List.mem_singleton_self _, by rw [A.ws_toNat]; exact A.bound⟩

theorem AtABI.entry {s : State} (A : AtABI s) : Entry s (wsOf s) (lenOf s) := by
  have hlo := A.stackLo
  have hhi := A.stackBound
  refine ⟨hlo, by omega_arith, A.ws, fun j hj => ofs_far fun hc => ?_⟩
  have := (s.gpr .esp).isLt
  by_cases h56 : j < 56
  · refine A.stkScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith
  · refine A.retScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith

/-- The width `N = 2 n` of 32-bit words. -/
abbrev nAt (s : State) : Nat := 2 * (arg s 2).toNat

theorem AtABI.lay {s : State} (A : AtABI s) :
    Lay (lenOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat (arg s 7).toNat
      (arg s 8).toNat := by
  have := A.s_le; have := A.mo_le; have := A.inv_le; have := A.a_le; have := A.b_le; have := A.o_le
  have := A.smo; have := A.sinv; have := A.sa; have := A.sb; have := A.so; have := A.omo; have := A.oinv
  have := A.pos; have := A.bound
  simp only [scratchBytes, Apart] at *
  constructor <;> simp only [nAt, lenOf] <;> omega_arith

/-- The arguments, read from the state after the registers' push. -/
theorem AtABI.readArg {s : State} (A : AtABI s) {t : State} (hesp : t.gpr .esp = s.gpr .esp - 16)
    (hrd : t.rd = s.rd) (hmem : Frame [below (s.gpr .esp) 16] s.mem t.mem) {i : Nat} (hi : i < 9) :
    readSrc t (.mem (atArg i)) = some (arg s i) := by
  have hb := A.stackBound
  have hlo := A.stackLo
  have ea : t.ea (atArg i) = argAddr s i := by
    simp only [State.ea, atArg, at_, hesp, argAddr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (16 : BitVec 32).toNat = 16 from rfl]
    have := (s.gpr .esp).isLt
    omega_arith
  have hin : InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
    rw [hrd, A.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega_arith
  show t.load32 (t.ea (atArg i)) = _
  rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd hin h]
  refine congrArg some (Mem.readW_congr fun j hj => hmem _ fun r hr h => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  have := (s.gpr .esp).isLt
  simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat] at h
  omega_arith

theorem upd_trans {t t₁ t₂ : State} {r : Reg} {v₁ v₂ : BitVec 32} (u₁ : Upd t t₁ r v₁) (u₂ : Upd t₁ t₂ r v₂) :
    Upd t t₂ r v₂ :=
  ⟨u₂.gpr, fun q h => (u₂.other q h).trans (u₁.other q h), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.syms.trans u₁.syms⟩

/-- `atPtr r i`: `r = ws + ` the offset in argument `i`. -/
theorem atPtr_ok {s t : State} {r : Reg} (hr : r ≠ .esp) {i : Nat} {is : List Instr} {Q : State → Prop}
    (h0 : readSrc t (.mem (atArg 0)) = some (arg s 0)) (hi : readSrc t (.mem (atArg i)) = some (arg s i))
    (k : ∀ t', Upd t t' r (arg s 0 + arg s i) → WP isa (.block is) t' Q) :
    WP isa (.block (atPtr r i ++ is)) t Q := by
  simp only [atPtr, List.cons_append, List.nil_append]
  refine wp_movS h0 fun t₁ u₁ _ => wp_addS (by rw [Dynamic.readSrc_upd u₁ (Ne.symm hr)]; exact hi)
    fun t₂ u₂ _ => k t₂ ?_
  rw [u₁.gpr] at u₂
  exact upd_trans u₁ u₂

/-- `atParams`: the kernel's parameters from the arguments. -/
theorem atParams_ok {s : State} (A : AtABI s) :
    WP isa (.block atParams) (pushed rs4 s) fun t =>
      PVals (vals t) (wsOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
        (arg s 7).toNat (arg s 8).toNat ∧
      t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧ t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr := by
  have hlo := A.stackLo
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl] at F1
  have e1 : (pushed rs4 s).gpr .esp = s.gpr .esp - 16 := by rw [pushed_esp]; rfl
  have rd : ∀ t, t.gpr .esp = s.gpr .esp - 16 → t.rd = s.rd → t.mem = (pushed rs4 s).mem →
      ∀ i < 9, readSrc t (.mem (atArg i)) = some (arg s i) := fun t he hr hm i hi =>
    A.readArg he hr (by rw [hm]; exact F1) hi
  let St : State → Prop := fun t => t.gpr .esp = s.gpr .esp - 16 ∧ t.rd = s.rd ∧
    t.mem = (pushed rs4 s).mem ∧ t.wr = (pushed rs4 s).wr
  have st : ∀ {t t' : State} {r : Reg} {v : BitVec 32}, St t → Upd t t' r v → r ≠ .esp → St t' :=
    fun ⟨a, b, c, d⟩ u hr => ⟨by rw [u.other _ (Ne.symm hr), a], by rw [u.rd, b], by rw [u.mem, c], by rw [u.wr, d]⟩
  have S0 : St (pushed rs4 s) := ⟨e1, pushed_rd _ _, rfl, rfl⟩
  have rd' : ∀ {t}, St t → ∀ i < 9, readSrc t (.mem (atArg i)) = some (arg s i) :=
    fun h => rd _ h.1 h.2.1 h.2.2.1
  simp only [atParams, List.append_assoc]
  refine atPtr_ok (by decide) (rd' S0 0 (by decide)) (rd' S0 7 (by decide)) fun t1 u1 => ?_
  have S1 := st S0 u1 (by decide)
  refine atPtr_ok (by decide) (rd' S1 0 (by decide)) (rd' S1 8 (by decide)) fun t2 u2 => ?_
  have S2 := st S1 u2 (by decide)
  refine atPtr_ok (by decide) (rd' S2 0 (by decide)) (rd' S2 3 (by decide)) fun t3 u3 => ?_
  have S3 := st S2 u3 (by decide)
  refine atPtr_ok (by decide) (rd' S3 0 (by decide)) (rd' S3 6 (by decide)) fun t4 u4 => ?_
  have S4 := st S3 u4 (by decide)
  refine atPtr_ok (by decide) (rd' S4 0 (by decide)) (rd' S4 5 (by decide)) fun t5 u5 => ?_
  have S5 := st S4 u5 (by decide)
  refine atPtr_ok (by decide) (rd' S5 0 (by decide)) (rd' S5 4 (by decide)) fun t6 u6 => ?_
  have S6 := st S5 u6 (by decide)
  refine wp_movS (rd' S6 2 (by decide)) fun t7 u7 _ => wp_addS rfl fun t8 u8 _ => wp_addS rfl fun t9 u9 _ =>
    wp_addS rfl fun t10 u10 _ => WP.block_nil ?_
  have S10 := st (st (st (st S6 u7 (by decide)) u8 (by decide)) u9 (by decide)) u10 (by decide)
  have g : ∀ r, r ≠ .eax → t10.gpr r = t6.gpr r := fun r h => by
    rw [u10.other _ h, u9.other _ h, u8.other _ h, u7.other _ h]
  have hW := A.ws_toNat
  have hn8 : 8 * (arg s 2).toNat < 2 ^ 32 := by
    have := A.s_le; have := A.bound; simp only [scratchBytes, lenOf] at *; omega_arith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, S10.1, S10.2.2.1, S10.2.1, S10.2.2.2⟩
  · show (t10.gpr .ebp).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .edi).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .esi).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      BitVec.toNat_add, hW]
  · show (t10.gpr .edx).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .ecx).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .ebx).toNat = _
    rw [g _ (by decide), u6.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .eax).toNat = _
    rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr]
    simp only [BitVec.toNat_add]
    have := (arg s 2).isLt
    simp only [nAt]
    omega_arith

end VG.Proof.Mont.X86.Sse2

end

end


/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: correctness

`at_correct`: from `mulContract abi 56`'s precondition, `atBody` terminates
with the callee-saved registers and the return address as they were and the
contract's postcondition.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

theorem read_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_val32' (m : Mem) (ws : Addr) (d n : Nat) : numAt m ws d (8 * n) = val32 m ws d (2 * n) := by
  unfold numAt
  rw [show 8 * n = 4 * (2 * n) by omega_using []]
  exact read_val32 m ws (2 * n) d

theorem numAt_w32' (m : Mem) (ws : Addr) (d : Nat) : numAt m ws d 4 = w32 m ws d := by
  unfold numAt
  rw [show 4 = 4 * 1 from rfl, read_val32 m ws 1 d]
  simp [val32]

theorem atBody_noSp : NoSp (seqs [.block atParams, withParams, .block restoreRegs]) :=
  NoSp.of_all (by decide +kernel)

/-- What `body atParams` takes of a state meeting the contract's precondition. -/
theorem atReady {s : State} (A : AtABI s) :
    Ready atParams (wsOf s) (lenOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
      (arg s 7).toNat (arg s 8).toNat s := by
  have Ly := A.lay
  have hinv := A.inv
  have hb := A.bLt
  rw [numAt_val32', numAt_w32'] at hinv
  rw [numAt_val32', numAt_val32'] at hb
  exact ⟨A.entry, Ly, atParams_ok A, VG.Proof.Mont.X86.Square.low_inverse s.mem (wsOf s) _ _ Ly.hN hinv, hb⟩

theorem at_correct (s : State) (h : (Proof.Rsa.MontMul.mulContract abi 56).pre s) :
    ∃ tr t, Exec isa atBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.MontMul.mulContract abi 56).post s t := by
  have A := atAbi_of h
  have R := atReady A
  obtain ⟨tr, t, E, lt, cong, mem, cs, -, -⟩ := body_ok R.entry R.ly atBody_noSp R.par R.inv R.bLt
  have hso := A.so
  have hol := A.o_le
  have hscr := A.s_le
  have hst := A.stackBound
  simp only [Apart, scratchBytes] at hso hscr
  refine ⟨tr, t, E, ⟨cs, ?_⟩, ?_⟩
  · refine Mem.readW_congr fun i hi => mem _ (fun r hr => ?_) (fun hc => ?_)
    · have := ofs_far (base := wsOf s) (size := lenOf s) (x := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i)
        fun hc => A.retScratch _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [nAt, lenOf] at this ⊢ <;> omega_arith
    · have := (s.gpr .esp).isLt
      simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        at hc
      omega_using [hi, hc]
  · sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [numAt_val32', numAt_val32']; exact lt
    · rw [numAt_val32', numAt_val32', numAt_val32', numAt_val32',
        show 64 * (arg s 2).toNat = 32 * nAt s by simp only [nAt]; omega_using []]
      exact cong
    · intro i hi hj
      have hb := A.bound
      apply mem _ (fun r hr => ?_) (fun hc => ?_)
      · rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
          simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, scratchBytes] at this
        rcases hr with rfl | rfl <;> simp only [nAt] <;> omega_using [this]
      · have := (s.gpr .esp).isLt
        have := (arg s 0).isLt
        have := A.stackLo
        refine A.stkScratch (wsOf s + BitVec.ofNat 64 i) ?_ ?_
        · simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            at hc ⊢
          omega_using [this, hc]
        · simp only [Region.Contains, lenOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat]
          omega_using [hi]

end VG.Proof.Mont.X86.Sse2

end

end


/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: verified

Two runs from states with the same public arguments compute the same
numbers (`atReady`), so `body_relCT` makes them leak the same; the witness of
the scalar function's precondition, whose stack is far from its working
space, meets this one's too.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)

theorem at_publicArgs {s t : State} (H : (Proof.Rsa.MontMul.mulContract abi 56).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 9, arg s i = arg t i := by
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption
  | 5, _ => with_reducible assumption
  | 6, _ => with_reducible assumption
  | 7, _ => with_reducible assumption
  | 8, _ => with_reducible assumption

theorem at_constantTime :
    ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 56).pre (Proof.Rsa.MontMul.mulContract abi 56).pub atBody := by
  apply RelCT.constantTime
  refine RelCT.mono (P := fun s₁ s₂ => ∃ W L N S mo inv o a b, BPair atParams W L N S mo inv o a b s₁ s₂)
    (RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => body_relCT (fun _ _ h => h) (atParams_relCT.mono (fun _ _ ⟨_, _, B, ex, ey⟩ => by
        rw [ex, ey, pushed_esp, pushed_esp, B.2.2]) fun _ _ _ => trivial)) ?_ fun _ _ _ => trivial
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨sp, args⟩ := at_publicArgs hp
  have R := atReady (atAbi_of h₂)
  simp only [wsOf, lenOf, nAt, ← args 0 (by decide), ← args 1 (by decide), ← args 2 (by decide),
    ← args 3 (by decide), ← args 4 (by decide), ← args 5 (by decide), ← args 6 (by decide),
    ← args 7 (by decide), ← args 8 (by decide)] at R
  exact ⟨_, _, _, _, _, _, _, _, _, atReady (atAbi_of h₁), R, sp⟩

end VG.Proof.Mont.X86.Sse2
