module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Body
public import VerifiedGarbage.Proof.Mont.X86.Sse2.TimeTaint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Mcdt

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Sse2.Columns
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
what each satisfies by correctness. `relCT_frame`: a frame whose push and pop
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

/-- A frame whose push leaks the same addresses and leaves `esp` and the
frame's size the same in both runs, and whose pop leaks addresses of `esp`. -/
theorem relCT_frame {i j : Instr} {body : Prog isa} {P R : State → State → Prop}
    (hpush : ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push i s₁ = some a₁ → isa.push i s₂ = some a₂ →
      isa.addrs i s₁ = isa.addrs i s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len)
    (hpop : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp → isa.addrs j b₁ = isa.addrs j b₂)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ isa.push i s₁ = some a ∧ isa.push i s₂ = some b) body R) :
    RelCT isa P (.frame i body j) fun c₁ c₂ => c₁.gpr .esp = c₂.gpr .esp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨ha, hsp, hl⟩ := hpush _ _ _ _ hp p₁ p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨_, _, hp, p₁, p₂⟩ b₁ b₂
      obtain ⟨-, -, -, -, e₁', k₁, l₁, hk₁, hk₁', hh₁, g₁⟩ := pop_eq q₁
      obtain ⟨-, -, -, -, e₂', k₂, l₂, hk₂, hk₂', hh₂, g₂⟩ := pop_eq q₂
      have hb' := e₁'.trans (hsp.trans e₂'.symm)
      rw [hh₁, hh₂] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hk : k₁ = k₂ := by omega
      refine ⟨by rw [ha, hpop _ _ hb'], ?_⟩
      show s₁'.gpr .esp = s₂'.gpr .esp
      rw [g₁, g₂, hb', hk]

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

theorem mcdt_push_eq {r : Reg} {s a : State} (h : isa.push (.mcdtEnter r) s = some a) :
    r ≠ .esp ∧ a = mcdtPushed r s := by
  simp only [isa, push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨hc.1, rfl⟩

/-- An MCDT frame's push, for runs with the same `esp`. -/
theorem mcdt_frame {r : Reg} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp) :
    ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push (.mcdtEnter r) s₁ = some a₁ → isa.push (.mcdtEnter r) s₂ = some a₂ →
      isa.addrs (.mcdtEnter r) s₁ = isa.addrs (.mcdtEnter r) s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len := by
  intro s₁ s₂ a₁ a₂ hp h₁ h₂
  obtain ⟨hr, rfl⟩ := mcdt_push_eq h₁
  obtain ⟨-, rfl⟩ := mcdt_push_eq h₂
  have e := hsp _ _ hp
  exact ⟨by simp only [addrs, e], by rw [mcdtPushed_esp _ _ hr, mcdtPushed_esp _ _ hr, e],
    by rw [mcdtPushed_wr, mcdtPushed_wr]; rfl⟩

theorem mcdtLeave_addrs : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp →
    isa.addrs .mcdtLeave b₁ = isa.addrs .mcdtLeave b₂ := by
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
  refine relCT_of_wp ((relCT_frame (mcdt_frame fun _ _ h => ?_) mcdtLeave_addrs columns_relCT).mono
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
  refine (relCT_frame (R := fun _ _ => True) (push_frame fun _ _ h => (hP _ _ h).2.2) (pop_addrs .ebx 4) ?_).mono
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
  · refine relCT_frame (push_frame ?_) (pop_addrs .eax 7)
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
