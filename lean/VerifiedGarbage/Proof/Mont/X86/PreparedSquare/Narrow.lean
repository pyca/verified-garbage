module

public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Columns
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Permissions
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args

/-! # Execute columns with their cached stack values read-only -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def cacheRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 16⟩
def readonly (s : State) (W : Addr) (L : Nat) : State :=
  s.withRegions (cacheRegion s :: s.rd) [⟨W, L⟩]

structure ColumnReady (s : State) (W : Addr) (L N S o a : Nat) (A : Nat → BitVec 32) : Prop where
  args : Args s W L A
  ws : Ws s W L
  values : ArgVals A W N S 256 56 o a a
  lay : Lay L N S 256 56 a a
  positive : 0 < N
  edi : PtrAt s W .edi S
  inverse : (w32 s.mem W 256 * w32 s.mem W 56 + 1) % 2 ^ 32 = 0
  small : val32 s.mem W a N < val32 s.mem W 256 N
  wr : s.wr = [cacheRegion s, ⟨W, L⟩]
  fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  apart : (cacheRegion s).Disjoint ⟨W, L⟩

theorem readonly_covers {s : State} {W : Addr} {L : Nat}
    (wr : s.wr = [cacheRegion s, ⟨W, L⟩]) :
    Covers (s.rd ++ s.wr) ((readonly s W L).rd ++ (readonly s W L).wr) ∧
    Covers ((readonly s W L).rd ++ (readonly s W L).wr) (s.rd ++ s.wr) ∧
    Covers (readonly s W L).wr s.wr := by
  have eq : ∀ r, r ∈ s.rd ++ s.wr ↔ r ∈ (cacheRegion s :: s.rd) ++ [⟨W, L⟩] := by
    intro r
    rw [wr]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  refine ⟨?_, ?_, ?_⟩
  · intro x n ⟨r, hr, hc⟩
    exact ⟨r, (eq r).mp hr, hc⟩
  · intro x n ⟨r, hr, hc⟩
    exact ⟨r, (eq r).mpr hr, hc⟩
  · intro x n ⟨r, hr, hc⟩
    change r ∈ [⟨W, L⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    rw [wr]
    exact ⟨_, by simp, hc⟩

theorem ColumnReady.readonly_args {s : State} {W : Addr} {L N S o a : Nat} {A : Nat → BitVec 32}
    (R : ColumnReady s W L N S o a A) : Args (readonly s W L) W L A :=
  R.args.withRegions (readonly_covers R.wr).1

theorem ColumnReady.readonly_out {s : State} {W : Addr} {L N S o a : Nat} {A : Nat → BitVec 32}
    (R : ColumnReady s W L N S o a A) : ArgsOut 3 (readonly s W L) := by
  refine ⟨R.fit, ?_⟩
  intro r hr
  change r ∈ [⟨W, L⟩] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact R.apart

theorem ColumnReady.readonly_wp {s : State} {W : Addr} {L N S o a : Nat} {A : Nat → BitVec 32}
    (R : ColumnReady s W L N S o a A) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.columns (readonly s W L) fun _ => True := by
  have hw : Ws (readonly s W L) W L := ⟨List.mem_singleton_self _, R.ws.nowrap⟩
  exact WP.mono (columns_ok R.readonly_args hw R.values R.lay R.positive R.edi R.inverse R.small)
    (fun _ _ => True.intro)

theorem columns_trace_same {s t u v : State} {W : Addr} {L N S o a : Nat} {A : Nat → BitVec 32}
    (R : ColumnReady s W L N S o a A) (T : ColumnReady t W L N S o a A)
    (sp : s.gpr .esp = t.gpr .esp) {ls lt : List Leak}
    (ES : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns s ls u)
    (ET : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns t lt v) : ls = lt := by
  have scratch : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (R.edi.trans T.edi.symm)
  obtain ⟨_, sr, sw⟩ := readonly_covers R.wr
  obtain ⟨_, tr, tw⟩ := readonly_covers T.wr
  exact columns_trace_of_readonly R.readonly_args T.readonly_args sp scratch R.readonly_out T.readonly_out
    R.readonly_wp T.readonly_wp sr sw tr tw ES ET

theorem Args.reindex {s : State} {W : Addr} {L N S o a : Nat} {A B : Nat → BitVec 32}
    (h : Args s W L B) (VA : ArgVals A W N S 256 56 o a a)
    (VB : ArgVals B W N S 256 56 o a a) : Args s W L A := by
  have zero : A 0 = B 0 := BitVec.eq_of_toNat_eq (VA.ws.trans VB.ws.symm)
  have width : A 2 = B 2 := BitVec.eq_of_toNat_eq (by have := VA.n; have := VB.n; omega)
  have modulus : A 3 = B 3 := BitVec.eq_of_toNat_eq (VA.mo.trans VB.mo.symm)
  have input : A 7 = B 7 := BitVec.eq_of_toNat_eq (VA.a.trans VB.a.symm)
  refine ⟨?_, h.far, ?_, ?_⟩
  · intro i hi
    rw [h.read i hi]
    apply congrArg some
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [cacheValue, zero, width, modulus, input]
  · apply BitVec.eq_of_toNat_eq
    exact VA.inv
  · apply BitVec.eq_of_toNat_eq
    exact VA.mo

theorem columns_trace {s t u v : State} {W : Addr} {L N S o a : Nat} {A B : Nat → BitVec 32}
    (R : ColumnReady s W L N S o a A) (T : ColumnReady t W L N S o a B)
    (sp : s.gpr .esp = t.gpr .esp) {ls lt : List Leak}
    (ES : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns s ls u)
    (ET : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns t lt v) : ls = lt := by
  have T' : ColumnReady t W L N S o a A :=
    ⟨T.args.reindex R.values T.values, T.ws, R.values, T.lay, T.positive, T.edi, T.inverse,
      T.small, T.wr, T.fit, T.apart⟩
  exact columns_trace_same R T' sp ES ET

end VG.Proof.Mont.X86.PreparedSquare
