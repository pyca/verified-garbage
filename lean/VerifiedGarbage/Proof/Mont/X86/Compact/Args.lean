module

public import VerifiedGarbage.Impl.Mont.X86.Compact
import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Cdecl arguments and prepared array pointers for compact multiplication -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

structure Args (s : State) (W : Addr) (L : Nat) (A : Nat → BitVec 32) : Prop where
  read : ∀ i < 5, readSrc s (.mem (Compact.arg i)) = some (A i)
  far : ∀ i < 5, ArgFar s W L (Compact.arg i)

theorem Args.keep {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Args t W L A :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

theorem Args.of_keeps {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : Args s W L A) {rs : List Reg} (K : Keeps rs s t) (hsp : .esp ∉ rs)
    (O : Outs W [(0, L)] s.mem t.mem) : Args t W L A :=
  h.keep O (K.1 _ hsp) K.2.1 K.2.2

theorem Args.of_upd {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : Args s W L A) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) : Args t W L A :=
  h.of_keeps u.keeps (by simpa using hd.symm) (by rw [u.mem]; exact Outs.refl _ _ _)

theorem arrayPtr_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {r : Reg} {j : Nat} (fit : 64 + 8 * j + 4 ≤ L) :
    WP isa (.block (Compact.arrayPtr r j)) s fun t =>
      t.gpr r = s.mem.readW (off W (64 + 8 * j)) 32 ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  unfold Compact.arrayPtr
  refine wp_movS (ha.read 0 (by decide)) fun a A _ => ?_
  have hwA := hw.of_keeps A.keeps
  have ptr : PtrAt a W r 0 := by
    rw [PtrAt, A.gpr, base, Nat.add_zero, Nat.mod_eq_of_lt]
    have := hw.nowrap
    omega
  refine wp_movS (readSrc_ptr hwA ptr (d := 64 + 8 * j) (by omega)) fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.gpr, A.mem, Nat.zero_add], T.mem.trans A.mem, A.keeps.trans T.keeps⟩

theorem operandPtr_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {r t : Reg} (reg : r ≠ .esp) (distinct : r ≠ t) {i : Nat} (index : i < 5)
    (fit : 64 + 8 * (A i).toNat + 4 ≤ L) :
    WP isa (.block (Compact.operandPtr r i t)) s fun u =>
      u.gpr r = s.mem.readW (off W (64 + 8 * (A i).toNat)) 32 ∧
      u.mem = s.mem ∧ Keeps [r, t] s u := by
  unfold Compact.operandPtr
  refine wp_movS (ha.read 0 (by decide)) fun a B _ => ?_
  refine wp_movS ((ha.of_upd B reg).read i index) fun b C _ => ?_
  refine wp_addS rfl fun c D _ => ?_
  refine wp_addS rfl fun d E _ => ?_
  refine wp_addS rfl fun e F _ => ?_
  have scaled : (e.gpr t).toNat = 8 * (A i).toNat := by
    rw [F.gpr, E.gpr, D.gpr, C.gpr]
    simp only [BitVec.toNat_add]
    have := hw.nowrap
    omega
  refine wp_addS rfl fun f G _ => ?_
  have K : Keeps [r, t] s f := (B.keeps.mono (by simp)).trans
    ((C.keeps.mono (by simp)).trans ((D.keeps.mono (by simp)).trans
      ((E.keeps.mono (by simp)).trans ((F.keeps.mono (by simp)).trans (G.keeps.mono (by simp))))))
  have M : f.mem = s.mem := G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans B.mem))))
  have ptr : PtrAt f W r (8 * (A i).toNat) := by
    rw [PtrAt, G.gpr, BitVec.toNat_add, scaled, F.other r distinct, E.other r distinct,
      D.other r distinct, C.other r distinct, B.gpr, base]
  refine wp_movS (readSrc_ptr (hw.of_keeps K) ptr (d := 64) (by omega)) fun u U _ => WP.block_nil ?_
  refine ⟨?_, U.mem.trans M, K.trans (U.keeps.mono (by simp))⟩
  rw [U.gpr, M, Nat.add_comm (8 * (A i).toNat) 64]

end VG.Proof.Mont.X86.Compact
