module

import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.X25519.Arm.Invert
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
public import VerifiedGarbage.Impl.Ed25519.Arm.Packed
public import VerifiedGarbage.Proof.Ed25519.Arm.Packed
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField

/-! ### `Ed25519.Arm.PointPowers`, which this module and modules that import it used -/

section

/-! ### `Ed25519.Arm.PointTableLoad`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.Arm.PointTable`. -/

@[expose] public section

section
/-! Compact point tables in the caller's eight-KiB workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem Ctx.ptr_nat {b : BitVec 32} {s : State} (hc : Ctx b s) {o : Nat} (ho : o < 8192) :
    (b + BitVec.ofNat 32 o).toNat = b.toNat + o := by
  have hb := hc.fit
  rw [toNat_add_lt (by rw [toNat_imm (by omega_using [ho])]; omega_using [ho, hb]), toNat_imm (by omega_using [ho])]

theorem Ctx.ptr_addr {b : BitVec 32} {s : State} (hc : Ctx b s) {o : Nat} (ho : o < 8192) :
    State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o :=
  addr_add (by have := hc.fit; omega_using [ho, this])

structure TableKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest [.r2, .r3] s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem

theorem TableKeep.ctx {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem TableKeep.trans {b : BitVec 32} {s t u : State} {o n : Nat}
    (h : TableKeep b o n s t) (k : TableKeep b o n t u) : TableKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem TableKeep.mono {b : BitVec 32} {s t : State} {o n o' n' : Nat}
    (h : TableKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableKeep b o' n' s t :=
  ⟨h.rest, h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.slot {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (hn : o + n ≤ 8192) (i : Slot)
    (hsep : offset i + 64 ≤ o ∨ o + n ≤ offset i) :
    ∀ k < 16, limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
  have hi := slot_range i
  rw [ACC_eq] at hi
  refine limb_frame h.frame fun r hm k hk => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (by omega_using [hsep, hk]) (by omega_using [hi, hk]) (by omega_using [hn])

theorem TableKeep.env {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (ho : 1632 ≤ o) (hn : o + n ≤ 8192) : env t.mem b = env s.mem b := by
  funext i
  have hi := slot_range i
  rw [ACC_eq] at hi
  exact congrArg VG.Proof.X25519.toFe (val16_congr (h.slot hn i (.inl (by omega_using [ho, hi]))))

theorem TableKeep.lim {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (ho : 1632 ≤ o) (hn : o + n ≤ 8192)
    (hl : AllLim s.mem b) : AllLim t.mem b := by
  intro i k hk
  have hi := slot_range i
  rw [ACC_eq] at hi
  rw [h.slot hn i (.inl (by omega_using [ho, hi])) k hk]
  exact hl i k hk

def tableF (m : Mem) (b : BitVec 32) (o : Nat) : Spec.X25519.Fe :=
  packedF m (State.addr b + BitVec.ofNat 64 o)

theorem TableKeep.tableF {b : BitVec 32} {s t : State} {o n d : Nat}
    (h : TableKeep b o n s t) (hn : o + n ≤ 8192) (hd : d + 32 ≤ 8192)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : tableF t.mem b d = tableF s.mem b d := by
  refine congrArg VG.Proof.X25519.toFe (packedV_frame h.frame fun r hm => ?_)
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ hsep (by omega_using [hd]) (by omega_using [hn])

theorem toTableQuarter_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (packField (64 + 64 * j) (32 * j))) s fun t =>
      tableF t.mem b (o + 32 * j) = env s.mem b ⟨j, by omega_using [hj]⟩ ∧
      TableKeep b (o + 32 * j) 32 s t := by
  have ea := hc.ptr_addr (by omega_using [ho] : o < 8192)
  refine WP.mono (packField_ok hc (by omega_using [hj]) (hl ⟨j, by omega_using [hj]⟩) (by omega_using [hj]) hp
    (by rw [hc.ptr_nat (by omega_using [ho])]; have := hc.fit; omega_using [ho, hj, this])
    (fun i hi => by rw [ea, Offset.add_add]; exact in_base hc.wr (by omega_using [ho, hj, hi]) (by omega_using [ho, hj, hi]))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inl (by omega_using [hlo, hj])) (by omega_using [hj]) (by omega_using [ho, hj])))
    fun t ⟨hr, hf, hv⟩ => ?_
  rw [ea, Offset.add_add] at hf hv
  exact ⟨congrArg VG.Proof.X25519.toFe hv, ⟨hr.mono (by decide), hf⟩⟩

theorem toTablePrefix_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => packField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), tableF t.mem b (o + 32 * j) = env s.mem b ⟨j, by omega_using [hn, hj]⟩) ∧
      TableKeep b o (32 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega_using [hn])) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (toTableQuarter_ok (hk.ctx hc) (hk.lim hlo (by omega_using [ho, hn]) hl)
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega_using [hn])) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega_using []) (by omega_using [])).trans (ku.mono (by omega_using []) (by omega_using []))⟩
    by_cases h : j < n
    · rw [ku.tableF (by omega_using [ho, hn]) (by omega_using [ho, hn, hj]) (.inl (by omega_using [h])), hv j h]
    · have e : j = n := by omega_using [hj, h]
      subst j
      rw [hu, hk.env hlo (by omega_using [ho, hn])]

def tablePoint (m : Mem) (b : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨tableF m b o, tableF m b (o + 32), tableF m b (o + 64), tableF m b (o + 96)⟩

theorem pointToTable_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t => tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 ∧
      TableKeep b o 128 s t := by
  refine WP.mono (toTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hk⟩
  simp only [tablePoint, point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! Restore compact table entries into working point coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fromTableQuarter_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (unpackField (64 + 64 * j) (32 * j))) s fun t =>
      env t.mem b ⟨j, by omega_using [hj]⟩ = tableF s.mem b (o + 32 * j) ∧ AllLim t.mem b ∧
      TableKeep b (64 + 64 * j) 64 s t := by
  have ea := hc.ptr_addr (by omega_using [ho] : o < 8192)
  refine WP.mono (unpackField_ok hc (by omega_using [hj]) (by omega_using [hj]) hp
    (by rw [hc.ptr_nat (by omega_using [ho])]; have := hc.fit; omega_using [ho, hj, this])
    (fun i hi => by
      rw [ea, Offset.add_add]
      exact in_base (List.mem_append_right _ hc.wr) (by omega_using [ho, hj, hi]) (by omega_using [ho, hj, hi]))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inr (by omega_using [hlo, hj])) (by omega_using [ho, hj]) (by omega_using [hj])))
    fun t ⟨hr, hf, hlt, hv⟩ => ?_
  rw [ea, Offset.add_add] at hv
  have hu := field_update ⟨j, by omega_using [hj]⟩ hl (frame_o16 hf) hlt
  exact ⟨congrArg VG.Proof.X25519.toFe hv, hu.1, ⟨hr, hf⟩⟩

theorem fromTablePrefix_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => unpackField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), env t.mem b ⟨j, by omega_using [hn, hj]⟩ = tableF s.mem b (o + 32 * j)) ∧
      AllLim t.mem b ∧ TableKeep b 64 (64 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, hl, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega_using [hn])) fun t ⟨hv, hlt, hk⟩ => ?_
    refine WP.mono (fromTableQuarter_ok (hk.ctx hc) hlt
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega_using [hn])) fun u ⟨hu, hlu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, hlu,
      (hk.mono (by omega_using []) (by omega_using [])).trans (ku.mono (by omega_using []) (by omega_using []))⟩
    by_cases h : j < n
    · have he : env u.mem b ⟨j, by omega_using [hn, hj]⟩ = env t.mem b ⟨j, by omega_using [hn, hj]⟩ :=
        congrArg VG.Proof.X25519.toFe (val16_congr (ku.slot (by omega_using [hn]) ⟨j, by omega_using [hn, hj]⟩
          (.inl (by simp only [offset]; omega_using [h]))))
      rw [he, hv j h]
    · have e : j = n := by omega_using [hj, h]
      subst j
      rw [hu, hk.tableF (by omega_using [hn]) (by omega_using [ho, hn]) (.inr (by omega_using [hlo, hn]))]

theorem pointFromTable_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1632 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t => point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      AllLim t.mem b ∧ TableKeep b 64 256 s t := by
  refine WP.mono (fromTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hlt, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hlt, hk⟩
  change env t.mem b 0 = _ at h0
  change env t.mem b 1 = _ at h1
  change env t.mem b 2 = _ at h2
  change env t.mem b 3 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

end VG.Proof.Ed25519.Arm

end

end

/-! Merged from `Proof.Ed25519.Arm.PointTableAddr`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.PointLoop`. -/
section
/-! Fixed batches of exact doublings preserve the saved accumulator. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure DoubleInv (s₀ : State) (b : BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  value : point (env s.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : IKeep b s₀ s

end VG.Proof.Ed25519.Arm
end

/-! Public table addresses and bounded counters. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem movw_nat {v : Nat} (hv : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega_arith)]

theorem sub_beq_zero_nat {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 32) + BitVec.ofNat 32 y = BitVec.ofNat 32 y := BitVec.zero_add _
  rw [hz]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [toNat_imm hx, toNat_imm hy] at this
  · exact congrArg (BitVec.ofNat 32)

end VG.Proof.Ed25519.Arm
end

/-! Constructing bounded tables of exact point doublings. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev TableFrame (b : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [FA b, ⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m'

theorem TableFrame.mono {b : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableFrame b o' n' m m' := by
  refine h.sub fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ ho hn⟩

theorem TableFrame.workspace {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [FA b] m m') : TableFrame b o n m m' :=
  h.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

theorem TableFrame.table {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') : TableFrame b o n m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem tablePoint_frame {b : BitVec 32} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, (⟨State.addr b + BitVec.ofNat 64 d, 128⟩ : Region).Disjoint r) :
    tablePoint m' b d = tablePoint m b d := by
  have he : ∀ i, i + 32 ≤ 128 → tableF m' b (d + i) = tableF m b (d + i) := by
    intro i hi
    refine congrArg VG.Proof.X25519.toFe (packedV_frame hf fun r hm => ?_)
    exact (hd r hm).sub_left (Offset.sub _ (by omega_arith) (by omega_arith))
  have h0 := he 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [tablePoint, h0, he 32 (by decide), he 64 (by decide), he 96 (by decide)]

theorem TableFrame.point {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') {d : Nat} (hd : 1632 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 ≤ 8192) (hn : o + n ≤ 8192) :
    tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Offset.disjoint _ hsep (by omega_arith) (by omega_arith)

theorem workspace_tablePoint {b : BitVec 32} {m m' : Mem} (h : Frame [FA b] m m')
    {d : Nat} (hd : 1632 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by decide)

abbrev powersClob : List Reg := [.r10, .r11] ++ fclob

structure PowersKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : TableFrame b o n s.mem t.mem

theorem PowersKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : PowersKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem PowersKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem PowersKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : PowersKeep b o n s t) (k : PowersKeep b o n t u) : PowersKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem PowersKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : PowersKeep b o' n' s t :=
  ⟨h.rest, TableFrame.mono h.frame ho hn⟩

end VG.Proof.Ed25519.Arm

end

end

/-! ### `Ed25519.Arm.AccumulateStep`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.Arm.PointAccumulate`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.AccKeep`. -/
section
/-! Point accumulation changes the field workspace and its table pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev accClob : List Reg := fclob
structure AccKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest accClob s t
  frame : Frame [FA b] s.mem t.mem

theorem AccKeep.ctx {b : BitVec 32} {s t : State} (h : AccKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem AccKeep.trans {b : BitVec 32} {s t u : State} (h : AccKeep b s t) (k : AccKeep b t u) :
    AccKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem AccKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem AccKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hws : ∀ r ∈ ws, r ∈ accClob) (hm : t.mem = s.mem) : AccKeep b s t :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem AccKeep.of_table {b : BitVec 32} {s t : State} {o n : Nat} (h : TableKeep b o n s t)
    (ho : 64 ≤ o) (hn : o + n ≤ 1632) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.high {b : BitVec 32} {s t : State} (h : TableKeep b 64 256 s t)
    (i : Slot) (hi : 4 ≤ i.val) :
    VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i :=
  congrArg VG.Proof.X25519.toFe (val16_congr (h.slot (by decide) i
    (.inr (by simp only [offset]; omega_arith))))

theorem point_congr {e f : Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : point e x y z t = point f x y z t := by
  simp only [point, hx, hy, hz, ht]

theorem savePoint_d (e : Env) : evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : Env) : evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : Env) : evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : Env) :
    point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : Env) :
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PrepareAdd`. -/
section
/-! Save the accumulator and load the next exact power into Q. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.BitMask`. -/
section
/-! Scalar bits in the sixteen-byte batch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem AccKeep.bit {b : BitVec 32} {s t : State} (h : AccKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1568)
    (.inl (by omega_arith)) (by omega_arith) (by decide)) _ (Region.contains_self _ _)

theorem scalarBitMask_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat) (hj : j < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t => AccKeep b s t ∧ t.mem = s.mem ∧
      t.gpr .r9 = 0 - BitVec.ofNat 32 (!bit).toNat := by
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have ep : s1.gpr .r2 = b + BitVec.ofNat 32 j := by
    rw [u1.gpr]
    change s.gpr .r0 + s.gpr .r11 = _
    rw [hc.r0, h11]
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (32 + j)) (by decide)
    (by rw [ep, Offset.add_add, addr_add (by have := hc.fit; omega_arith)]; rw [Nat.add_comm j 32])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_
  have hr : Rest [.r2, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨AccKeep.of_rest hr (by decide) hm, hm, ?_⟩
  rw [u3.gpr]
  change s2.gpr .r9 - 1 = _
  rw [u2.gpr, u1.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointSelect`. -/
section
/-! Branch-free selection using the verified limb swaps. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def swapSlot (a b : Slot) (sw : Bool) (i : Slot) : Slot :=
  if sw then if i = a then b else if i = b then a else i else i

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env := fun i => e (swapSlot a b sw i)
def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapEnvs_step (ops : List (Slot × Slot)) (a b : Slot) (sw : Bool) {e f g : Env}
    (hf : f = swapEnv a b sw e) (hg : g = swapEnvs ops sw f) :
    g = swapEnvs ((a, b) :: ops) sw e := hg.trans (congrArg (swapEnvs ops sw) hf)

theorem swapField_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) (hab : a ≠ b) {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have ha := slot_range a
  have hb := slot_range b
  rw [ACC_eq] at ha hb
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok (by omega_arith) (by omega_arith) (by simp only [offset]; omega_arith) hc
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ht => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr base) (offset i) k =
      limb s.mem (State.addr base) (offset (swapSlot a b sw i)) k := by
    intro i k hk
    by_cases hia : i = a
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.lx k hk
    by_cases hib : i = b
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, hia, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.ly k hk
    · have hn1 : i.val ≠ a.val := fun h => hia (Fin.ext h)
      have hn2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
      have hi := slot_range i
      rw [ACC_eq] at hi
      have ei : swapSlot a b sw i = i := by simp only [swapSlot, hia, hib, ite_false, ite_self]
      rw [ei]
      refine limb_frame ht.frame (fun r hr j hj => ?_) k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (by simp only [offset]; omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨ht.rest.mono (by decide), ?_⟩,
    fun i k hk => by rw [he i k hk]; exact hl _ k hk,
    ht.rest.gpr _ (by decide), funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (he i))⟩
  refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem swapFields_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (ops : List (Slot × Slot)) (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool}
    (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (swapFields ops)) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl, rfl⟩
  | cons ab ops ih =>
    rcases ab with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc hl a b (hops (a, b) (by simp)) hm) fun t ⟨hk, hlt, ht9, hv⟩ => ?_
    refine WP.mono (ih (hk.ctx hc) hlt (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (ht9.trans hm))
      fun u ⟨ku, hlu, hu9, vu⟩ => ?_
    refine ⟨hk.trans ku, hlu, hu9.trans ht9, ?_⟩
    exact swapEnvs_step ops a b sw (e := env s.mem base) (f := env t.mem base) (g := env u.mem base) hv vu

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by cases sw <;> rfl

theorem pointSelect_d (e : Env) (sw : Bool) : swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block pointSelect) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 =
        (if sw then point (env s.mem base) 17 18 19 20 else point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.mono (swapFields_ok hc hl pointSelectPairs (by decide) hm) fun t ⟨hk, hlt, _, hv⟩ => ?_
  exact ⟨hk, hlt, by rw [hv, pointSelect_eval], by rw [hv, pointSelect_d]⟩

end VG.Proof.Ed25519.Arm
end

/-! Add one exact table power and select with its scalar bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem select_flip {α : Type} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) : c = if bit then b else a := by
  cases bit with
  | false => exact hc.trans hd
  | true => exact hc.trans he

end VG.Proof.Ed25519.Arm
end

/-! One descending scalar bit implements the specification's recursion. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [scalarBit, h] <;> decide

theorem choose_after (s n : Nat) (p x y : Spec.Ed25519.Point)
    (hx : x = after s p (n + 1)) (hy : y = powerPoint p n) :
    (if scalarBit s n then Spec.Ed25519.pointAdd x y else x) = after s p n := by
  rw [hx, hy]
  have h := (after_step s p n).symm
  by_cases hz : (s / 2 ^ n) % 2 = 0
  · simpa only [scalarBit, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, ite_true] using h
  · simpa only [scalarBit, hz, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] using h

abbrev loopClob : List Reg := .r11 :: accClob
structure LoopKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest loopClob s t
  frame : Frame [FA b] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (s : State) : LoopKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem LoopKeep.ctx {b : BitVec 32} {s t : State} (h : LoopKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem LoopKeep.trans {b : BitVec 32} {s t u : State} (h : LoopKeep b s t) (k : LoopKeep b t u) :
    LoopKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem LoopKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : LoopKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩
theorem LoopKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hw : ∀ r ∈ ws, r ∈ loopClob) (hm : t.mem = s.mem) : LoopKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem LoopKeep.bit {b : BitVec 32} {s t : State} (h : LoopKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1568)
    (.inl (by omega_arith)) (by omega_arith) (by decide)) _ (Region.contains_self _ _)

theorem accumulateDec_ok (s : State) (n : Nat) (h11 : s.gpr .r11 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block [.dp .sub .r11 .r11 (.imm 1)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 n ∧ Rest [.r11] s t ∧ t.mem = s.mem := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨?_, ht.rest (by decide), ht.mem⟩
  rw [ht.gpr]
  change s.gpr .r11 - 1 = _
  rw [h11, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem accumulateTest_ok (s : State) (n : Nat) (hn : n < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 n) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun t => t.z = decide (n = 0) ∧
      Rest [] s t ∧ t.mem = s.mem := by
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨?_, ht.rest _, ht.mem⟩
  have he : BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n := BitVec.sub_zero _
  rw [hz, h11, he, ofNat_beq_zero (by omega_arith)]

end VG.Proof.Ed25519.Arm

end

end

/-! Merged from `Proof.Ed25519.Arm.PointPowersLoop`. -/

@[expose] public section

section
/-! Checkpoint-loop termination and exact table contents. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointBatch`. -/
section
/-! Merged from `Proof.Ed25519.Arm.AccumulateLoop`. -/
section
/-! The descending sixteen-bit loop follows the specification exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure AccumulateInv (s₀ : State) (b : BitVec 32) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat
  table : ∀ i < 16, tablePoint s.mem b (5728 + 128 * i) = powerPoint p (start + i)
  keep : LoopKeep b s₀ s

end VG.Proof.Ed25519.Arm
end

/-! The local table preserves the accumulator and the checkpoint table. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.of_acc {b : BitVec 32} {o n : Nat} {s t : State} (h : AccKeep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩
theorem PowersKeep.of_keep {b : BitVec 32} {o n : Nat} {s t : State} (h : Keep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩

end VG.Proof.Ed25519.Arm
end

/-! Frames for scalar multiplication preserve argument pointers,
register saves, and all data beyond the compact tables. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev mulRegions (b : BitVec 32) (o n : Nat) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA b,
    ⟨State.addr b + BitVec.ofNat 64 o, n⟩]

structure MulKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (mulRegions b o n) s.mem t.mem

theorem MulKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : MulKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem MulKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)
theorem MulKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : MulKeep b o n s t) (k : MulKeep b o n t u) : MulKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem MulKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : MulKeep b o' n' s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))), Offset.sub _ ho hn⟩
theorem MulKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) : MulKeep b o n s t :=
  ⟨h.rest, Frame.mono h.frame (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩
theorem MulKeep.of_loop {b : BitVec 32} {o n : Nat} {s t : State}
    (h : LoopKeep b s t) : MulKeep b o n s t :=
  ⟨h.rest.mono (by decide), h.frame.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [mulRegions, List.mem_cons, true_or, or_true])⟩
theorem MulKeep.of_bits {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)⟩
theorem MulKeep.of_rest {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem MulKeep.word {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : 1632 ≤ o) (hn : o + n ≤ 8192)
    (d : Nat) (hd : d = 48 ∨ d = 52) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem MulKeep.table {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) {d : Nat} (hd : 1632 ≤ d) (hb : d + 128 ≤ 8192)
    (hn : o + n ≤ 8192) (hs : d + 128 ≤ o ∨ o + n ≤ d) :
    tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem smallFrame_env {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64) :
    env m' b = env m b := by
  funext i
  exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)))

theorem smallFrame_lim {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hl : AllLim m b) : AllLim m' b := by
  intro i k hk
  rw [limb_frame hf (fun r hr j hj => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) k hk]
  exact hl i k hk

end VG.Proof.Ed25519.Arm
