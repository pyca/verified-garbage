module

import VerifiedGarbage.Proof.Ed25519.Arm.Points
public import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Impl.Ed25519.Arm.PointPowers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
public import VerifiedGarbage.Impl.Ed25519.Arm.Packed
public import VerifiedGarbage.Proof.Ed25519.Arm.Packed
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

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

theorem doubleBody_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (n : Nat) (hn : n < 16) (hcount : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa doubleBody s fun t => t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      AllLim t.mem b ∧ point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hi⟩ => ?_)
  refine WP.mono (decR10_ok (by omega_arith) ((hk.rest.gpr _ (by decide)).trans hcount))
    fun u ⟨hu, hz, hr, hm⟩ => ?_
  exact ⟨hu, hz, hm ▸ hlt, by rw [hm]; exact hv, by rw [hm]; exact hi,
    (IKeep.of_keep hk).trans (IKeep.of_counter hr hm)⟩

structure DoubleInv (s₀ : State) (b : BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  value : point (env s.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : IKeep b s₀ s

theorem doubleLoop_ok {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (hcount : s₀.gpr .r10 = 16) (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop doubleBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧ IKeep b s₀ t := by
  apply WP.loop (DoubleInv s₀ b) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega_arith : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega_arith
    refine WP.mono (doubleBody_ok hi.ctx hi.lim k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htl, htv, hthi, htk⟩ => ?_
    have hv : point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega_arith, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, decide_true, Bool.not_true], htl, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz, decide_eq_false hk0, Bool.not_false],
        k, by omega_arith, ⟨by omega_arith, by omega_arith, htk.ctx hi.ctx, htl, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hc, hl, hcount, rfl, fun _ _ => rfl,
      ⟨Rest.refl _ _, Frame.refl _ _⟩⟩

theorem double16_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hk : IKeep b s t := IKeep.of_counter (ht.rest (by decide)) ht.mem
  refine WP.mono (doubleLoop_ok (hk.ctx hc) (by rw [ht.mem]; exact hl)
    ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, hv, hh, hu⟩ => ?_
  rw [ht.mem] at hv hh
  exact ⟨hlu, hv, hh, hk.trans hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Public table addresses and bounded counters. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem movw_nat {v : Nat} (hv : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega_arith)]

theorem tableAddr_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (start j : Nat)
    (ho : start + 128 * j < 8192) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr start)) s fun t =>
      t.gpr .r12 = b + BitVec.ofNat 32 (start + 128 * j) ∧
      Rest [.r3, .r12] s t ∧ t.mem = s.mem := by
  have hb := hc.fit
  refine wp_movw fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = start := by rw [u1.gpr, movw_nat (by omega_arith)]
  have e2 : (s2.gpr .r12).toNat = b.toNat + start := by
    rw [u2.gpr]
    change (s1.gpr .r0 + s1.gpr .r3).toNat = _
    rw [u1.other _ (by decide), hc.r0, toNat_add_lt (by rw [e1]; omega_arith), e1]
  have e11 : (s2.gpr .r11 <<< 7).toNat = 128 * j := by
    rw [u2.other _ (by decide), u1.other _ (by decide), h11, toNat_shl, toNat_imm (by omega_arith)]
    omega_arith
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  apply BitVec.eq_of_toNat_eq
  rw [u3.gpr]
  change (s2.gpr .r12 + (s2.gpr .r11 <<< 7)).toNat = _
  rw [toNat_add_lt (by rw [e2, e11]; omega_arith), e2, e11, hc.ptr_nat ho]
  omega_arith

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

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 32)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧ t.z = decide (j + 1 = count) ∧
      Rest [.r3, .r11] s t ∧ t.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_cmp (op2_reg _ _) fun s3 u3 hz => WP.block_nil ?_
  have e2 : s2.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [u2.gpr]
    change s1.gpr .r11 + 1 = _
    rw [u1.other _ (by decide), h11, BitVec.ofNat_add]
    rfl
  have e3 : s2.gpr .r3 = BitVec.ofNat 32 count := by
    rw [u2.other _ (by decide), u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [movw_nat (by omega_arith), toNat_imm (by omega_arith)]
  exact ⟨by rw [u3.gpr]; exact e2,
    by rw [hz, e2, e3, sub_beq_zero_nat (by omega_arith) (by omega_arith)],
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _)),
    by rw [u3.mem, u2.mem, u1.mem]⟩

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

theorem powerBatch_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  cases batch with
  | true => exact double16_ok hc hl hd
  | false =>
    refine WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hh⟩ => ?_
    exact ⟨hlt, hv, hh, IKeep.of_keep hk⟩

theorem powersBody_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) (o j count : Nat) (hlo : 1632 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (powersBody o count batch) s fun t => t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧
      t.z = decide (j + 1 = count) ∧ AllLim t.mem b ∧
      tablePoint t.mem b (o + 128 * j) = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧
      PowersKeep b (o + 128 * j) 128 s t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hc o j (by omega_arith) (by omega_arith) h11) fun t ⟨htp, htr, htm⟩ => ?_
  have hct := hc.of_rest htr (by decide)
  refine WP.mono (pointToTable_ok hct (by rw [htm]; exact hl) htp (by omega_arith) (by omega_arith))
    fun u ⟨hut, huk⟩ => ?_
  have heu : env u.mem b = env s.mem b := (huk.env (by omega_arith) (by omega_arith)).trans
    (congrArg (fun m => env m b) htm)
  refine WP.seq (WP.mono (powerBatch_ok (huk.ctx hct)
    (huk.lim (by omega_arith) (by omega_arith) (by rw [htm]; exact hl)) (by rw [heu]; exact hd) batch)
    fun v ⟨hvl, hvp, hvhi, hvk⟩ => ?_)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hvk.rest.gpr _ (by decide), huk.rest.gpr _ (by decide), htr.gpr _ (by decide), h11]
  refine WP.mono (powersNext_ok v j count hj hn hvc) fun w ⟨hwc, hwz, hwr, hwm⟩ => ?_
  refine ⟨hwc, hwz, by rw [hwm]; exact hvl, ?_, ?_, ?_, ?_⟩
  · rw [hwm, workspace_tablePoint hvk.frame (by omega_arith) (by omega_arith), hut, htm]
  · rw [hwm, hvp, heu]
  · intro i hi
    rw [hwm, hvhi i hi, heu]
  · refine ⟨(htr.mono (by decide)).trans ((huk.rest.mono (by decide)).trans
      ((hvk.rest.mono (by decide)).trans (hwr.mono (by decide)))), ?_⟩
    rw [hwm, ← htm]
    exact (TableFrame.table huk.frame).trans (TableFrame.workspace hvk.frame)

end VG.Proof.Ed25519.Arm
