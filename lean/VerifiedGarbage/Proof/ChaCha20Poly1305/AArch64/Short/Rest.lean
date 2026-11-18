module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.ShortRest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk

/-! ### `ChaCha20Poly1305.AArch64.Stitched.Rest`, which the modules that import this one used -/

section

/-! ### `ChaCha20Poly1305.AArch64.Stitched.Crypt`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the chunks in the context

`Stitch.bulk` runs on the regions of the stream (the ChaCha20 state, the data
and the working space, as `vg_chacha20_xor`'s contract gives them), which the
context and the data contain (`WP.narrow`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked BPre Acc bulk_ok)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

variable {sve : Bool}

@[simp] theorem withRegions_v (s : State) (rd wr : List Region) : (s.withRegions rd wr).v = s.v := rfl

/-- The data from byte `o`. -/
abbrev dRo (s₀ : State) (o : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 o, L s₀ - o⟩

theorem dRo_sub (s₀ : State) {o : Nat} (ho : o ≤ L s₀) : Region.Sub (dRo s₀ o) (dR s₀) :=
  Offset.sub_base _ (by omega_using [ho])

/-- The destination from byte `o`. -/
abbrev qRo (s₀ : State) (Q : Addr) (o : Nat) : Region := ⟨Q + BitVec.ofNat 64 o, L s₀ - o⟩

/-- The stream's regions in the context, with the destination from byte `o`. -/
abbrev streamR (s₀ : State) (Q : Addr) (o : Nat) : List Region := [sub s₀ 64 64, qRo s₀ Q o, sub s₀ 128 320]

theorem toNat_off_le {p : Addr} {o L : Nat} (hw : p.toNat + L ≤ 2 ^ 64) (ho : o ≤ L) (hL : L < 2 ^ 64) :
    (p + BitVec.ofNat 64 o).toNat + (L - o) ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, hL])]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega_using [hw, ho])

theorem bulk_bpre {s₀ : State} (hp : APre e s₀) {Q : Addr} (hq : DstR s₀ Q) {o : Nat} (ho : o ≤ L s₀)
    {s : State} (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o)) (hx3 : s.gpr .x3 = off (cx s₀) 128)
    (hx4 : s.gpr .x4 = Q + BitVec.ofNat 64 o) :
    BPre (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := by
  have hsub := dRo_sub s₀ ho
  have hqsub : Region.Sub (qRo s₀ Q o) ⟨Q, L s₀⟩ := Offset.sub_base _ (by omega_using [ho])
  have hst : (sub s₀ 64 64).Disjoint (dRo s₀ o) :=
    (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hsub
  have hsq : (sub s₀ 64 64).Disjoint (qRo s₀ Q o) :=
    (hq.ctx.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hqsub
  have hsb : (sub s₀ 64 64).Disjoint (sub s₀ 128 320) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hdb : (dRo s₀ o).Disjoint (sub s₀ 128 320) :=
    (hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hsub
  have hqb : (qRo s₀ Q o).Disjoint (sub s₀ 128 320) :=
    (hq.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hqsub
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL : L s₀ - o < 2 ^ 64 := by omega_using [hL5]
  have hw : (dp s₀ + BitVec.ofNat 64 o).toNat + (L s₀ - o) ≤ 2 ^ 64 := toNat_off_le hp.wrap_d ho hL5
  have hwq : (Q + BitVec.ofNat 64 o).toNat + (L s₀ - o) ≤ 2 ^ 64 := toNat_off_le hq.wrap ho hL5
  have hal : Q + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 o ∨ (dRo s₀ o).Disjoint (qRo s₀ Q o) := by
    rcases hq.same with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left hsub).sub_right hqsub)
  have e1 : (s.withRegions [dRo s₀ o] (streamR s₀ Q o)).gpr .x1 = dp s₀ + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, hx1]
  have e2 : VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = L s₀ - o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hL]
  have e0 : VG.Proof.ChaCha20.AArch64.Xor.st (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = off (cx s₀) 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, hx0]
  have e3 : VG.Proof.ChaCha20.AArch64.Xor.bp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = off (cx s₀) 128 := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.bp, State.withRegions_gpr, hx3]
  have e4 : VG.Proof.ChaCha20.AArch64.Xor.tp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = Q + BitVec.ofNat 64 o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.tp, State.withRegions_gpr, hx4]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Xor.stR, VG.Proof.ChaCha20.AArch64.Xor.dR,
      VG.Proof.ChaCha20.AArch64.Xor.tR, VG.Proof.ChaCha20.AArch64.Xor.bR,
      VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_rd, State.withRegions_wr, e0, e1, e2, e3, e4]
  -- The goals `simp only` leaves, in the order of `BPre`'s fields: each fact where it fits, rather than tried
  -- on every goal, where an `exact` between two other regions unfolds them before it fails.
  exacts [hst, hsq, hsb, hdb, hqb, hal, hw, hwq, by simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]]

/-- The chunks, on the context's regions, from byte `o` of the data to byte `o`
of the destination `Q`. -/
theorem bulkA_ok (enc : Bool) {s₀ : State} (hp : APre e s₀) {Q : Addr} (hq : DstR s₀ Q)
    (hin : enc = true → Q = dp s₀) {o : Nat} (ho : o ≤ L s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o))
    (hx3 : s.gpr .x3 = off (cx s₀) 128) (hx4 : s.gpr .x4 = Q + BitVec.ofNat 64 o) (hL : 512 ≤ L s₀ - o)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {R a : Nat} (ha : Acc R a s) :
    WP isa (Stitch.bulk sve enc) s fun u =>
      (∃ T, Bulked enc R a (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) T
        (u.withRegions [dRo s₀ o] (streamR s₀ Q o))) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame (streamR s₀ Q o) s.mem u.mem := by
  have hb := bulk_bpre hp hq ho hx0 hx1 hx2 hx3 hx4
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hLo : L s₀ - o < 2 ^ 64 := by omega_using [hL5]
  have hL' : 512 ≤ VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hLo]; exact hL
  have hin' : enc = true → VG.Proof.ChaCha20.AArch64.Xor.tp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) =
      VG.Proof.ChaCha20.AArch64.Xor.dp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := fun he => by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.tp, VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_gpr,
      hx1, hx4, hin he]
  have ha' : Acc R a (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := ⟨ha.h, ha.h2, ha.key, ha.k0, ha.k1⟩
  have hw : Covers (streamR s₀ Q o) s.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega_using []⟩
    · exact ⟨⟨Q, L s₀⟩, hq.wr, o, rfl, by show o + (L s₀ - o) ≤ L s₀; omega_using [ho]⟩
    · exact ⟨ctxR s₀, hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega_using []⟩
  have hr : Covers [dRo s₀ o] (s.rd ++ s.wr) := by
    rw [hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, hp.d_in, o, rfl, by show o + (L s₀ - o) ≤ L s₀; omega_using [ho]⟩
  refine WP.narrow (bulk_ok enc hb hin' hL' ha') (Covers.append_left hr (Covers.right hw)) hw ?_
    (by cases sve <;> cases enc <;> decide +kernel)
  intro u hrd' hwr' hsp hf hu
  exact ⟨hu, hrd', hwr', hsp, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64

end

end

/-! ### `ChaCha20Poly1305.AArch64.Stitched.Crypted`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `cryptStitched`

From the state after the data's first `o` bytes (a multiple of 64) were
encrypted from counter 1 and absorbed, with the counter past them and `x22`,
`x23` pointing after them (`Entry`): after `T` chunks (none for fewer than
512 bytes after them), the data's first `o + 512 T` bytes encrypted from
counter 1, the counter advanced past them, the stream's arguments set to the
rest, and the bytes absorbed (`pre`) and the rest's pointer and length in
`x22`, `x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked Acc rebase rebase_of)
open VG.Proof.ChaCha20 (ctr)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov wp_str32)
open VG.Proof.Poly1305 (absorbAll)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

variable {sve : Bool}

/-- The bytes absorbed after `T` chunks from byte `o`: all of them when
decrypting, all but the last chunk when encrypting. -/
def pre (o : Nat) (enc : Bool) (T : Nat) : Nat := o + if enc then 512 * (T - 1) else 512 * T

theorem pre_le (o : Nat) (enc : Bool) (T : Nat) : pre o enc T ≤ o + 512 * T := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega_using []

theorem pre_zero (o : Nat) (enc : Bool) : pre o enc 0 = o := by
  cases enc <;> simp [pre]

theorem pre_mod {o : Nat} (ho : o % 16 = 0) (enc : Bool) (T : Nat) : pre o enc T % 16 = 0 := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega_using [ho]

/-- The keystream from counter 1. -/
abbrev KS1 (s₀ : State) : List Byte :=
  keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)

/-- The keystream after `q` blocks continues the one from counter 1. -/
theorem ks1_off (s₀ : State) {q k : Nat} (hk : 64 * q + k < L s₀) :
    (keystream (ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) q) (L s₀ - 64 * q)).getD k 0 =
      (KS1 s₀).getD (64 * q + k) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega_using [hk]), VG.Proof.ChaCha20.keystream_getD _ hk,
    VG.Proof.ChaCha20.ctr_ctr, show q + k / 64 = (64 * q + k) / 64 by omega_using [],
    show k % 64 = (64 * q + k) % 64 by omega_using []]

/-- What `cryptStitched` starts from: the data's first `o` bytes (a multiple
of 64) encrypted from `s` into the output and absorbed, the counter past them,
the data after them as in `s`, and `x22`, `x23` the data after them. -/
structure Entry (enc : Bool) (o : Nat) (s₀ s : State) (key msg : List Byte) (w : State) : Prop where
  inv : Inv0 enc s₀ w
  o64 : o % 64 = 0
  le : o ≤ L s₀
  x22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 o
  x23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - o)
  st : stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64)
  data : ∀ k < L s₀, o ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k)
  out : ∀ k < o, w.mem (op enc s₀ + BitVec.ofNat 64 k) =
    s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
  mac : Repr w.mem (off (cx s₀) 448) key (msg ++ bytesAt (if enc then w.mem else s.mem) (dp s₀) o)
  vec : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- What `cryptStitched` leaves, after `T` chunks from byte `o`, from `s` (its
data and Poly1305's message) and `w` (the rest of memory): the data's first
`o + 512 T` bytes encrypted into the output, and the data after them as in
`s`. -/
structure Crypted (enc : Bool) (o : Nat) (s₀ s w : State) (key msg : List Byte) (T : Nat) (u : State) :
    Prop where
  inv : Inv0 enc s₀ u
  le : o + 512 * T ≤ L s₀
  lt : L s₀ - (o + 512 * T) < 512
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (o + 512 * T)
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - (o + 512 * T))
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 (pre o enc T)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - pre o enc T)
  cnt : stateAt u.mem (off (cx s₀) 64) =
    ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64 + 8 * T)
  data : ∀ k < L s₀, o + 512 * T ≤ k → u.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k)
  out : ∀ k < o + 512 * T, u.mem (op enc s₀ + BitVec.ofNat 64 k) =
    s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
  frame : Frame [sub s₀ 64 408, sub s₀ 32 16, oR enc s₀] w.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key
    (msg ++ bytesAt (if enc then u.mem else s.mem) (dp s₀) (pre o enc T))
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- `Crypted`'s data in place (`seal`): the first `o + 512 T` bytes encrypted. -/
theorem Crypted.dataAt {o : Nat} {s₀ s w : State} {key msg : List Byte} {T : Nat} {u : State}
    (h : Crypted true o s₀ s w key msg T u) : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < o + 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
  by_cases hkp : k < o + 512 * T
  · rw [ite_eq_left hkp]; exact h.out k hkp
  · rw [ite_eq_right hkp]; exact h.data k hk (by omega_using [hkp])

/-- `Entry`, from its data in place (`seal`). -/
theorem Entry.ofAt {o : Nat} {s₀ s : State} {key msg : List Byte} {w : State}
    (inv : Inv0 true s₀ w) (o64 : o % 64 = 0) (le : o ≤ L s₀)
    (x22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 o) (x23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - o))
    (st : stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64))
    (data : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < o then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k))
    (mac : Repr w.mem (off (cx s₀) 448) key (msg ++ bytesAt w.mem (dp s₀) o))
    (vec : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    Entry true o s₀ s key msg w :=
  ⟨inv, o64, le, x22, x23, st, fun k hk hko => by rw [data k hk, ite_eq_right (by omega_using [hko])],
    fun k hk => by rw [op_true, data k (by omega_using [le, hk]), ite_eq_left hk], mac, vec⟩

/-! ## Helpers -/

/-- The vector registers other than `v8` and `v9` are kept. -/
theorem WP.otherV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true) :
    WP isa c s fun u => Q u ∧ ∀ r ∈ preservedV, r ≠ .v8 → r ≠ .v9 → u.v r = s.v r := by
  obtain ⟨t, u, he, hq⟩ := h
  exact ⟨t, u, he, hq, fun r hr h8 h9 => Exec.vec (fun i hi =>
    VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV_ne (List.all_eq_true.mp
      ((Code.allInstrs_eq _ c) ▸ hc) i hi) hr h8 h9) he⟩

theorem bulk_otherV (sve enc : Bool) :
    (Stitch.bulk sve enc).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases sve <;> cases enc
  · show Stitch.bulkOpen.allInstrs _ = true; lit_decide
  · show Stitch.bulkSeal.allInstrs _ = true; lit_decide
  · show Stitch.bulkOpenSve.allInstrs _ = true; lit_decide
  · show Stitch.bulkSealSve.allInstrs _ = true; lit_decide

/-- A byte of the data outside a frame of the context. -/
theorem data_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {k : Nat} (hk : k < L s₀) :
    m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k) :=
  hf.bytes hd (Nat.le_of_lt (s₀.gpr .x5).isLt) hk

/-- A byte of the output `Q` outside a frame. -/
theorem out_frame {s₀ : State} {Q : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨Q, L s₀⟩ : Region).Disjoint r) {k : Nat} (hk : k < L s₀) :
    m' (Q + BitVec.ofNat 64 k) = m (Q + BitVec.ofNat 64 k) :=
  hf.bytes hd (Nat.le_of_lt (s₀.gpr .x5).isLt) hk

/-- The state after `cryptSetup`. -/
theorem setup_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block cryptSetup) w fun s₂ =>
      s₂.gpr .x0 = off (cx s₀) 64 ∧ s₂.gpr .x1 = w.gpr .x22 ∧ s₂.gpr .x2 = w.gpr .x23 ∧
      s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if (w.gpr .x23).toNat < 512 then 1 else 0) ∧
      Kept [] w s₂ ∧ s₂.mem = w.mem ∧
      ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  obtain core : WP isa (.block cryptSetup) w fun s₂ =>
      s₂.gpr .x0 = off (cx s₀) 64 ∧ s₂.gpr .x1 = w.gpr .x22 ∧ s₂.gpr .x2 = w.gpr .x23 ∧
      s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if (w.gpr .x23).toNat < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s₂.gpr r = w.gpr r) ∧
      s₂.mem = w.mem ∧ s₂.rd = w.rd ∧ s₂.wr = w.wr := by
    obtain c₁ : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128])
        w fun s₁ => s₁.gpr .x0 = off (cx s₀) 64 ∧ s₁.gpr .x1 = w.gpr .x22 ∧
          s₁.gpr .x2 = w.gpr .x23 ∧ s₁.gpr .x3 = off (cx s₀) 128 ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₁.gpr r = w.gpr r) ∧
          s₁.mem = w.mem ∧ s₁.rd = w.rd ∧ s₁.wr = w.wr :=
      wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
        wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
          ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
            by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
            by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
            by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
            fun r h0 h1 h2 h3 => by rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0],
            by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
            by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    refine WP.block_append (c₁.mono fun s₁ ⟨x0₁, x1₁, x2₁, x3₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.check_ok s₁).mono
      fun s₂ ⟨x5₂, g₂, m₂, rd₂, wr₂, _, _⟩ => ?_
    exact ⟨by rw [g₂ _ (by decide), x0₁], by rw [g₂ _ (by decide), x1₁], by rw [g₂ _ (by decide), x2₁],
      by rw [g₂ _ (by decide), x3₁], by rw [x5₂, x2₁],
      fun r h0 h1 h2 h3 h5 => by rw [g₂ r h5, g₁ r h0 h1 h2 h3], by rw [m₂, m₁], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
  refine (WP.preservedV (WP.withSp core) (by lit_decide)).mono
    fun s₂ ⟨⟨⟨x0, x1, x2, x3, x5, g, m, rd, wr⟩, sp⟩, hv⟩ => ⟨x0, x1, x2, x3, x5,
      ⟨fun r hr _ => g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
        (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
        (by rintro rfl; exact absurd hr (by decide)), sp, rd, wr, by rw [m]; exact Frame.refl _ _⟩, m, hv⟩

/-- `counterOne`: the counter set to 1. -/
theorem counterOne_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv e s₀ s) :
    WP isa (.block counterOne) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ Kept [sub s₀ 64 64] s s' ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  obtain core : WP isa (.block counterOne) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    exact WP.block_nil ⟨by rw [g₂.mem, u₁.gpr, u₁.mem, one32], by rw [g₂.rd, u₁.rd], by rw [g₂.wr, u₁.wr]⟩
  refine WP.mono (WP.preservedV (WP.kept core rfl) (by lit_decide))
    fun s' ⟨⟨⟨hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ => ⟨hm, Kept.of hg hsp hrd hwr ?_, hv⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The ChaCha20 state after `counterOne`: counter 1. -/
theorem setup_cnt {s₀ : State} {s : State}
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    stateAt (s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (off (cx s₀) 64) =
      Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
  rw [show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, hst, set12_initState]

/-- After the lengths and `counterOne`, `cryptStitched` starts from the data's
first byte. -/
theorem entry_zero (enc : Bool) {s₀ : State} {s w : State} (h : Inv enc s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg)
    (hm : w.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (hk : Kept [sub s₀ 64 64] s w) :
    Entry enc 0 s₀ w key msg w := by
  refine ⟨(h.step1 hk (by lit_omega) (by lit_omega) (by lit_omega)).inv0, by decide, Nat.zero_le _, ?_, ?_,
    ?_, fun _ _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k), ?_, fun _ _ => rfl⟩
  · rw [hk.cs _ (pres .x22) (pres30 .x22), h.x22, Poly1305.AArch64.add_ofNat_zero]
  · rw [hk.cs _ (pres .x23) (pres30 .x23), h.x23, Nat.sub_zero, hL]
  · rw [hm, setup_cnt hst, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [Stitch.bytesAt_zero, List.append_nil]
    exact Repr.frame hk.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr

theorem Inv0.kept {s₀ s s' : State} (h : Inv0 e s₀ s) (hk : Kept [] s s') : Inv0 e s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

/-- No chunks: fewer than 512 bytes from byte `o`. -/
theorem short_crypted (enc : Bool) {s₀ : State} {o : Nat} {s w : State} {key msg : List Byte}
    (E : Entry enc o s₀ s key msg w) {s₂ : State}
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = w.gpr .x22) (x2₂ : s₂.gpr .x2 = w.gpr .x23)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [] w s₂) (m₂ : s₂.mem = w.mem)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64)
    (hs : L s₀ - o < 512) :
    Crypted enc o s₀ s w key msg 0 s₂ := by
  obtain h22 : s₂.gpr .x22 = w.gpr .x22 := k₂.cs _ (pres .x22) (pres30 .x22)
  obtain h23 : s₂.gpr .x23 = w.gpr .x23 := k₂.cs _ (pres .x23) (pres30 .x23)
  refine ⟨E.inv.kept k₂, by have := E.le; omega_using [this], by omega_using [hs], x0₂, ?_, ?_, x3₂, ?_, ?_, ?_, fun k hk hko => ?_,
    fun k hk => ?_, ?_, ?_, fun r hr => (v₂ r hr).trans (E.vec r hr)⟩
  · rw [x1₂, E.x22, Nat.mul_zero, Nat.add_zero]
  · rw [x2₂, E.x23, Nat.mul_zero, Nat.add_zero]
  · rw [pre_zero, h22, E.x22]
  · rw [pre_zero, h23, E.x23]
  · rw [m₂, E.st, Nat.mul_zero, Nat.add_zero]
  · rw [Nat.mul_zero, Nat.add_zero] at hko; rw [m₂]; exact E.data k hk hko
  · rw [Nat.mul_zero, Nat.add_zero] at hk; rw [m₂]; exact E.out k hk
  · rw [m₂]; exact Frame.refl _ _
  · rw [pre_zero, m₂]; exact E.mac

/-! ## The accumulator in registers -/

theorem h2_le {a b c : Nat} (h : a + 2 ^ 64 * b + 2 ^ 128 * c < Spec.Poly1305.P) : c ≤ 4 := by
  obtain h₁ : 2 ^ 128 * c < 2 ^ 128 * 5 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h₁)

/-- The accumulator's words, from the 24 bytes. -/
theorem leNum_words (m : Mem) (c : Addr) :
    VG.Spec.Poly1305.leNum (bytesAt m (off c 448) 24) = (m.readW (off c 448) 64).toNat +
      2 ^ 64 * (m.readW (off c 456) 64).toNat + 2 ^ 128 * (m.readW (off c 464) 64).toNat := by
  rw [Poly1305.AArch64.leNum_acc]
  simp only [Poly1305.AArch64.w64, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The key's clamped words, as `polyIn` stores them. -/
theorem clamp_words (m : Mem) (c : Addr) :
    Poly1305.AArch64.Rk m (off c 448) = (m.readW (off c 472) 64 &&& M0).toNat +
      2 ^ 64 * (m.readW (off c 480) 64 &&& M1).toNat := by
  simp only [Poly1305.AArch64.Rk, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memIn_288 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 288) 64 = m.readW (off c 472) 64 &&& M0 := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64]

theorem memIn_296 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 296) 64 = m.readW (off c 480) 64 &&& M1 := by
  rw [memIn, Mem.readW_writeW_self64]

theorem memIn_800 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 32) 64 = a := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

theorem memIn_808 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 40) 64 = b := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

/-- The words `polyIn` stores. -/
abbrev inR (s₀ : State) : List Region := [sub s₀ 288 16, sub s₀ 32 16]

theorem memIn_frame {s₀ : State} (m : Mem) (a b : BitVec 64) :
    Frame (inR s₀) m (memIn m (cx s₀) a b) := by
  have c (k d : Nat) (h₁ : k ≤ d) (h₂ : d + 8 ≤ k + 16) (h₃ : k + 16 ≤ 1280) :
      (sub s₀ k 16).Contains (off (cx s₀) d) (64 / 8) :=
    contains_sub s₀ h₁ h₂ h₃
  exact ((((Frame.refl _ m).writeW (by simp) _ (c 32 32 (by decide) (by decide) (by decide))).writeW
    (by simp) _ (c 32 40 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 288 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 296 (by decide) (by decide) (by decide))

theorem storeHm_frame (m : Mem) (p : Addr) (w0 w1 w2 : BitVec 64) :
    Frame [⟨p, 24⟩] m (Poly1305.AArch64.storeHm m p w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (Poly1305.AArch64.hR p).Contains (Poly1305.AArch64.off p d) (64 / 8) :=
    fun d hd => Poly1305.AArch64.hR_contains p hd
  exact (((Frame.refl _ m).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

/-- The pointer and length of the data not yet absorbed. -/
theorem restP_eq (enc : Bool) (d : Addr) {o L T : Nat} (hT : 1 ≤ T) (hle : o + 512 * T ≤ L) :
    restP enc (d + BitVec.ofNat 64 (o + 512 * T)) (BitVec.ofNat 64 (L - (o + 512 * T))) =
      (d + BitVec.ofNat 64 (pre o enc T), BitVec.ofNat 64 (L - pre o enc T)) := by
  cases enc
  · rfl
  · simp only [restP, pre, ite_true]
    obtain e : o + 512 * T = o + 512 * (T - 1) + 512 := by omega_using [hT]
    refine Prod.ext ?_ ?_
    · show d + BitVec.ofNat 64 (o + 512 * T) - BitVec.ofNat 64 512 = _
      rw [e, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    · show BitVec.ofNat 64 (L - (o + 512 * T)) + BitVec.ofNat 64 512 = _
      rw [← BitVec.ofNat_add]; congr 1; omega_using [hT, hle]

/-- The accumulator `polyIn` loads. -/
theorem acc_in {s₀ s₂ s₃ : State} {key msg : List Byte}
    (hr : Repr s₂.mem (off (cx s₀) 448) key msg) (x0₃ : s₃.gpr .x0 = off (cx s₀) 64)
    (a21 : s₃.gpr .x21 = s₂.mem.readW (off (cx s₀) 448) 64)
    (a22 : s₃.gpr .x22 = s₂.mem.readW (off (cx s₀) 456) 64)
    (a23 : s₃.gpr .x23 = s₂.mem.readW (off (cx s₀) 464) 64)
    {a b : BitVec 64} (m₃ : s₃.mem = memIn s₂.mem (cx s₀) a b) :
    Acc (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16)))
      (VG.Spec.Poly1305.accumulate (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg)
      s₃ := by
  have hA := hr.2.2
  rw [leNum_words] at hA
  obtain hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  obtain r0 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off =
      s₂.mem.readW (off (cx s₀) 472) 64 &&& M0 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 224 = off (cx s₀) 288 from off_off _ 64 224, memIn_288]
  obtain r1 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off =
      s₂.mem.readW (off (cx s₀) 480) 64 &&& M1 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 232 = off (cx s₀) 296 from off_off _ 64 232, memIn_296]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Poly.hval, a21, a22, a23]; rw [hA]
  · rw [a23]; rw [← hA] at hlt; exact h2_le hlt
  · simp only [Poly.rval, r0, r1]
    rw [← clamp_words, ← Poly1305.AArch64.clamp_key, Poly1305.AArch64.off_24]
    exact congrArg (fun k => VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (List.take 16 k))) hr.2.1
  · rw [r0]; exact Poly1305.AArch64.Radix64.key0_lt _
  · rw [r1]; exact Poly1305.AArch64.Radix64.key1_lt _

/-! ## The chunks -/

theorem data_ctx {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 1280) :
    (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

/-- A prefix of the data outside a frame of the context. -/
theorem prefix_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {n : Nat} (hn : n ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n :=
  bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hn))
    (Nat.le_trans hn (Nat.le_of_lt (s₀.gpr .x5).isLt))

/-- The saved `x27` and `x28` are outside the stream's regions. -/
theorem saved_bulk {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) {o : Nat} (ho : o ≤ L s₀) {m m' : Mem}
    (hf : Frame (streamR s₀ Q o) m m') {d : Nat}
    (hd : d = 32 ∨ d = 40) : m'.readW (off (cx s₀) d) 64 = m.readW (off (cx s₀) d) 64 := by
  refine hf.readW (r := sub s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
  obtain h₁ : d + 8 ≤ 1280 := by omega_using [hd]
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega_using [hd]) h₁ (by lit_omega)
  · exact (hq.ctx.sub_left (sub_ctx s₀ h₁)).sub_right (Offset.sub_base _ (by omega_using [ho]))
  · exact sub_disj s₀ (by omega_using [hd]) h₁ (by lit_omega)

/-- The output's first `o` bytes are outside the stream's regions. -/
theorem prefix_streamR {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) {o : Nat} (ho : o ≤ L s₀) :
    ∀ r ∈ streamR s₀ Q o, (⟨Q, o⟩ : Region).Disjoint r := by
  obtain hP : Region.Sub ⟨Q, o⟩ ⟨Q, L s₀⟩ := Region.sub_prefix ho
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hq.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hP
  · have := hq.wrap
    exact Offset.base_disjoint Q (Nat.le_refl o) (by omega_using [ho, this])
  · exact (hq.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hP

/-- The regions of the context `cryptStitched` writes, and the data. -/
theorem crypt_sub {s₀ : State} (r : Region) (k n : Nat) (h₁ : 64 ≤ k)
    (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
    ∃ r' ∈ [sub s₀ 64 408, sub s₀ 32 16, oR e s₀], Region.Sub r r' :=
  ⟨sub s₀ 64 408, List.mem_cons_self, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩

/-- At least 512 bytes from byte `o`: the chunks. -/
theorem long_crypted (enc : Bool) {s₀ : State} (hp : APre enc s₀) {o : Nat} {s w : State}
    {key msg : List Byte} (E : Entry enc o s₀ s key msg w) {s₂ : State}
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = w.gpr .x22) (x2₂ : s₂.gpr .x2 = w.gpr .x23)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [] w s₂) (m₂ : s₂.mem = w.mem)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64)
    (hL : 512 ≤ L s₀ - o) :
    WP isa (.seq (.block (polyIn ++ [bulkDst (!enc)])) (.seq (Stitch.bulk sve enc) (.block (polyEnd enc)))) s₂
      fun u => ∃ T, 1 ≤ T ∧ Crypted enc o s₀ s w key msg T u := by
  obtain hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hL5
  have ho := E.le
  obtain o16 : o % 16 = 0 := by have := E.o64; omega_arith
  obtain i₂ := E.inv.kept k₂
  let msg' := msg ++ bytesAt (if enc then w.mem else s.mem) (dp s₀) o
  obtain hr₂ : Repr s₂.mem (off (cx s₀) 448) key msg' := by rw [m₂]; exact E.mac
  refine WP.seq (WP.block_append ((polyIn_ok hp i₂.x21 i₂.rd i₂.wr).mono
    fun s₃ ⟨⟨a21, a22, a23, m₃, g₃, rd₃, wr₃⟩, v₃, sp₃, _, _⟩ => (bulkDst_ok (!enc) s₃).mono
    fun t₃ ⟨x4t, gt, mt, rdt, wrt, spt, vt⟩ => ?_))
  obtain x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃ _ (by decide), x0₂]
  obtain x1₃ : s₃.gpr .x1 = dp s₀ + BitVec.ofNat 64 o := by rw [g₃ _ (by decide), x1₂, E.x22]
  obtain x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 (L s₀ - o) := by rw [g₃ _ (by decide), x2₂, E.x23]
  obtain x3₃ : s₃.gpr .x3 = off (cx s₀) 128 := by rw [g₃ _ (by decide), x3₂]
  obtain x0t : t₃.gpr .x0 = off (cx s₀) 64 := by rw [gt _ (by decide), x0₃]
  obtain x1t : t₃.gpr .x1 = dp s₀ + BitVec.ofNat 64 o := by rw [gt _ (by decide), x1₃]
  obtain x2t : t₃.gpr .x2 = BitVec.ofNat 64 (L s₀ - o) := by rw [gt _ (by decide), x2₃]
  obtain x3t : t₃.gpr .x3 = off (cx s₀) 128 := by rw [gt _ (by decide), x3₃]
  obtain x28₃ : s₃.gpr .x28 = s₀.gpr .x28 := by
    rw [g₃ _ (by decide), k₂.cs _ (by decide) (by decide), E.inv.un .x28 (by decide)]
  obtain x4t' : t₃.gpr .x4 = op enc s₀ + BitVec.ofNat 64 o := by rw [x4t, x1₃]; exact cond_out s₀ x28₃ o
  obtain ha := acc_in hr₂ x0₃ a21 a22 a23 m₃
  obtain hat : Acc _ _ t₃ := ha.of (fun r hr => gt r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) mt
  refine WP.seq ((WP.otherV (bulkA_ok enc hp hp.o (fun he => by subst he; rfl) ho x0t x1t x2t x3t x4t' hL
    (by rw [rdt, rd₃, i₂.rd]) (by rw [wrt, wr₃, i₂.wr]) hat)
    (bulk_otherV sve enc)).mono fun s₄ ⟨⟨⟨T, hB⟩, rd₄, wr₄, sp₄, f₄⟩, ov₄⟩ => ?_)
  rw [mt] at f₄
  have hi := hB.inv
  obtain x0₄ : s₄.gpr .x0 = off (cx s₀) 64 := by
    obtain e := hi.x0; simp only [State.withRegions_gpr, Stitch.st_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.st, x0t] at e; exact e
  obtain x1₄ : s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 (o + 512 * T) := by
    obtain e := hi.x1; simp only [State.withRegions_gpr, Stitch.dp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.dp, x1t] at e
    rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
  obtain hLB : VG.Proof.ChaCha20.AArch64.Xor.L (t₃.withRegions [dRo s₀ o] (streamR s₀ (op enc s₀) o)) = L s₀ - o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, x2t, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_arith)
  obtain x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - (o + 512 * T)) := by
    obtain e := hi.x2; simp only [State.withRegions_gpr, Stitch.L_rebase, hLB] at e
    rw [e, Nat.sub_sub]
  obtain x3₄ : s₄.gpr .x3 = off (cx s₀) 128 := by
    obtain e := hi.x3; simp only [State.withRegions_gpr, Stitch.bp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.bp, x3t] at e; exact e
  obtain le₄ : o + 512 * T ≤ L s₀ := by
    obtain e := hi.le; simp only [Stitch.L_rebase, hLB] at e; omega_arith
  obtain x4₄ : s₄.gpr .x4 = op enc s₀ + BitVec.ofNat 64 (o + 512 * T) := by
    obtain e := hi.x4; simp only [State.withRegions_gpr, Stitch.tp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.tp, x4t'] at e
    rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine (polyEnd_ok hp enc x0₄ (by rw [rd₄, rdt, rd₃, i₂.rd]) (by rw [wr₄, wrt, wr₃, i₂.wr])).mono
    fun s₅ ⟨⟨hv₅, m₅, x21₅, x27₅, x28₅, x22₅, x23₅, g₅, rd₅, wr₅⟩, vv₅, sp₅, _, _⟩ => ⟨T, hB.pos, ?_⟩
  -- Memory.
  obtain f₂₃ : Frame (inR s₀) s₂.mem s₃.mem := by rw [m₃]; exact memIn_frame _ _ _
  obtain f₄₅ : Frame [sub s₀ 448 24] s₄.mem s₅.mem := by rw [m₅]; exact storeHm_frame _ _ _ _ _
  obtain hF₂ : Frame [sub s₀ 64 408, sub s₀ 32 16, oR enc s₀] w.mem s₅.mem := by
    rw [← m₂]
    refine (f₂₃.sub ?_).trans ((f₄.sub ?_).trans (f₄₅.sub ?_)) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with hr | hr
      · exact crypt_sub r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 32 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact crypt_sub r 64 64 (by decide) (by decide) hr
      · exact ⟨oR enc s₀, by simp, hr ▸ (Offset.sub_base _ (by omega_using [hL]) : Region.Sub (qRo s₀ (op enc s₀) o) (oR enc s₀))⟩
      · exact crypt_sub r 128 320 (by decide) (by decide) hr
    · exact crypt_sub r 448 24 (by decide) (by decide) hr
  obtain hd₂₃ : ∀ r ∈ inR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)
  obtain hd₄₅ : ∀ r ∈ [sub s₀ 448 24], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)
  have d₀₃ (k : Nat) (hk : k < L s₀) :
      s₃.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) := by
    rw [data_frame f₂₃ hd₂₃ hk, m₂]
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64) := by
    rw [stateAt_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      m₂, E.st]
  -- The data and the counter.
  obtain hO₂₃ : ∀ r ∈ inR s₀, (oR enc s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hp.o.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))
  obtain hO₄₅ : ∀ r ∈ [sub s₀ 448 24], (oR enc s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.o.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))
  obtain hj : ∀ k, o ≤ k → k < L s₀ → k - o < VG.Proof.ChaCha20.AArch64.Xor.L
      (t₃.withRegions [dRo s₀ o] (streamR s₀ (op enc s₀) o)) := fun k h₁ h₂ => by
    rw [hLB]; omega_arith
  obtain ek : ∀ X : Addr, ∀ k, o ≤ k → X + BitVec.ofNat 64 o + BitVec.ofNat 64 (k - o) = X + BitVec.ofNat 64 k :=
    fun X k h => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h]
  obtain data₅ : ∀ k < L s₀, o + 512 * T ≤ k →
      s₅.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk hkT
    rw [data_frame f₄₅ hd₄₅ hk]
    obtain e := hi.src (k - o) (hj k (by omega_arith) hk) (by omega_arith)
    simp only [Stitch.dp_rebase, Stitch.D0_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.D0, VG.Proof.ChaCha20.AArch64.Xor.dp,
      State.withRegions_gpr, x1t, mt] at e
    rw [ek _ k (by omega_arith)] at e
    rw [e, d₀₃ k hk, E.data k hk (by omega_arith)]
  obtain out₅ : ∀ k < o + 512 * T, s₅.mem (op enc s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0 := by
    intro k hk
    obtain hkL : k < L s₀ := by omega_arith
    rw [out_frame f₄₅ hO₄₅ hkL]
    by_cases hko : k < o
    · rw [f₄.bytes (prefix_streamR hp.o ho) (Nat.le_trans ho hL') hko, out_frame f₂₃ hO₂₃ hkL, m₂,
        E.out k hko]
    · have e := hi.data (k - o) (hj k (by omega_arith) hkL)
      simp only [Stitch.tp_rebase, Stitch.D0_rebase, Stitch.T0_rebase, Stitch.KS_rebase] at e
      simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.D0, VG.Proof.ChaCha20.AArch64.Xor.KS,
        VG.Proof.ChaCha20.AArch64.Xor.S0, VG.Proof.ChaCha20.AArch64.Xor.dp, VG.Proof.ChaCha20.AArch64.Xor.tp,
        VG.Proof.ChaCha20.AArch64.Xor.T0, mt,
        VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0t, x1t, x4t', hLB, st₃] at e
      obtain o64 : 64 * (o / 64) = o := by have := E.o64; omega_arith
      obtain ks := ks1_off s₀ (q := o / 64) (k := k - o) (by omega_arith)
      rw [o64, Nat.add_sub_cancel' (by omega_arith)] at ks
      rw [ek _ k (by omega_arith), ek _ k (by omega_arith), d₀₃ k hkL, E.data k hkL (by omega_arith), ks,
        ite_eq_left (by omega_arith)] at e
      exact e
  obtain cnt₅ : stateAt s₅.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64 + 8 * T) := by
    have e := hi.cnt
    simp only [Stitch.st_rebase, Stitch.S0_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.S0, mt,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0t, st₃] at e
    rw [stateAt_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), e, VG.Proof.ChaCha20.ctr_ctr]
  have r₄ (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₄.mem.readW (off (cx s₀) d) 64 = s₃.mem.readW (off (cx s₀) d) 64 := saved_bulk hp.o ho f₄ hd
  obtain un₅ : ∀ r ∈ untouched, s₅.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h5 : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x27, .x28])
        (h3 : r ∉ [Reg.x21, .x22, .x23, .x24, .x25]) (hu : r ∈ untouched) :
        s₅.gpr r = s₀.gpr r := by
      obtain e := hi.cs r hc
      simp only [State.withRegions_gpr] at e
      rw [g₅ r h5, e, rebase_of hn, State.withRegions_gpr, gt r (by
        intro he; subst he; exact absurd (List.mem_cons_self) h5), g₃ r h3,
        k₂.cs r hc (untouched_preserved r hu).2, E.inv.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 32 ∨ d = 40) (hu : r ∈ untouched)
        (hx : s₅.gpr r = s₄.mem.readW (off (cx s₀) d) 64)
        (hm : (memIn s₂.mem (cx s₀) (s₂.gpr .x27) (s₂.gpr .x28)).readW (off (cx s₀) d) 64 = s₂.gpr r) :
        s₅.gpr r = s₀.gpr r := by
      rw [hx, r₄ d hd, m₃, hm, k₂.cs r (untouched_preserved r hu).1 (untouched_preserved r hu).2,
        E.inv.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 32 (.inl rfl) (by decide) x27₅ (memIn_800 _ _ _ _)
    · rcases Bool.eq_false_or_eq_true enc with he | he
      · rw [he, Bool.cond_true] at x28₅
        exact x2728 _ 40 (.inr rfl) (by decide) x28₅ (memIn_808 _ _ _ _)
      · show s₅.gpr .x28 = s₀.gpr .x28
        rw [he, Bool.cond_false] at x28₅
        rw [he] at x4₄
        rw [x28₅, x4₄, x1₄, op_false, qp, sub_off_eq]
  obtain hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg'
  have ac₄ := hB.acc
  obtain hX := hv₅ ac₄.h2
  rw [show hacc s₄ = Poly.hval (s₄.withRegions [dRo s₀ o] (streamR s₀ (op enc s₀) o)) from rfl, ac₄.h,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr₂.2.1
  rw [k24] at hr1
  obtain hm16 : msg.length % 16 = 0 := by
    have := hr₂.1; simp only [msg', List.length_append, Poly1305.length_bytesAt] at this; omega_arith
  -- The bytes absorbed, in the order Poly1305 takes them.
  obtain habs : (msg ++ bytesAt (if enc then s₅.mem else s.mem) (dp s₀) (pre o enc T)) =
      msg' ++ (if enc then bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1))
        else bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 o) (512 * T)) := by
    simp only [msg', List.append_assoc]
    refine congrArg (msg ++ ·) ?_
    cases enc
    · simp only [Bool.false_eq_true, ite_false, pre]
      rw [Poly1305.bytesAt_add]
      refine congrArg (_ ++ ·) ?_
      simp only [bytesAt]
      apply List.map_congr_left
      intro i hi
      obtain hi := List.mem_range.mp hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, d₀₃ (o + i) (by omega_arith),
        E.data (o + i) (by omega_arith) (by omega_arith)]
    · simp only [ite_true, pre]
      obtain hP : Region.Sub ⟨dp s₀, o⟩ (dR s₀) := Region.sub_prefix ho
      obtain e1 : bytesAt s₅.mem (dp s₀) o = bytesAt w.mem (dp s₀) o := by
        rw [bytesAt_frame f₄₅ (p := dp s₀) (n := o) (fun r hr => (hd₄₅ r hr).sub_left hP) (by omega_arith),
          bytesAt_frame f₄ (p := dp s₀) (n := o) (prefix_streamR hp.o ho) (by omega_arith),
          bytesAt_frame f₂₃ (p := dp s₀) (n := o) (fun r hr => (hd₂₃ r hr).sub_left hP) (by omega_arith), m₂]
      obtain e2 : bytesAt s₅.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1)) =
          bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1)) :=
        bytesAt_frame f₄₅ (fun r hr => (hd₄₅ r hr).sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      rw [Poly1305.bytesAt_add, e1, e2]
  refine ⟨⟨x21₅, un₅, by rw [sp₅, sp₄, spt, sp₃, k₂.sp, E.inv.sp], by rw [rd₅, rd₄, rdt, rd₃, i₂.rd],
      by rw [wr₅, wr₄, wrt, wr₃, i₂.wr], E.inv.saved.frame hF₂ ?_, E.inv.frame.trans (hF₂.sub ?_)⟩,
    le₄, by have e := hB.rest; rw [hLB] at e; omega_arith, by rw [g₅ _ (by decide), x0₄],
    by rw [g₅ _ (by decide), x1₄], by rw [g₅ _ (by decide), x2₄],
    by rw [g₅ _ (by decide), x3₄], by rw [x22₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄],
    by rw [x23₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄], cnt₅, data₅, out₅, hF₂, ⟨?_, ?_, ?_⟩, fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.o.ctx.sub_left (sub_ctx s₀ (by lit_omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨oR enc s₀, by simp, fun _ h => h⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := pre_mod o16 enc T; omega_arith
  · rw [k24, bytesAt_frame hF₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.o.ctx.sub_left (sub_ctx s₀ (by lit_omega))) (by lit_omega), ← m₂]
    exact hr1
  · rw [m₅, Poly1305.AArch64.storeHm_acc, ← m₅]
    show Poly1305.AArch64.Radix64.hval s₅ = _
    rw [hX, habs, Poly1305.accumulate_append hr₂.1]
    cases enc
    · simp only [Bool.false_eq_true, ite_false, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1t, mt]
    · simp only [ite_true, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1t]
  · have e4 : s₄.v r = t₃.v r := by
      by_cases h8 : r = .v8
      · subst h8; simpa using hi.v8
      by_cases h9 : r = .v9
      · subst h9; simpa using hi.v9
      exact ov₄ r hr h8 h9
    rw [vv₅, e4, vt, v₃, ← (E.vec r hr)]; exact v₂ r hr

/-- The whole chunks, from byte `o`. -/
theorem cryptStitched_ok (enc : Bool) (he : enc = false) {s₀ : State} (hp : APre enc s₀) {o : Nat}
    {s w : State} {key msg : List Byte} (E : Entry enc o s₀ s key msg w) :
    WP isa (cryptStitched sve enc (!enc)) w fun u => ∃ T, Crypted enc o s₀ s w key msg T u := by
  unfold cryptStitched
  rw [show afterBulk sve enc = .block (polyEnd enc) by simp only [afterBulk, he, Bool.false_eq_true,
    ite_false]]
  obtain hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hLo : L s₀ - o < 2 ^ 64 := by omega_using [hL5]
  refine WP.seq ((setup_ok E.inv.x21).mono fun s₂ ⟨x0₂, x1₂, x2₂, x3₂, x5₂, k₂, m₂, v₂⟩ => ?_)
  rw [E.x23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLo] at x5₂
  apply WP.ite (decide (L s₀ - o < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro hs
    exact WP.block_nil ⟨0, short_crypted enc E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂ (of_decide_eq_true hs)⟩
  · intro hs
    exact (long_crypted enc hp E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂
      (by have := of_decide_eq_false hs; omega_using [this])).mono fun _ ⟨T, _, hc⟩ => ⟨T, hc⟩

/-! ## When encrypting -/

/-- What `cryptStitched` leaves when encrypting, from `s`: the data's first `P`
bytes encrypted from counter 1, the counter advanced past them if data
follows, the stream's arguments set to the rest, the first `A` bytes absorbed,
and the rest's pointer and length in `x22`, `x23`. -/
structure Sealed (s₀ s w : State) (key msg : List Byte) (P A : Nat) (u : State) : Prop where
  inv : Inv0 true s₀ u
  le : P ≤ L s₀
  aP : A ≤ P
  a16 : A % 16 = 0
  p64 : P < L s₀ → P % 64 = 0
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 P
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 A
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - A)
  cnt : P < L s₀ →
    stateAt u.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64)
  data : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] w.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key (msg ++ bytesAt u.mem (dp s₀) A)
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem Crypted.sealed {s₀ s w : State} {key msg : List Byte} {o T : Nat} {u : State}
    (h : Crypted true o s₀ s w key msg T u) (ho : o % 64 = 0) :
    Sealed s₀ s w key msg (o + 512 * T) (pre o true T) u :=
  ⟨h.inv, h.le, pre_le o true T, pre_mod (by omega_using [ho]) true T, fun _ => by omega_using [ho], h.x0, h.x1, h.x2, h.x3,
    h.x22, h.x23, fun _ => by rw [h.cnt, show (o + 512 * T) / 64 = o / 64 + 8 * T by omega_using []],
    fun k hk => by
      by_cases hkp : k < o + 512 * T
      · rw [ite_eq_left hkp]; exact h.out k hkp
      · rw [ite_eq_right hkp]; exact h.data k hk (by omega_using [hkp]),
    h.frame, by simpa only [ite_true] using h.mac, h.vec⟩

end VG.Proof.ChaCha20Poly1305.AArch64

end

end

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the rest of the data

`vg_chacha20_xor` (any backend) on the data after the first `P` bytes (the
chunks, and when encrypting with SVE2 up to 256 bytes more), from the counter
after them: the whole data encrypted from counter 1.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-- The data after its first `P` bytes. -/
abbrev restR (s₀ : State) (P : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 P, L s₀ - P⟩

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega_using [hk]) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt; omega_using [hk, h])

theorem not_rest {s₀ : State} {P k : Nat} (hk : k < P) (hP : P ≤ L s₀) :
    ¬ (restR s₀ P).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_using [hP, hL]) (by omega_using [hk, hP, hL])]
  split <;> omega_arith

/-- The keystream from block `q`. -/
theorem ks_shift (S : VG.Proof.ChaCha20.CState) {len q k : Nat} (hk : k < len) (hq : 64 * q ≤ k) :
    (keystream S len).getD k 0 =
      (Spec.ChaCha20.serialize (Spec.ChaCha20.block (ctr (ctr S q) ((k - 64 * q) / 64)))).getD
        ((k - 64 * q) % 64) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hk, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show q + (k - 64 * q) / 64 = k / 64 by omega_using [hq], show (k - 64 * q) % 64 = k % 64 by omega_using [hq]]

/-- The output after its first `P` bytes. -/
abbrev restQ (s₀ : State) (Q : Addr) (P : Nat) : Region :=
  ⟨Q + BitVec.ofNat 64 P, L s₀ - P⟩

theorem not_restQ {s₀ : State} {Q : Addr} {P k : Nat} (hk : k < P) (hP : P ≤ L s₀) :
    ¬ (restQ s₀ Q P).Contains (Q + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_using [hP, hL]) (by omega_using [hk, hP, hL])]
  split <;> omega_arith

/-- `bytesAt` of a destination XORed from a source. -/
theorem bytesAt_xor2 {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    Spec.ChaCha20.bytesAt m' q n = List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m p n) ks := by
  apply List.ext_getElem
  · simp [Spec.ChaCha20.bytesAt, hks]
  · intro k h₁ h₂
    simp only [Spec.ChaCha20.bytesAt, List.length_map, List.length_range] at h₁
    simp only [Spec.ChaCha20.bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]

/-- The data from `P`, encrypted from the counter after `P / 64` blocks (if
any data follows), into the output (`XorCallee.callWith (!e)`), whose first
`P` bytes are the data's encrypted. -/
theorem rest_callOut (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr) (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op e s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0) :
    WP isa (v.callee.callWith (!e)) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR e s₀] w s' ∧ Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P] w.mem s'.mem ∧
      bytesAt s'.mem (op e s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wo := hp.o.wrap
  have ts : Region.Sub (restQ s₀ (op e s₀) P) (oR e s₀) := Offset.sub_base _ (by omega_using [hle])
  refine xor_callOut v hp hrd hwr h28 hx0 hx1 hx2 hx3 (by omega_using [hle]) fun s' v' k' d' => ?_
  refine ⟨v', ?_, ?_, ?_⟩
  · refine k'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨oR e s₀, by simp, ts⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨restQ s₀ (op e s₀) P, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine bytesAt_xor2 (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < P
    · have hin : (oR e s₀).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        Offset.contains_base _ (by omega_using [hk]) (by omega_using [hL, hk])
      have hs : ¬ (⟨off (cx s₀) 64, 64⟩ : Region).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.o.ctx.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)) _ hh hin
      have hb : ¬ (⟨off (cx s₀) 128, 320⟩ : Region).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.o.ctx.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)) _ hh hin
      rw [k'.frame _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hs
        · exact not_restQ hk' hle
        · exact hb), hout k hk']
    · have hPL : P < L s₀ := by omega_using [hk, hk']
      have h64 := hP hPL
      have ea : ∀ X : Addr, X + BitVec.ofNat 64 P + BitVec.ofNat 64 (k - P) = X + BitVec.ofNat 64 k := fun X => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega_using [hk'])]
      have x := VG.Proof.ChaCha20.AArch64.Xor.bytes_of_to
        (VG.Proof.ChaCha20.length_keystream _ _) d' (k := k - P) (by omega_using [hk, hk'])
      rw [ea, ea, hdata k hk (by omega_using [hk']), hcnt hPL, VG.Proof.ChaCha20.keystream_getD _ (by omega_using [hk, hk'])] at x
      rw [x, ks_shift _ hk (q := P / 64) (by omega_using [hk']), show 64 * (P / 64) = P by omega_using [hP, hPL]]

/-- `rest_callOut` in place (`seal`), from the data's first `P` bytes
encrypted in place. -/
theorem rest_call (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr) (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa v.callee.inPlace w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w s' ∧ Frame [sub s₀ 64 384, restR s₀ P] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) :=
  rest_callOut v hp hle hP hx0 hx1 hx2 hx3 hrd hwr h28 hcnt
    (fun k hk hkp => by rw [hdata k hk, ite_eq_right (by omega_using [hkp])])
    (fun k hk => by rw [op_true, hdata k (by omega_using [hle, hk]), ite_eq_left hk])

/-- The data before the rest is kept. -/
theorem prefix_rest {s₀ : State} (hp : APre e s₀) {m m' : Mem} {P n : Nat}
    (hf : Frame [sub s₀ 64 384, restR s₀ P] m m') (hn : n ≤ P) (hP : P ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 384) (by lit_omega)) _ hh
      (data_in (by omega_using [hn, hP, hi]))
  · exact not_rest (by omega_using [hn, hi]) hP

/-- `cryptRest`'s arguments: the stream's, from the context and `x22`, `x23`. -/
theorem restArgs_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128]) w
      fun w' => (w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
        w'.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w w') ∧
        ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23,
      .addImm .x .x3 .x21 128]) w fun w' =>
      w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
      w'.gpr .x3 = off (cx s₀) 128 ∧ w'.mem = w.mem ∧ w'.rd = w.rd ∧ w'.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
          by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.preservedV (WP.mono (WP.kept core (by rfl))
    fun w' ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩) (by lit_decide)

end VG.Proof.ChaCha20Poly1305.AArch64

end

end

/-! ### `ChaCha20Poly1305.AArch64.Short.Stash`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, 257 to 511 bytes: the state copied

`ShortRest.stash`: the ChaCha20 state at `ctx[0, 64)` copied to
`ctx[64, 128)` a word at a time, with its counter (word 12) set to 5.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.ShortRest

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.ShortRest
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_ldr32 wp_str32)
open VG.Spec.ChaCha20 (stateAt initState)

variable {e : Bool}

/-- The word `stashW k` stores: 5 for the counter, else the source's word. -/
abbrev stashVal (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k = 12 then 5 else m.readW (off c (4 * k)) 32

theorem five32 : ((((5 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 5 := rfl

/-- One word copied. -/
theorem stashW_ok {s₀ s : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (stashW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (64 + 4 * k)) (stashVal s.mem (cx s₀) k) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain o : InRegions s.wr (off (cx s₀) (64 + 4 * k)) 4 := by
    rw [hwr]; exact hp.in_ctx (by omega_using [hk])
  unfold stashW stashVal
  split
  · next h12 =>
    subst h12
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) (64 + 4 * 12)) (by decide) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
    · rw [g₂.mem, u₁.gpr, u₁.mem, five32]
    · rw [g₂.gpr, u₁.other r hr]
    · rw [g₂.rd, u₁.rd]
    · rw [g₂.wr, u₁.wr]
  · next h12 =>
    obtain i : InRegions (s.rd ++ s.wr) (off (cx s₀) (4 * k)) 4 := by
      rw [hrd, hwr]; exact hp.in_ctx' (by omega_using [hk])
    refine wp_ldr32 (a := off (cx s₀) (4 * k)) ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) (64 + 4 * k)) ⟨by omega_using [], by omega_using [hk]⟩
      (by rw [u₁.other _ (by decide), hx21]) (by rw [u₁.wr]; exact o) fun s₂ g₂ =>
        WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
    · rw [g₂.mem, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · rw [g₂.gpr, u₁.other r hr]
    · rw [g₂.rd, u₁.rd]
    · rw [g₂.wr, u₁.wr]

/-- The first `n` words of the copy. -/
def stashN (n : Nat) : List Instr := (List.range n).flatMap stashW

theorem stashN_succ (n : Nat) : stashN (n + 1) = stashN n ++ stashW n := by
  simp only [stashN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Words `j` and `k` of `ctx`, for `j ≠ k < 32`, do not overlap. -/
theorem word_sep (c : Addr) {j k : Nat} (hj : j < 32) (hk : k < 32) (h : j ≠ k) :
    Mem.Sep (off c (4 * j)) 4 (off c (4 * k)) 4 := Offset.sep c (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])

/-- After the first `n` words. -/
structure Copied (s₀ s : State) (n : Nat) (s' : State) : Prop where
  word : ∀ j < n, s'.mem.readW (off (cx s₀) (64 + 4 * j)) 32 = stashVal s.mem (cx s₀) j
  frame : Frame [sub s₀ 64 64] s.mem s'.mem
  gpr : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stashN_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 16, WP isa (.block (stashN n)) s (Copied s₀ s n)
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [stashN_succ]
    refine WP.block_append ((stashN_ok hp hx21 hrd hwr n (by omega_using [hn])).mono fun s₁ h₁ => ?_)
    refine (stashW_ok hp (k := n) (by omega_using [hn]) (by rw [h₁.gpr _ (by decide), hx21])
      (by rw [h₁.rd, hrd]) (by rw [h₁.wr, hwr])).mono fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    -- The source word `n` is outside the copy written so far.
    obtain src : stashVal s₁.mem (cx s₀) n = stashVal s.mem (cx s₀) n := by
      unfold stashVal
      split
      · rfl
      · refine h₁.frame.readW (r := sub s₀ (4 * n) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [])
    refine ⟨fun j hj => ?_, ?_, fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [rd₂, h₁.rd],
      by rw [wr₂, h₁.wr]⟩
    · rw [m₂, src]
      by_cases hjn : j = n
      · subst hjn; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
            rw [show off (cx s₀) (64 + 4 * j) = off (cx s₀) (4 * (16 + j)) by congr 1; omega_using [],
              show off (cx s₀) (64 + 4 * n) = off (cx s₀) (4 * (16 + n)) by congr 1; omega_using []]
            exact word_sep _ (by omega_using [hn, hj]) (by omega_using [hn]) (by omega_using [hjn])) (by decide)]
        exact h₁.word j (by omega_using [hj, hjn])
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ (by
        show (sub s₀ 64 64).Contains (off (cx s₀) (64 + 4 * n)) 4
        exact Offset.contains _ (e := 64) (k := 64) (by omega_using []) (by omega_using [hn]) (by omega_using []))

theorem stash_eq : stash = stashN 16 := rfl

/-- The state copied, with counter 5. -/
theorem stateAt_copy {s₀ s s' : State} (h : Copied s₀ s 16 s')
    (hst : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)) :
    stateAt s'.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
  apply Vector.ext
  intro j hj
  obtain w := h.word j hj
  simp only [stateAt, Vector.getElem_ofFn] at hst ⊢
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (64 + 4 * j) from off_off _ _ _, w]
  unfold stashVal
  obtain hs := congrArg (·[j]) hst
  simp only [Vector.getElem_ofFn, off_off, Nat.zero_add] at hs
  split
  · next h12 => subst h12; simp [Spec.ChaCha20.initState]
  · next h12 =>
    rw [hs]
    simp only [Spec.ChaCha20.initState, Vector.getElem_ofFn]
    split <;> simp_all

end VG.Proof.ChaCha20Poly1305.AArch64.ShortRest

end

end


/-!
# ChaCha20-Poly1305 on AArch64, 257 to 511 bytes: the parts

`ShortRest.first` XORs the first 256 bytes with the keystream of
`Short.prologue`, and `ShortRest.rest` the rest with the stream from the
state `stash` copied; together they encrypt the data from counter 1. After
the prologue, the code branches to `Short.lean`'s for up to 256 bytes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.ShortRest

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.ShortRest
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_mov wp_movz wp_subImm)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ks5 ks5_eq kp' xorKsAt_ok)
open VG.Spec.ChaCha20 (stateAt keystream serialize block initState)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data after the first 256 bytes. -/
abbrev restR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 256, L s₀ - 256⟩

theorem restR_sub {s₀ : State} (hL : 256 ≤ L s₀) : Region.Sub (restR s₀) (dR s₀) :=
  Offset.sub_base _ (by omega_using [hL])

/-- The output after its first 256 bytes, at `Q`. -/
abbrev restQ (s₀ : State) (Q : Addr) : Region := ⟨Q + BitVec.ofNat 64 256, L s₀ - 256⟩

theorem restQ_sub {s₀ : State} {Q : Addr} (hL : 256 ≤ L s₀) : Region.Sub (restQ s₀ Q) ⟨Q, L s₀⟩ :=
  Offset.sub_base _ (by omega_using [hL])

/-- The regions the stream writes, into the output at `Q`. -/
abbrev streamR (s₀ : State) (Q : Addr) : List Region := [sub s₀ 64 64, restQ s₀ Q, sub s₀ 128 320]

theorem streamR_work {s₀ : State} (hL : 256 ≤ L s₀) :
    ∀ r ∈ streamR s₀ (op e s₀), ∃ r' ∈ [workR s₀, oR e s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · exact ⟨oR e s₀, by simp, restQ_sub hL⟩
  · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩

/-- The stream's regions are apart from a part `[a, a + n)` of the context
that is apart from its own. -/
theorem streamR_ctx {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) (hL : 256 ≤ L s₀) {a n : Nat}
    (ha : a + n ≤ 1280) (h1 : a + n ≤ 64 ∨ 128 ≤ a) (h2 : a + n ≤ 128 ∨ 448 ≤ a) :
    ∀ r ∈ streamR s₀ Q, (sub s₀ a n).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega_using [h1]) ha (by lit_omega)
  · exact (hq.ctx.sub_left (sub_ctx s₀ ha)).sub_right (restQ_sub hL)
  · exact sub_disj s₀ (by omega_using [h2]) ha (by lit_omega)

theorem streamR_saved {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) :
    ∀ r ∈ streamR s₀ (op e s₀), (sub s₀ 576 56).Disjoint r :=
  streamR_ctx hp.o hL (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The state copied -/

theorem stash_ok {s₀ s : State} (hp : APre e s₀) (h : Inv e s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)) :
    WP isa (.block stash) s fun s' => Inv e s₀ s' ∧ Kept [sub s₀ 64 64] s s' ∧
      stateAt s'.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
  rw [stash_eq]
  refine WP.mono (WP.withSp (stashN_ok hp h.x21 h.rd h.wr 16 (Nat.le_refl _))) fun s' ⟨c, sp⟩ => ?_
  obtain k : Kept [sub s₀ 64 64] s s' :=
    ⟨fun r hr _ => c.gpr r (by rintro rfl; exact absurd hr (by decide)), sp, c.rd, c.wr, c.frame⟩
  refine ⟨h.step k (fun r hr => ?_) (fun r hr => ?_), k, stateAt_copy c hst⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The first 256 bytes -/

theorem first_ok {s₀ s : State} (hp : APre e s₀) (h : Inv e s₀ s) (hL : 256 ≤ L s₀) :
    WP isa (first (!e)) s fun s' => Inv e s₀ s' ∧ Kept [oR e s₀] s s' ∧
      (∀ i < 256, s'.mem (op e s₀ + BitVec.ofNat 64 i) =
        s.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ s.mem (kp' s₀ + BitVec.ofNat 64 i)) ∧
      Frame [⟨op e s₀, 256⟩] s.mem s'.mem := by
  unfold first
  obtain hstart : WP isa (.block [mov .x14 .x23, .movz .x .x23 256 0]) s fun s' =>
      s'.gpr .x14 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl,
        fun r h14 h23 => by rw [u₂.other r h23, u₁.other r h14], by rw [u₂.mem, u₁.mem],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  refine WP.seq ((WP.withSp hstart).mono fun s₁ h₁ => ?_)
  obtain ⟨⟨x14₁, x23₁, g₁, m₁, rd₁, wr₁⟩, sp₁⟩ := h₁
  refine WP.seq ((Short.xorKsDst_ok hp hp.o (!e) (o := 0) (n := 256) (by decide) (by omega_using [hL])
    (by rw [g₁ _ (by decide) (by decide), h.x21]) (by rw [g₁ _ (by decide) (by decide), h.x22, BitVec.add_zero])
    (cond_out s₀ (by rw [g₁ _ (by decide) (by decide), h.un .x28 (by decide)]) 0)
    x23₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])).mono fun s₂ ⟨k₂, x₂, f₂, g₂⟩ => ?_)
  obtain hlast : WP isa (.block [mov .x23 .x14]) s₂ fun s' => Upd s₂ s' .x23 (s₂.gpr .x14) :=
    wp_mov fun s' u => WP.block_nil u
  refine (WP.withSp hlast).mono fun s₃ ⟨u₃, sp₃⟩ => ?_
  obtain k : Kept [oR e s₀] s s₃ := by
    refine ⟨fun r hr h30 => ?_, by rw [sp₃, k₂.sp, sp₁], by rw [u₃.rd, k₂.rd, rd₁],
      by rw [u₃.wr, k₂.wr, wr₁], ?_⟩
    · by_cases h23 : r = .x23
      · subst h23
        rw [u₃.gpr, g₂ _ (by decide), x14₁]
      · have h14 : r ≠ .x14 := by rintro rfl; exact absurd hr (by decide)
        rw [u₃.other r h23, k₂.cs r hr h30, g₁ r h14 h23]
    · rw [u₃.mem, ← m₁]; exact k₂.frame
  refine ⟨h.step k (oR_inv hp).1 (oR_inv hp).2, k, fun i hi => ?_, ?_⟩
  · have := x₂ i hi
    rw [Nat.zero_add] at this
    rw [u₃.mem, this, m₁]
  · rw [u₃.mem, ← m₁]
    simpa only [BitVec.add_zero] using f₂

/-! ## The rest -/

theorem restArgs_ok {s₀ s : State} (h : Inv e s₀ s) (hL : 256 ≤ L s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x22 256, .subImm .x .x2 .x23 256,
      .addImm .x .x3 .x21 128]) s fun s' =>
      s'.gpr .x0 = off (cx s₀) 64 ∧ s'.gpr .x1 = dp s₀ + BitVec.ofNat 64 256 ∧
      s'.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256) ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      Kept [] s s' ∧ s'.mem = s.mem := by
  obtain core : WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x22 256, .subImm .x .x2 .x23 256,
      .addImm .x .x3 .x21 128]) s fun s₄ =>
      s₄.gpr .x0 = off (cx s₀) 64 ∧ s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 256 ∧
      s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256) ∧ s₄.gpr .x3 = off (cx s₀) 128 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₄.gpr r = s.gpr r) ∧ s₄.mem = s.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ =>
    wp_subImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x21],
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x22],
       by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.x23,
         VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hL],
       by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x21],
       fun r h0 h1 h2 h3 => by rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h0],
       by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
       by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine (WP.withSp core).mono fun s' ⟨⟨x0, x1, x2, x3, g, m, rd, wr⟩, sp'⟩ => ?_
  refine ⟨x0, x1, x2, x3, ⟨fun r hr _ => g r ?_ ?_ ?_ ?_, sp', rd, wr, by rw [m]; exact Frame.refl _ _⟩, m⟩ <;>
    rintro rfl <;> exact absurd hr (by decide)

theorem rest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s : State} (hp : APre e s₀) (h : Inv e s₀ s)
    (hL : 256 ≤ L s₀) (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀)) :
    WP isa (rest v.callee (!e)) s fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ Inv e s₀ s' ∧
      Kept (streamR s₀ (op e s₀)) s s' ∧
      Spec.ChaCha20.bytesAt s'.mem (op e s₀ + BitVec.ofNat 64 256) (L s₀ - 256) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256))
          (keystream (initState (K s₀) 5 (N s₀)) (L s₀ - 256)) := by
  unfold rest
  refine WP.seq (WP.mono (WP.preservedV (restArgs_ok h hL) (by lit_decide))
    fun s₁ ⟨⟨x0₁, x1₁, x2₁, x3₁, k₁, m₁⟩, v₁⟩ => ?_)
  refine xor_callOut v hp (by rw [k₁.rd, h.rd]) (by rw [k₁.wr, h.wr])
    (by rw [k₁.cs _ (by decide) (by decide), h.un .x28 (by decide)]) x0₁ x1₁ x2₁ x3₁ (by omega_using [hL])
    fun s₂ v₂ k₂ data₂ => ?_
  obtain k : Kept (streamR s₀ (op e s₀)) s s₂ := (k₁.sub fun r hr => absurd hr List.not_mem_nil).trans k₂
  refine ⟨fun r hr => (v₂ r hr).trans (v₁ r hr), h.step k (streamR_work hL) (streamR_saved hp hL), k, ?_⟩
  rw [data₂, m₁, hst]

/-! ## The data encrypted -/

/-- Byte `i` of the data is in its region. -/
theorem dR_byte {s₀ : State} (hp : APre e s₀) {i : Nat} (hi : i < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
  have := hp.wrap_d
  obtain h := Offset.contains (dp s₀) (d := i) (n := 1) (e := 0) (k := L s₀) (by omega_using []) (by omega_using [hi])
    (by simp only [L, dp] at this hi ⊢; omega_using [])
  simpa only [BitVec.add_zero] using h

/-- Byte `i < 256` of the output is outside what the stream writes. -/
theorem first_out {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) (hL : 256 ≤ L s₀) {i : Nat} (hi : i < 256) :
    ∀ r ∈ streamR s₀ Q, ¬ r.Contains (Q + BitVec.ofNat 64 i) 1 := by
  have wq := hq.wrap
  obtain hb : (⟨Q, L s₀⟩ : Region).Contains (Q + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hL, hi]) (by omega_using [hi])
  intro r hr hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hq.ctx.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))) _ hc hb
  · have hd := Offset.base_disjoint Q (e := 256) (n := L s₀ - 256) (k := 256) (Nat.le_refl _) (by omega_using [wq])
    obtain h1 := Offset.contains Q (d := i) (n := 1) (e := 0) (k := 256) (by omega_using []) (by omega_using [hi]) (by omega_using [])
    rw [BitVec.add_zero] at h1
    exact hd _ h1 hc
  · exact (hq.ctx.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) _ hc hb

/-- Byte `i ≥ 256` of the data is outside the output's first 256. -/
theorem rest_out {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) {i : Nat} (h₁ : 256 ≤ i) (h₂ : i < L s₀) :
    ∀ r ∈ [(⟨Q, 256⟩ : Region)], ¬ r.Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
  intro r hr hc
  simp only [List.mem_singleton] at hr; subst hr
  obtain hd := hq.sep (a := 0) (n := 256) (c := i) (m := 1) (by omega_using [h₁]) (by omega_using [h₂])
  rw [BitVec.add_zero] at hd
  exact hd _ hc (Region.contains_self _ _)

/-- The keystream from counter 5 continues the one from counter 1 after 256 bytes. -/
theorem ks_rest (key nonce : List Byte) {n i : Nat} (h₁ : 256 ≤ i) (h₂ : i < n) :
    (keystream (initState key 5 nonce) (n - 256)).getD (i - 256) 0 =
      (keystream (initState key 1 nonce) n).getD i 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega_using [h₁, h₂]), VG.Proof.ChaCha20.keystream_getD _ h₂,
    VG.Proof.ChaCha20Poly1305.ctr_initState, VG.Proof.ChaCha20Poly1305.ctr_initState,
    show (i - 256) % 64 = i % 64 by omega_using [h₁]]
  congr 4
  rw [show i / 64 = (i - 256) / 64 + 4 by omega_using [h₁], BitVec.ofNat_add]
  bv_omega

/-- `ChaCha20.xor_getD`, from the source at `p` to the destination at `q`. -/
theorem xor_getD2 {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : Spec.ChaCha20.bytesAt m' q n = List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m p n) ks) {j : Nat}
    (hj : j < n) : m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) ^^^ ks.getD j 0 := by
  have := congrArg (·.getD j 0) h
  rw [VG.Proof.ChaCha20.bytesAt_getD _ _ hj] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem
    (by rw [VG.Proof.ChaCha20.length_bytesAt]; exact hj), List.getElem?_eq_getElem (by rw [hks]; exact hj)]
  simp only [Option.getD_some]
  rw [VG.Proof.ChaCha20.getElem_eq_getD' _ (by rw [VG.Proof.ChaCha20.length_bytesAt]; exact hj),
    VG.Proof.ChaCha20.bytesAt_getD _ _ hj,
    VG.Proof.ChaCha20.getElem_eq_getD' _ (show j < ks.length by omega_using [hks, hj])]

theorem ct_rest {s₀ : State} {Q : Addr} (hq : DstR s₀ Q) (hL : 256 ≤ L s₀) {m₃ m₄ m₅ : Mem}
    (hD : bytesAt m₃ (dp s₀) (L s₀) = D s₀)
    (hk : ∀ i < 256, m₃ (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i))
    (hx : ∀ i < 256, m₄ (Q + BitVec.ofNat 64 i) =
      m₃ (dp s₀ + BitVec.ofNat 64 i) ^^^ m₃ (kp' s₀ + BitVec.ofNat 64 i))
    (hf₄ : Frame [⟨Q, 256⟩] m₃ m₄)
    (hr : Spec.ChaCha20.bytesAt m₅ (Q + BitVec.ofNat 64 256) (L s₀ - 256) =
      List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m₄ (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256))
        (keystream (initState (K s₀) 5 (N s₀)) (L s₀ - 256)))
    (hf₅ : Frame (streamR s₀ Q) m₄ m₅) :
    bytesAt m₅ Q (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  obtain hDl : (D s₀).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  obtain hDi : ∀ i < L s₀, (D s₀).getD i 0 = m₃ (dp s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [← hD]; exact VG.Proof.ChaCha20.bytesAt_getD _ _ hi
  rw [encrypt_eq]
  apply List.ext_getElem
  · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
  · intro i h₁ h₂
    obtain hiL : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
    obtain e1 : (bytesAt m₅ Q (L s₀))[i] = m₅ (Q + BitVec.ofNat 64 i) := by simp [bytesAt]
    obtain e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = m₃ (dp s₀ + BitVec.ofNat 64 i) := fun h => by
      rw [← List.getElem_of_eq hD (by rw [VG.Proof.Poly1305.length_bytesAt]; exact hiL)]
      simp [bytesAt]
    obtain e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length).length,
        (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length)[i] =
          (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
      rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, hDl]
    rw [List.getElem_zipWith, e1, e2, e3]
    by_cases hi : i < 256
    · rw [hf₅ _ (first_out hq hL hi), hx i hi, hk i hi, ks5_eq s₀ (n := L s₀) hiL]
    · have hi' : 256 ≤ i := by omega_using [hi]
      obtain x := xor_getD2 (VG.Proof.ChaCha20.length_keystream _ _) hr (j := i - 256)
        (by omega_using [hiL, hi])
      obtain sh : ∀ X : Addr, X + BitVec.ofNat 64 256 + BitVec.ofNat 64 (i - 256) = X + BitVec.ofNat 64 i :=
        fun X => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hi']
      rw [sh, sh] at x
      rw [x, hf₄ _ (rest_out hq hi' hiL), ks_rest _ _ hi' hiL]

/-! ## `seal` and `open` up to the tag -/

/-- After the prologue. -/
theorem sealAfter_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s₁ : State} (hp : APre true s₀)
    (hL₁ : 256 ≤ L s₀) (h₁ : Short.PostP true s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa (ShortRest.sealAfter v.callee) s₁ (MainS s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold ShortRest.sealAfter
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  obtain D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  obtain K₂ : ∀ i < 256, s₂.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [Short.ks_frame k₂.frame (by rdisj_all) hi]
    exact Short.ks_post h₁.ks hi
  refine WP.seq (WP.mono (WP.preservedV (first_ok hp i₂ hL₁) (by lit_decide))
    fun s₃ ⟨⟨i₃, k₃, x₃, f₃⟩, v₃⟩ => ?_)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), st₂]
  refine WP.seq (WP.mono (rest_ok v hp i₃ hL₁ st₃) fun s₄ ⟨v₄, i₄, k₄, r₄⟩ => ?_)
  obtain ct₄ := ct_rest hp.o hL₁ D₂ K₂ x₃ f₃ r₄ k₄.frame
  rw [op_true] at ct₄
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₄.x21
    i₄.rd i₄.wr i₄.x24 (by rw [i₄.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₅ ⟨⟨k₅, r₅⟩, v₅⟩ => ?_)
  obtain i₅ := mac_inv i₄ k₅
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₅) (by lit_decide)) fun s₆ ⟨⟨i₆, k₆, len₆⟩, v₆⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₆.x21
    i₆.rd i₆.wr i₆.x22 (by rw [i₆.x23]; exact hL s₀)) (by lit_decide))
    fun s₇ ⟨⟨k₇, r₇⟩, v₇⟩ => ?_)
  obtain i₇ := mac_inv i₆ k₇
  refine WP.mono (WP.preservedV (absorbLengths_ok hp i₇) (by lit_decide)) fun s₈ ⟨⟨i₈, k₈, r₈⟩, v₈⟩ => ?_
  obtain hd4 := streamR_ctx hp.o hL₁ (a := 448) (n := 128) (by lit_omega) (by lit_omega) (by lit_omega)
  obtain R₄ : Repr s₄.mem (off (cx s₀) 448) (otk s₀) [] :=
    Repr.frame k₄.frame hd4 (Repr.frame k₃.frame (by rdisj_all) (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
  obtain A₄ : bytesAt s₄.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₄.frame (fun r hr => ?_) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame k₃.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame k₂.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt), hA]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm.sub_right (sub_ctx s₀ (by lit_omega))
    · exact hp.a_d.sub_right (restQ_sub hL₁)
    · exact hp.c_a.symm.sub_right (sub_ctx s₀ (by lit_omega))
  obtain ct₆ : bytesAt s₆.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [bytesAt_frame k₆.frame (by rdisj_all) hL', bytesAt_frame k₅.frame (by rdisj_all) hL', ct₄]
  obtain L₇ : bytesAt s₇.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₇.frame (by rdisj_all) (by lit_omega), len₆]
  obtain R₈ := r₈ _ _ (r₇ _ _ (Repr.frame k₆.frame (by rdisj_all) (r₅ _ _ R₄)))
  rw [L₇, ct₆, A₄] at R₈
  refine ⟨i₈.inv0, fun r hr => (v₈ r hr).trans ((v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans
      ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · refine (congrArg (Repr s₈.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₈
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₈.frame (by rdisj_all) hL', bytesAt_frame k₇.frame (by rdisj_all) hL', ct₆]

/-- After the prologue. -/
theorem openAfter_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s₁ : State} (hp : APre false s₀)
    (hL₁ : 256 ≤ L s₀) (h₁ : Short.PostP false s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa (ShortRest.openAfter v.callee) s₁ (MainO s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold ShortRest.openAfter
  refine WP.seq (WP.mono (WP.preservedV (stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  obtain A₂ : bytesAt s₂.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)]
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₂.x21
    i₂.rd i₂.wr i₂.x24 (by rw [i₂.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₃ ⟨⟨k₃, r₃⟩, v₃⟩ => ?_)
  obtain i₃ := mac_inv i₂ k₃
  obtain D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₃.x21
    i₃.rd i₃.wr i₃.x22 (by rw [i₃.x23]; exact hL s₀)) (by lit_decide))
    fun s₄ ⟨⟨k₄, r₄⟩, v₄⟩ => ?_)
  obtain i₄ := mac_inv i₃ k₄
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₄) (by lit_decide)) fun s₅ ⟨⟨i₅, k₅, len₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok hp i₅) (by lit_decide)) fun s₆ ⟨⟨i₆, k₆, r₆⟩, v₆⟩ => ?_)
  obtain D₆ : bytesAt s₆.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₆.frame (by rdisj_all) hL', bytesAt_frame k₅.frame (by rdisj_all) hL',
      bytesAt_frame k₄.frame (by rdisj_all) hL', D₃]
  obtain K₆ : ∀ i < 256, s₆.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [Short.ks_frame k₆.frame (by rdisj_all) hi, Short.ks_frame k₅.frame (by rdisj_all) hi,
      Short.ks_frame k₄.frame (by rdisj_all) hi, Short.ks_frame k₃.frame (by rdisj_all) hi,
      Short.ks_frame k₂.frame (by rdisj_all) hi]
    exact Short.ks_post h₁.ks hi
  obtain st₆ : stateAt s₆.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₆.frame (by rdisj_all), stateAt_frame k₅.frame (by rdisj_all),
      stateAt_frame k₄.frame (by rdisj_all), stateAt_frame k₃.frame (by rdisj_all), st₂]
  refine WP.seq (WP.mono (WP.preservedV (first_ok hp i₆ hL₁) (by lit_decide))
    fun s₇ ⟨⟨i₇, k₇, x₇, f₇⟩, v₇⟩ => ?_)
  obtain st₇ : stateAt s₇.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₇.frame (by rdisj_all), st₆]
  refine WP.seq (WP.mono (rest_ok v hp i₇ hL₁ st₇) fun s₈ ⟨v₈, i₈, k₈, r₈⟩ => ?_)
  obtain pt₈ := ct_rest hp.o hL₁ D₆ K₆ x₇ f₇ r₈ k₈.frame
  refine WP.mono (WP.preservedV (finalizeTo_ok hp i₈ (out := 48) (by omega_using [])) (by lit_decide))
    fun s₉ ⟨⟨k₉, tag₉⟩, v₉⟩ => ?_
  obtain hd8 := streamR_ctx hp.o hL₁ (a := 448) (n := 128) (by lit_omega) (by lit_omega) (by lit_omega)
  obtain R₂ : Repr s₂.mem (off (cx s₀) 448) (otk s₀) [] := Repr.frame k₂.frame (by rdisj_all) h₁.poly
  obtain R₄ := r₄ _ _ (r₃ _ _ R₂)
  obtain T₉ := tag₉ _ _ (Repr.frame k₈.frame hd8 (Repr.frame k₇.frame (by rdisj_all)
    (r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄))))
  rw [len₅, D₃, A₂] at T₉
  refine ⟨i₈.inv0.step k₉ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₉ r hr).trans ((v₈ r hr).trans
      ((v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans
        ((v₂ r hr).trans (v₁ r hr)))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₉]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₉.frame (by rdisj_all) hL', pt₈]

/-! ## The branch on the length, after the prologue -/

/-- `s₁` but for `x9` and `x10` is still after the prologue. -/
theorem postP_agree {s₀ s₁ s₂ : State} (h : Short.Agree s₁ s₂) (hp : Short.PostP e s₀ s₁) :
    Short.PostP e s₀ s₂ := by
  obtain ⟨⟨x21, x22, x23, x24, x25, un, sp, rd, wr, sv, fr⟩, fine, poly, ks, st0⟩ := hp
  obtain hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x10 := by decide
  refine ⟨⟨by rw [h.gpr _ (by decide) (by decide), x21], by rw [h.gpr _ (by decide) (by decide), x22],
    by rw [h.gpr _ (by decide) (by decide), x23], by rw [h.gpr _ (by decide) (by decide), x24],
    by rw [h.gpr _ (by decide) (by decide), x25],
    fun r hr => by rw [h.gpr r (hu r hr).1 (hu r hr).2, un r hr], by rw [h.sp, sp], by rw [h.rd, rd],
    by rw [h.wr, wr], by rw [h.mem]; exact sv, by rw [h.mem]; exact fr⟩,
    by rw [h.mem]; exact fine, by rw [h.mem]; exact poly, by rw [h.mem]; exact ks, by rw [h.mem]; exact st0⟩

/-- The value `split` leaves in `x9`. -/
abbrev splitVal (x : BitVec 64) : BitVec 64 := (x - BitVec.ofNat 64 1) >>> 8

/-- `x9`, zero iff `1 ≤ len ≤ 256`. -/
theorem split_ok (s₀ : State) :
    WP isa (.block split) s₀ fun s₁ => Short.Agree s₀ s₁ ∧ s₁.gpr .x9 = splitVal (s₀.gpr .x23) := by
  obtain h : WP isa (.block split) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = splitVal (s₀.gpr .x23) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr :=
    wp_subImm (by decide) fun s₁ u₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil
      ⟨fun r h9 _ => by rw [u₂.other r h9, u₁.other r h9],
        by rw [u₂.gpr, u₁.gpr],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.withSp h) (by lit_decide))
    fun s₁ ⟨⟨⟨g, x9, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9⟩

theorem splitVal_eq {L : Nat} (h : L < 2 ^ 64) :
    (splitVal (BitVec.ofNat 64 L) == 0) = decide (1 ≤ L ∧ L ≤ 256) := by
  obtain hz : ∀ x : BitVec 64, (x == 0) = decide (x.toNat = 0) := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    · have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr hx]
      simp [this]
  rw [hz]
  congr 1
  apply propext
  simp only [splitVal, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega_using [h]

/-- The branch: to `Short.lean`'s code iff `1 ≤ len ≤ 256`. -/
theorem split_eval {s₀ s₁ s₂ : State} (h₁ : Short.PostP e s₀ s₁) (h : s₂.gpr .x9 = splitVal (s₁.gpr .x23)) :
    isa.eval (.zero .x .x9) s₂ = some (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) := by
  obtain e : isa.eval (.zero .x .x9) s₂ = some (s₂.gpr .x9 == 0) :=
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₂ .x9
  rw [e, h, h₁.inv.x23, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, splitVal_eq (s₀.gpr .x5).isLt]

/-! ## `seal` and `open` up to the tag, for `lo ≤ len ≤ 511` -/

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 1 ≤ L s₀) : WP isa (ShortRest.sealMain v.callee) s₀ (MainS s₀) := by
  unfold ShortRest.sealMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (split_ok s₁) fun s₂ ⟨ag, x9⟩ => ?_)
  obtain h₂ := postP_agree ag h₁
  obtain v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 :=
    fun r hr => (ag.v r hr).trans (v₁ r hr)
  refine WP.ite (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) (split_eval h₁ x9) (fun h => ?_) (fun h => ?_)
  · exact Short.sealAfter_ok hp (of_decide_eq_true h).2 h₂ v₂
  · exact sealAfter_ok v hp (by have := of_decide_eq_false h; omega_using [hlo, this]) h₂ v₂

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 1 ≤ L s₀) : WP isa (ShortRest.openMain v.callee) s₀ (MainO s₀) := by
  unfold ShortRest.openMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (split_ok s₁) fun s₂ ⟨ag, x9⟩ => ?_)
  obtain h₂ := postP_agree ag h₁
  obtain v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 :=
    fun r hr => (ag.v r hr).trans (v₁ r hr)
  refine WP.ite (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) (split_eval h₁ x9) (fun h => ?_) (fun h => ?_)
  · exact Short.openAfter_ok hp (of_decide_eq_true h).2 h₂ v₂
  · exact openAfter_ok v hp (by have := of_decide_eq_false h; omega_using [hlo, this]) h₂ v₂

end VG.Proof.ChaCha20Poly1305.AArch64.ShortRest
