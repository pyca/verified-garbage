module

public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Hash
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-! ### `Ed448.RISCV64.Whole.Prune`, which the modules that import this one used -/

section

/-!
# Ed448's whole functions on RISCV64: pruning in place

`prune f o` clears bits 0–1 of the byte at `o(f)`, sets bit 7 of the byte
55 after it and clears the byte 56 after it (`prune_ok`); the 57 bytes then
decode to `Spec.Ed448.prune` of the hash they start (`pruned_value`, as on
ARMv7, `Proof/Ed448/Arm/PublicKey/Base.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Proof.Sha3 (writeW8_apply)

/-! ## The bytes -/

theorem off_ne (q : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) (h : d ≠ e) :
    q + BitVec.ofNat 64 d ≠ q + BitVec.ofNat 64 e := by
  intro x
  have := congrArg (fun a => (a - q).toNat) x
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
  exact h this

theorem bytesAt_split (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = m q :: (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 ++
      [m (q + BitVec.ofNat 64 55), m (q + BitVec.ofNat 64 56)]) := by
  have b1 : Spec.X25519.bytesAt m q 1 = [m q] := by
    simp [Spec.X25519.bytesAt]
  have b2 : ∀ p : Addr, Spec.X25519.bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := fun p => by
    simp [Spec.X25519.bytesAt, List.range_succ]
  rw [Proof.Ed448.bytesAt_eq, show 57 = 1 + (54 + 2) from rfl, VG.Proof.X25519.bytesAt_add,
    VG.Proof.X25519.bytesAt_add, b1, b2, Offset.add_add, Offset.add_add]
  rfl

theorem decodeLE_split (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) = (m q).toNat + 256 *
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) + 2 ^ 432 *
        ((m (q + BitVec.ofNat 64 55)).toNat + 256 * (m (q + BitVec.ofNat 64 56)).toNat)) := by
  rw [bytesAt_split, Spec.Ed448.decodeLE, Proof.Ed448.decodeLE_append]
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  rw [hl, show (256 : Nat) ^ 54 = 2 ^ 432 by decide +kernel]
  simp only [Spec.Ed448.decodeLE, Nat.mul_zero, Nat.add_zero]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, show 114 = 57 + 57 from rfl, VG.Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]

/-- The pruned bytes. -/
abbrev pruned (m : Mem) (q : Addr) : Mem :=
  ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
    (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
      (q + BitVec.ofNat 64 56) (0 : BitVec 8)

theorem pruned_value (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (pruned m q) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h => off_ne q (by omega_using [hi]) (by omega_using [hj]) h
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    ne j 0 h2 (by decide) (by omega_using [h1]) (e.trans z.symm)
  generalize hm' : pruned m q = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', pruned, Offset.add_add, writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega_using [hi]) (by omega_using []) (by omega_using [hi])),
      writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega_using [hi]) (by omega_using []) (by omega_using [hi])), writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega_using []) (by omega_using [hi]))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', pruned, writeW8_apply, ite_eq_right (ne0 56 (by omega_using []) (by omega_using [])).symm,
      writeW8_apply, ite_eq_right (ne0 55 (by omega_using []) (by omega_using [])).symm,
      writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', pruned, writeW8_apply, ite_eq_right (ne 55 56 (by omega_using []) (by omega_using []) (by omega_using [])),
      writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', pruned, writeW8_apply, ite_eq_left rfl]; rfl
  rw [decodeLE_split, decodeLE_split, mid, e0, e55, e56]
  have h0 := (m q).isLt
  have h55 := (m (q + BitVec.ofNat 64 55)).isLt
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  have hM' := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54)
  rw [hl] at hM'
  have hM : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) < 2 ^ 432 :=
    Nat.lt_of_lt_of_le hM' (Nat.le_of_eq (by decide +kernel))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h0),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) h55 (by decide))]
  exact (Proof.Ed448.prune_bytes (b56 := (m (q + BitVec.ofNat 64 56)).toNat) h0 hM h55).symm

/-- The pruned hash is `Spec.Ed448.prune` of the hash. -/
theorem pruned_prune (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (pruned m q) q 57) = Spec.Ed448.prune (Spec.Ed448.bytesAt m q 114) := by
  rw [pruned_value, Spec.Ed448.prune, bytesAt_take57]

/-- Pruning writes only the 57 bytes. -/
theorem pruned_frame (m : Mem) (q : Addr) : Frame [⟨q, 57⟩] m (pruned m q) := by
  have h : ∀ j, j < 57 → (⟨q, 57⟩ : Region).Contains (q + BitVec.ofNat 64 j) (8 / 8) := fun j hj =>
    Offset.contains_base q (by omega_using [hj]) (by omega_using [hj])
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ (h 55 (by decide))).writeW
    List.mem_cons_self _ (h 56 (by decide))
  have := h 0 (by decide)
  rwa [BitVec.add_zero] at this

/-! ## The instructions -/

theorem wp_ori {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n ||| BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .or d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem and_fc : ∀ b : Byte,
    ((BitVec.ofNat 64 b.toNat >>> 2) <<< 2).setWidth 8 = BitVec.ofNat 8 (b.toNat &&& 252) := by
  decide

theorem or_80 : ∀ b : Byte,
    (BitVec.ofNat 64 b.toNat ||| BitVec.ofInt 64 0x80).setWidth 8 = BitVec.ofNat 8 (b.toNat ||| 128) := by
  decide

/-- `prune f o`, at `q = o(f)`: the bytes pruned, only `a5` written. -/
theorem prune_ok {s : State} {f : Reg} {o : Nat} {q : Addr} (hf8 : f ≠ .a5) (ho : o + 56 < 2048)
    (hq : s.gpr f + BitVec.ofNat 64 o = q) (hw : ∀ j < 57, InRegions s.wr (q + BitVec.ofNat 64 j) 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = pruned s.mem q → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      (∀ r, r ≠ .a5 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (prune f o ++ is)) s Q := by
  have hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1 := fun j hj => by
    obtain ⟨R, hR, hc⟩ := hw j hj
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have ea : ∀ j < 57, s.gpr f + BitVec.ofNat 64 (o + j) = q + BitVec.ofNat 64 j := fun j hj => by
    rw [← hq, Offset.add_add]
  have e0 : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne55 : q + BitVec.ofNat 64 55 ≠ q := fun e => off_ne q (d := 55) (e := 0) (by decide) (by decide) (by decide)
    (e.trans e0.symm)
  unfold prune
  simp only [List.cons_append, List.nil_append]
  refine wp_lbz (a := q) (by omega_using [ho]) hq (by rw [← e0]; exact hr 0 (by decide))
    fun s1 v1 => ?_
  refine wp_srl (by decide) fun s2 v2 => wp_sll (by decide) fun s3 v3 => ?_
  refine wp_sb (a := q) (by omega_using [ho])
    (by rw [v3.other _ hf8, v2.other _ hf8, v1.other _ hf8]; exact hq)
    (by rw [v3.wr, v2.wr, v1.wr, ← e0]; exact hw 0 (by decide)) fun s4 v4 => ?_
  have g4 : s4.gpr f = s.gpr f := by
    rw [v4.gpr, v3.other _ hf8, v2.other _ hf8, v1.other _ hf8]
  refine wp_lbz (a := q + BitVec.ofNat 64 55) (by omega_using [ho]) (by rw [g4]; exact ea 55 (by decide))
    (by rw [v4.rd, v4.wr, v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr 55 (by decide)) fun s5 v5 => ?_
  refine wp_ori (by decide) fun s6 v6 => ?_
  refine wp_sb (a := q + BitVec.ofNat 64 55) (by omega_using [ho])
    (by rw [v6.other _ hf8, v5.other _ hf8, g4]; exact ea 55 (by decide))
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 55 (by decide)) fun s7 v7 => ?_
  refine wp_li (by decide) fun s8 v8 => ?_
  refine wp_sb (a := q + BitVec.ofNat 64 56) (by omega_using [ho])
    (by rw [v8.other _ hf8, v7.gpr, v6.other _ hf8, v5.other _ hf8, g4]; exact ea 56 (by decide))
    (by rw [v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 56 (by decide)) fun t vt => ?_
  refine k t ?_ ?_ ?_ ?_ fun r hr => ?_
  · have r3 : s3.gpr .a5 = ((BitVec.ofNat 64 (s.mem q).toNat) >>> 2) <<< 2 := by
      rw [v3.gpr, v2.gpr, v1.gpr]
    have m4 : s4.mem = s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252)) := by
      rw [v4.mem, v3.mem, v2.mem, v1.mem, r3, and_fc]
    have r6 : s6.gpr .a5 = BitVec.ofNat 64 (s.mem (q + BitVec.ofNat 64 55)).toNat ||| BitVec.ofInt 64 0x80 := by
      rw [v6.gpr, v5.gpr, m4, writeW8_apply, ite_eq_right ne55]
    have m7 : s7.mem = (s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252))).writeW (q + BitVec.ofNat 64 55)
        (BitVec.ofNat 8 ((s.mem (q + BitVec.ofNat 64 55)).toNat ||| 128)) := by
      rw [v7.mem, v6.mem, v5.mem, m4, r6, or_80]
    rw [vt.mem, v8.mem, m7, v8.gpr]
    rfl
  · rw [vt.sp, v8.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]
  · rw [vt.rd, v8.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd]
  · rw [vt.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]
  · rw [vt.gpr, v8.other r hr, v7.gpr, v6.other r hr, v5.other r hr, v4.gpr, v3.other r hr, v2.other r hr,
      v1.other r hr]

end VG.Proof.Ed448.RISCV64.Whole

end

end

/-!
# Ed448's whole functions on RISC-V: the setup

As on PPC64LE (`Proof/Ed448/PPC64LE/Whole/Common.lean`), with Ed25519's
invariant on this target (`Proof/Ed25519/RISCV64/Whole/Frame.lean`): the
registers `rs` and `ra` saved at `o(F)`, then the arguments moved into `rs`
(`setup_ok`, by `movs_ok`); a hash, or any step that keeps the callee-saved
registers and writes within the body's regions, apart from the slots, keeps
`Inv` (`Inv.kept`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea save_ok)

/-- `mov`s from registers that none of them writes, to distinct registers. -/
theorem movs_ok : ∀ (ms : List (Reg × Reg)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ ms, p.2 ∉ ms.map Prod.fst) → (ms.map Prod.fst).Nodup →
    (∀ u, u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      (∀ p ∈ ms, u.gpr p.1 = s.gpr p.2) → (∀ r, r ∉ ms.map Prod.fst → u.gpr r = s.gpr r) →
      WP isa (.block rest) u Q) →
    WP isa (.block (ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  intro ms
  induction ms with
  | nil => exact fun _ _ k => k _ rfl rfl rfl rfl (fun _ h => absurd h List.not_mem_nil) fun _ _ => rfl
  | cons p ms ih =>
    intro s rest Q hs hn k
    obtain ⟨d, n⟩ := p
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons, List.cons_append]
    refine wp_mv fun u hu => ih (fun q hq => fun h => hs q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ h))
      hn'.2 fun u' m' rd' wr' sp' hm ho => k u' (m'.trans hu.mem) (rd'.trans hu.rd) (wr'.trans hu.wr)
        (sp'.trans hu.sp) (fun q hq => ?_) fun r hr => ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hn'.1, hu.gpr]
      · have hq2 : q.2 ≠ d := fun e => hs q (List.mem_cons_of_mem _ hq) (e ▸ List.mem_cons_self)
        rw [hm q hq, hu.other _ hq2]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hu.other r hr.1]

/-- The saves at `o(F)` (`F`, a multiple of 8, in `f`), then the moves `ms` into the registers `rs`,
which hold `v`: the invariant holds after them. -/
theorem setup_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {ms : List (Reg × Reg)} {v : Reg → BitVec 64}
    {W : List Region} {rest : List Instr} {Q : State → Prop} (hal : (s.gpr f).toNat % 8 = 0)
    (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (hW : ∃ R ∈ W, Region.Sub (slotArea (s.gpr f) o rs) R) (hms : ms.map Prod.fst = rs)
    (hsrc : ∀ p ∈ ms, p.2 ∉ rs) (hnd : rs.Nodup) (hv : ∀ p ∈ ms, v p.1 = s.gpr p.2)
    (k : ∀ u, Inv s (s.gpr f) o rs v W u → (∀ r, r ∉ rs → u.gpr r = s.gpr r) → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine save_ok hal hfits hlo hin fun u hu hsv hfr => ?_
  refine movs_ok ms (fun p hp => hms ▸ hsrc p hp) (hms ▸ hnd)
    fun u' m' rd' wr' sp' hm ho => k u' ⟨rd'.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, fun r hr => ?_,
      fun r hr hn => ?_, m' ▸ hsv, m' ▸ hfr.sub fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hW⟩ fun r hn => ?_
  · rw [← hms] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [hm p hp, hv p hp, hu.gpr _ (by simp)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simp)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simp)]

/-- A step that keeps the callee-saved registers, writing within `W` and apart from the slots. -/
theorem Inv.kept {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hk : Kept Wc t t')
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' :=
  h.step hrs hk.rd hk.wr hk.sp hk.cs hk.frame hsub hd

end VG.Proof.Ed448.RISCV64.Whole
