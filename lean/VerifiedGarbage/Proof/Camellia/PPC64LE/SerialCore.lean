module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.SerialSbox
public import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorBytes
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.CtrCipher
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModeCore
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Camellia.Words

/-!
# The single-block Camellia core on PPC64LE

* `stage1_run`, `stage2_run`, `sLayer_run`: the S-boxes of the round's
  bytes (`Serial.sLayer`) are `substituted`, by `sbox1_affine` …
  `sbox4_affine`.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Serial

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.PPC64LE.Bytes
open VG.Impl.Camellia.PPC64LE.Serial
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Camellia.Serial (byte packed substituted substitutedByte linearWord)

/-! ## The constants -/

/-- What the core keeps in registers: the tables in `treg 0 … 12` and the
mask in `r12`. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 13, TabOk (s.vpr (treg k)) (tables.getD k m0f)
  mask : s.gpr .r12 = 0x0f0f0f0f0f0f0f0f

/-- The temporaries, which are not tables. -/
def temps : List VReg := [.v0, .v1, .v2, .v3]

theorem treg_temps : ∀ k < 13, treg k ∉ temps := by decide

theorem Consts.of_eq {s t : State} (h : Consts s) (hv : ∀ v, v ∉ temps → t.vpr v = s.vpr v)
    (hg : t.gpr .r12 = s.gpr .r12) : Consts t :=
  ⟨fun k hk => by rw [hv _ (treg_temps k hk)]; exact h.tab k hk, by rw [hg]; exact h.mask⟩

/-! ## Bytes -/

theorem gbyte_m0f {k : Nat} (hk : k < 8) : gbyte 0x0f0f0f0f0f0f0f0f k = 0x0f := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem gbyte_lsr4 (x : BitVec 64) {k : Nat} (hk : k < 8) :
    gbyte ((x >>> 4) &&& 0x0f0f0f0f0f0f0f0f) k = gbyte x k >>> 4 := by
  rw [gbyte_and, gbyte_m0f hk]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | (simp; done) | (simp; congr 1; omega_using [])

/-- A lookup by `vperm` in one of two tables, the choice in bit 4 of the
index (`sel`, `0` or `0x10`), its low bits a nibble. -/
theorem lookup_sel {T U c : BitVec 128} {t u : Vector Byte 16} (hT : TabOk T t) (hU : TabOk U u)
    {i : Nat} (hi : i < 16) {y sel : Byte} (hy : y.toNat < 16) (hc : vbyte c i = y ||| sel)
    (hs : sel = 0 ∨ sel = 0x10) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte U (j - 16)) i =
      if sel = 0x10 then u.getD y.toNat 0 else t.getD y.toNat 0 := by
  rcases hs with rfl | rfl
  · have e : (vbyte c i).toNat = y.toNat := by rw [hc]; simp
    rw [vperm_byte2 hT hU hi (by omega_using [hy, e]), e]; simp [hy]
  · have e : (vbyte c i).toNat = y.toNat + 16 := by rw [hc, toNat_or_16 hy]
    rw [vperm_byte2 hT hU hi (by omega_using [hy, e]), e]
    simp only [show ¬(y.toNat + 16 < 16) by omega_using [], ite_false, Nat.add_sub_cancel, ite_true]

/-- A lookup by `vperm` in one table, of a nibble. -/
theorem lookup_one {T c : BitVec 128} {t : Vector Byte 16} (hT : TabOk T t) {i : Nat} (hi : i < 16) {y : Byte}
    (hy : y.toNat < 16) (hc : vbyte c i = y) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte T (j - 16)) i = t.getD y.toNat 0 := by
  rw [vperm_byte2 hT hT hi (by rw [hc]; omega_using [hy]), hc]; simp [hy]

/-- The input map of byte `k` (from the least significant): `A_in ∘ rotl 1`
for `SBOX4`'s bytes. -/
def inMap (k : Nat) (b : Byte) : Byte := if k = 1 ∨ k = 4 then aff in4Lo in4Hi b else aff inLo inHi b

/-- The output map of byte `k`: `rotl 7 ∘ A_out` for `SBOX3`'s bytes,
`rotl 1 ∘ A_out` for `SBOX2`'s. -/
def outMap (k : Nat) (b : Byte) : Byte :=
  if k = 2 ∨ k = 5 then aff out3Lo out3Hi b else if k = 3 ∨ k = 6 then aff out2Lo out2Hi b else aff outLo outHi b

theorem selIn_eq {k : Nat} (hk : k < 8) : selIn.getD (7 - k) 0 = if k = 1 ∨ k = 4 then 0x10 else 0 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem selOut_eq {k : Nat} (hk : k < 8) : selOut.getD (7 - k) 0 = if k = 3 ∨ k = 6 then 0x10 else 0 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem mask36_eq {k : Nat} (hk : k < 8) : mask36.getD (7 - k) 0 = if k = 2 ∨ k = 5 then 0xff else 0 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem sel_cases (p : Prop) [Decidable p] : ((if p then 0x10 else 0 : Byte) = 0 ∨ (if p then 0x10 else 0 : Byte) = 0x10) := by
  by_cases h : p <;> simp [h]

theorem sel_iff (p : Prop) [Decidable p] : ((if p then 0x10 else 0 : Byte) = 0x10) ↔ p := by
  by_cases h : p <;> simp [h]

/-! ## The S-boxes -/

theorem exec_and {s : State} {d n m : Reg} :
    exec (.logic .and d n m) s = some (s.write d (s.gpr n &&& s.gpr m)) := rfl

/-- The tables, by register. -/
theorem Consts.t {s : State} (h : Consts s) :
    TabOk (s.vpr .v8) inLo ∧ TabOk (s.vpr .v9) in4Lo ∧ TabOk (s.vpr .v10) inHi ∧ TabOk (s.vpr .v11) in4Hi ∧
    TabOk (s.vpr .v12) outLo ∧ TabOk (s.vpr .v13) out2Lo ∧ TabOk (s.vpr .v14) outHi ∧
    TabOk (s.vpr .v15) out2Hi ∧ TabOk (s.vpr .v16) out3Lo ∧ TabOk (s.vpr .v17) out3Hi ∧
    TabOk (s.vpr .v18) selIn ∧ TabOk (s.vpr .v19) selOut ∧ TabOk (s.vpr .v7) mask36 :=
  ⟨h.tab 0 (by decide), h.tab 1 (by decide), h.tab 2 (by decide), h.tab 3 (by decide), h.tab 4 (by decide),
    h.tab 5 (by decide), h.tab 6 (by decide), h.tab 7 (by decide), h.tab 8 (by decide), h.tab 9 (by decide),
    h.tab 10 (by decide), h.tab 11 (by decide), h.tab 12 (by decide)⟩

/-- The nibbles of byte `k` of `x`, with the bits of `sel`, in the high
doubleword of the vector registers. -/
theorem nib_bytes {x m : BitVec 64} (hm : m = 0x0f0f0f0f0f0f0f0f) {k : Nat} (hk : k < 8) :
    gbyte (x &&& m) k = gbyte x k &&& 0x0f ∧ gbyte ((x >>> 4) &&& m) k = gbyte x k >>> 4 := by
  subst hm; exact ⟨by rw [gbyte_and, gbyte_m0f hk], gbyte_lsr4 x hk⟩

theorem stage1_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa stage1 s = some t ∧
      (∀ k < 8, gbyte (t.gpr .r8) k = Spec.Aes.sbox (inMap k (gbyte (s.gpr .r8) k))) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have T := hc.t
  let x := s.gpr .r8
  let a := s.write .r9 (s.gpr .r8 &&& s.gpr .r12)
  let b := a.write .r10 (a.gpr .r8 >>> 4)
  let c := b.write .r10 (b.gpr .r10 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r9 ++ c.unknowns 0) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r10 ++ d.unknowns 0) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v0 (e.vpr .v0 ||| e.vpr .v18)
  let g := f.writeV .v1 (f.vpr .v1 ||| f.vpr .v18)
  let h := g.writeV .v0 (ofVBytes fun i =>
      let j := (vbyte (g.vpr .v0) i).toNat % 32
      if j < 16 then vbyte (g.vpr .v8) j else vbyte (g.vpr .v9) (j - 16))
  let i := h.writeV .v1 (ofVBytes fun i =>
      let j := (vbyte (h.vpr .v1) i).toNat % 32
      if j < 16 then vbyte (h.vpr .v10) j else vbyte (h.vpr .v11) (j - 16))
  let j := i.writeV .v0 (i.vpr .v0 ^^^ i.vpr .v1)
  let l := j.writeV .v0 (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (j.vpr .v0) i))
  let t := l.write .r8 (vdword (l.vpr .v0) 0)
  refine ⟨t, ?_, fun k hk => ?_, fun r h8 h9 h10 => ?_, fun v hv => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [stage1, nibbles, List.cons_append, List.nil_append, runBlock_cons, exec_and,
      exec_lsr_d (by decide : 4 < 64), exec_mtvsrd, exec_vor, exec_vperm, exec_vxor, exec_vsbox, exec_mfvsrd,
      runStep_some, runBlock_nil]
    rfl
  · have nb := nib_bytes (x := x) hc.mask hk
    have c9 : c.gpr .r9 = x &&& s.gpr .r12 := rfl
    have c10 : c.gpr .r10 = (x >>> 4) &&& s.gpr .r12 := rfl
    have hsel := selIn_eq hk
    have hL : vbyte (g.vpr .v0) (7 - k) = (gbyte x k &&& 0x0f) ||| selIn.getD (7 - k) 0 := by
      show vbyte ((c.gpr .r9 ++ c.unknowns 0) ||| s.vpr .v18) (7 - k) = _
      rw [vbyte_or', vbyte_append _ _ hk, c9, nb.1, T.2.2.2.2.2.2.2.2.2.2.1 (7 - k) (by omega_using [])]
    have hH : vbyte (h.vpr .v1) (7 - k) = (gbyte x k >>> 4) ||| selIn.getD (7 - k) 0 := by
      show vbyte ((c.gpr .r10 ++ d.unknowns 0) ||| s.vpr .v18) (7 - k) = _
      rw [vbyte_or', vbyte_append _ _ hk, c10, nb.2, T.2.2.2.2.2.2.2.2.2.2.1 (7 - k) (by omega_using [])]
    rw [hsel] at hL hH
    have g8 : g.vpr .v8 = s.vpr .v8 := rfl
    have g9 : g.vpr .v9 = s.vpr .v9 := rfl
    have h10 : h.vpr .v10 = s.vpr .v10 := rfl
    have h11 : h.vpr .v11 = s.vpr .v11 := rfl
    have hv0 : h.vpr .v0 = ofVBytes fun i =>
        let j := (vbyte (g.vpr .v0) i).toNat % 32
        if j < 16 then vbyte (g.vpr .v8) j else vbyte (g.vpr .v9) (j - 16) := vpr_writeV_self _ _ _
    have iv1 : i.vpr .v1 = ofVBytes fun i =>
        let j := (vbyte (h.vpr .v1) i).toNat % 32
        if j < 16 then vbyte (h.vpr .v10) j else vbyte (h.vpr .v11) (j - 16) := vpr_writeV_self _ _ _
    have i0 : i.vpr .v0 = h.vpr .v0 := vpr_writeV_of_ne _ _ (by decide)
    have jv0 : j.vpr .v0 = i.vpr .v0 ^^^ i.vpr .v1 := vpr_writeV_self _ _ _
    rw [g8, g9] at hv0
    rw [h10, h11] at iv1
    have l0 := lookup_sel T.1 T.2.1 (by omega_using [] : 7 - k < 16) (toNat_and_0f _) hL (sel_cases _)
    have l1 := lookup_sel T.2.2.1 T.2.2.2.1 (by omega_using [] : 7 - k < 16) (toNat_shr4 _) hH (sel_cases _)
    have jv : vbyte (j.vpr .v0) (7 - k) = inMap k (gbyte x k) := by
      rw [jv0, i0, vbyte_xor', hv0, iv1, l0, l1]
      simp only [sel_iff, inMap, aff]
      split <;> rfl
    have lv0 : l.vpr .v0 = ofVBytes fun i => VectorCrypto.aesSbox (vbyte (j.vpr .v0) i) := vpr_writeV_self _ _ _
    have t8 : t.gpr .r8 = vdword (l.vpr .v0) 0 := gpr_write_self _ _ _
    rw [t8, gbyte_vdword _ hk, lv0, vbyte_packed _ (by omega_using []), jv, Proof.Aes.Vector.sbox_eq]
  · have e1 : t.gpr r = c.gpr r := gpr_write_of_ne _ _ h8
    exact e1.trans ((gpr_write_of_ne _ _ h10).trans ((gpr_write_of_ne _ _ h10).trans (gpr_write_of_ne _ _ h9)))
  · simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    have n0 := hv.1
    have n1 := hv.2.1
    change (j.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (i.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (h.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n1)]
    change (g.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (f.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n1)]
    change (e.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n1)]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    rfl

theorem mask_cases (p : Prop) [Decidable p] : ((if p then 0xff else 0 : Byte) = 0 ∨ (if p then 0xff else 0 : Byte) = 0xff) := by
  by_cases h : p <;> simp [h]

theorem mask_iff (p : Prop) [Decidable p] : ((if p then 0xff else 0 : Byte) = 0xff) ↔ p := by
  by_cases h : p <;> simp [h]

theorem stage2_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa stage2 s = some t ∧
      (∀ k < 8, gbyte (t.gpr .r8) k = outMap k (gbyte (s.gpr .r8) k)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have T := hc.t
  let x := s.gpr .r8
  let a := s.write .r9 (s.gpr .r8 &&& s.gpr .r12)
  let b := a.write .r10 (a.gpr .r8 >>> 4)
  let c := b.write .r10 (b.gpr .r10 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r9 ++ c.unknowns 0) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r10 ++ d.unknowns 0) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v2 (e.vpr .v0 ||| e.vpr .v19)
  let g := f.writeV .v3 (f.vpr .v1 ||| f.vpr .v19)
  let h := g.writeV .v2 (ofVBytes fun i =>
      let j := (vbyte (g.vpr .v2) i).toNat % 32
      if j < 16 then vbyte (g.vpr .v12) j else vbyte (g.vpr .v13) (j - 16))
  let i := h.writeV .v3 (ofVBytes fun i =>
      let j := (vbyte (h.vpr .v3) i).toNat % 32
      if j < 16 then vbyte (h.vpr .v14) j else vbyte (h.vpr .v15) (j - 16))
  let j := i.writeV .v2 (i.vpr .v2 ^^^ i.vpr .v3)
  let l := j.writeV .v0 (ofVBytes fun i =>
      let j' := (vbyte (j.vpr .v0) i).toNat % 32
      if j' < 16 then vbyte (j.vpr .v16) j' else vbyte (j.vpr .v16) (j' - 16))
  let n := l.writeV .v1 (ofVBytes fun i =>
      let j' := (vbyte (l.vpr .v1) i).toNat % 32
      if j' < 16 then vbyte (l.vpr .v17) j' else vbyte (l.vpr .v17) (j' - 16))
  let o := n.writeV .v0 (n.vpr .v0 ^^^ n.vpr .v1)
  let q := o.writeV .v0 ((o.vpr .v2 &&& ~~~o.vpr .v7) ||| (o.vpr .v0 &&& o.vpr .v7))
  let t := q.write .r8 (vdword (q.vpr .v0) 0)
  refine ⟨t, ?_, fun k hk => ?_, fun r h8 h9 h10 => ?_, fun v hv => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [stage2, nibbles, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      runBlock_cons, exec_and, runStep_some, runBlock_cons, exec_lsr_d (by decide : 4 < 64), runStep_some,
      runBlock_cons, exec_and, runStep_some, runBlock_cons, exec_mtvsrd, runStep_some,
      runBlock_cons, exec_mtvsrd, runStep_some, runBlock_cons, exec_vor, runStep_some,
      runBlock_cons, exec_vor, runStep_some, runBlock_cons, exec_vperm, runStep_some,
      runBlock_cons, exec_vperm, runStep_some, runBlock_cons, exec_vxor, runStep_some,
      runBlock_cons, exec_vperm, runStep_some, runBlock_cons, exec_vperm, runStep_some,
      runBlock_cons, exec_vxor, runStep_some, runBlock_cons, exec_vsel, runStep_some,
      runBlock_cons, exec_mfvsrd, runStep_some, runBlock_nil]
  · have nb := nib_bytes (x := x) hc.mask hk
    have c9 : c.gpr .r9 = x &&& s.gpr .r12 := rfl
    have c10 : c.gpr .r10 = (x >>> 4) &&& s.gpr .r12 := rfl
    have hsel := selOut_eq hk
    have e0 : vbyte (e.vpr .v0) (7 - k) = gbyte x k &&& 0x0f := by
      show vbyte (c.gpr .r9 ++ c.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ hk, c9, nb.1]
    have e1 : vbyte (e.vpr .v1) (7 - k) = gbyte x k >>> 4 := by
      show vbyte (c.gpr .r10 ++ d.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ hk, c10, nb.2]
    have hL : vbyte (g.vpr .v2) (7 - k) = (gbyte x k &&& 0x0f) ||| selOut.getD (7 - k) 0 := by
      show vbyte (e.vpr .v0 ||| s.vpr .v19) (7 - k) = _
      rw [vbyte_or', e0, T.2.2.2.2.2.2.2.2.2.2.2.1 (7 - k) (by omega_using [])]
    have hH : vbyte (h.vpr .v3) (7 - k) = (gbyte x k >>> 4) ||| selOut.getD (7 - k) 0 := by
      show vbyte (e.vpr .v1 ||| s.vpr .v19) (7 - k) = _
      rw [vbyte_or', e1, T.2.2.2.2.2.2.2.2.2.2.2.1 (7 - k) (by omega_using [])]
    have jL : vbyte (j.vpr .v0) (7 - k) = gbyte x k &&& 0x0f := e0
    have lH : vbyte (l.vpr .v1) (7 - k) = gbyte x k >>> 4 := e1
    rw [hsel] at hL hH
    have hv2 : h.vpr .v2 = ofVBytes fun i =>
        let j := (vbyte (g.vpr .v2) i).toNat % 32
        if j < 16 then vbyte (g.vpr .v12) j else vbyte (g.vpr .v13) (j - 16) := vpr_writeV_self _ _ _
    have iv3 : i.vpr .v3 = ofVBytes fun i =>
        let j := (vbyte (h.vpr .v3) i).toNat % 32
        if j < 16 then vbyte (h.vpr .v14) j else vbyte (h.vpr .v15) (j - 16) := vpr_writeV_self _ _ _
    have lv0 : l.vpr .v0 = ofVBytes fun i =>
        let j' := (vbyte (j.vpr .v0) i).toNat % 32
        if j' < 16 then vbyte (j.vpr .v16) j' else vbyte (j.vpr .v16) (j' - 16) := vpr_writeV_self _ _ _
    have nv1 : n.vpr .v1 = ofVBytes fun i =>
        let j' := (vbyte (l.vpr .v1) i).toNat % 32
        if j' < 16 then vbyte (l.vpr .v17) j' else vbyte (l.vpr .v17) (j' - 16) := vpr_writeV_self _ _ _
    have g12 : g.vpr .v12 = s.vpr .v12 := rfl
    have g13 : g.vpr .v13 = s.vpr .v13 := rfl
    have h14 : h.vpr .v14 = s.vpr .v14 := rfl
    have h15 : h.vpr .v15 = s.vpr .v15 := rfl
    have j16 : j.vpr .v16 = s.vpr .v16 := rfl
    have l17 : l.vpr .v17 = s.vpr .v17 := rfl
    rw [g12, g13] at hv2
    rw [h14, h15] at iv3
    rw [j16] at lv0
    rw [l17] at nv1
    have l0 := lookup_sel T.2.2.2.2.1 T.2.2.2.2.2.1 (by omega_using [] : 7 - k < 16) (toNat_and_0f _) hL (sel_cases _)
    have l1 := lookup_sel T.2.2.2.2.2.2.1 T.2.2.2.2.2.2.2.1 (by omega_using [] : 7 - k < 16) (toNat_shr4 _) hH (sel_cases _)
    have l2 := lookup_one T.2.2.2.2.2.2.2.2.1 (by omega_using [] : 7 - k < 16) (toNat_and_0f _) jL
    have l3 := lookup_one T.2.2.2.2.2.2.2.2.2.1 (by omega_using [] : 7 - k < 16) (toNat_shr4 _) lH
    have oA : vbyte (o.vpr .v2) (7 - k) =
        if k = 3 ∨ k = 6 then aff out2Lo out2Hi (gbyte x k) else aff outLo outHi (gbyte x k) := by
      show vbyte (i.vpr .v2 ^^^ i.vpr .v3) (7 - k) = _
      rw [vbyte_xor', show i.vpr .v2 = h.vpr .v2 from vpr_writeV_of_ne _ _ (by decide), hv2, iv3, l0, l1]
      simp only [sel_iff, aff]
      split <;> rfl
    have oB : vbyte (o.vpr .v0) (7 - k) =
        out3Lo.getD (gbyte x k &&& 0x0f).toNat 0 ^^^ out3Hi.getD (gbyte x k >>> 4).toNat 0 := by
      rw [show o.vpr .v0 = n.vpr .v0 ^^^ n.vpr .v1 from vpr_writeV_self _ _ _, vbyte_xor',
        show n.vpr .v0 = l.vpr .v0 from vpr_writeV_of_ne _ _ (by decide), lv0, nv1, l2, l3]
    have m7 : vbyte (o.vpr .v7) (7 - k) = if k = 2 ∨ k = 5 then 0xff else 0 := by
      rw [show o.vpr .v7 = s.vpr .v7 from rfl, T.2.2.2.2.2.2.2.2.2.2.2.2 (7 - k) (by omega_using []), mask36_eq hk]
    have qv : vbyte (q.vpr .v0) (7 - k) = outMap k (gbyte x k) := by
      rw [show q.vpr .v0 = (o.vpr .v2 &&& ~~~o.vpr .v7) ||| (o.vpr .v0 &&& o.vpr .v7) from vpr_writeV_self _ _ _,
        vbyte_sel _ _ _ (by omega_using []) (by rw [m7]; exact (mask_cases _).symm.elim Or.inr Or.inl), m7, oA, oB]
      simp only [mask_iff, outMap, aff]
    have t8 : t.gpr .r8 = vdword (q.vpr .v0) 0 := gpr_write_self _ _ _
    rw [t8, gbyte_vdword _ hk, qv]
  · have e1 : t.gpr r = c.gpr r := gpr_write_of_ne _ _ h8
    exact e1.trans ((gpr_write_of_ne _ _ h10).trans ((gpr_write_of_ne _ _ h10).trans (gpr_write_of_ne _ _ h9)))
  · simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨n0, n1, n2, n3⟩ := hv
    change (o.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (n.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (l.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n1)]
    change (j.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    change (i.writeV .v2 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n2)]
    change (h.writeV .v3 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n3)]
    change (g.writeV .v2 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n2)]
    change (f.writeV .v3 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n3)]
    change (e.writeV .v2 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n2)]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n1)]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e n0)]
    rfl

theorem byte_eq_gbyte (x : BitVec 64) (j : Nat) : byte x j = gbyte x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi,
    decide_true, Bool.true_and]

/-- A doubleword from its bytes. -/
theorem eq_of_gbytes {x y : BitVec 64} (h : ∀ k < 8, gbyte x k = gbyte y k) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (BitVec.getLsbD · (i % 8)) (h (i / 8) (by omega_using [hi]))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_using [], decide_true, Bool.true_and] at e
  rwa [show 8 * (i / 8) + i % 8 = i by omega_using []] at e

theorem sbox_maps (x : BitVec 64) {k : Nat} (hk : k < 8) :
    outMap k (Spec.Aes.sbox (inMap k (byte x k))) = substitutedByte x k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp [outMap, inMap, substitutedByte, sbox1_affine]
  · simp [outMap, inMap, substitutedByte, sbox4_affine]
  · simp [outMap, inMap, substitutedByte, sbox3_affine]
  · simp [outMap, inMap, substitutedByte, sbox2_affine]
  · simp [outMap, inMap, substitutedByte, sbox4_affine]
  · simp [outMap, inMap, substitutedByte, sbox3_affine]
  · simp [outMap, inMap, substitutedByte, sbox2_affine]
  · simp [outMap, inMap, substitutedByte, sbox1_affine]
  · omega

theorem sLayer_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa sLayer s = some t ∧ t.gpr .r8 = substituted (s.gpr .r8) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ab, ag, av, am, ard, awr, asp, asy⟩ := stage1_run s hc
  have ac : Consts a := hc.of_eq av (ag _ (by decide) (by decide) (by decide))
  obtain ⟨b, be, bb, bg, bv, bm, brd, bwr, bsp, bsy⟩ := stage2_run a ac
  refine ⟨b, ?_, eq_of_gbytes fun k hk => ?_, fun r h8 h9 h10 => (bg r h8 h9 h10).trans (ag r h8 h9 h10),
    fun v hv => (bv v hv).trans (av v hv), bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp,
    bsy.trans asy⟩
  · rw [sLayer, VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · rw [bb k hk, ab k hk, ← byte_eq_gbyte, sbox_maps _ hk, ← byte_eq_gbyte, substituted,
      VG.Proof.Camellia.Serial.byte_packed _ k hk]

/-! ## The P-function -/

theorem hi_eq (x : BitVec 64) : x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h : i < 32
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    exact BitVec.getLsbD_of_ge x _ (by omega_using [h])

theorem ror0 (y : BitVec 32) : y.rotateRight 0 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem sw_sw (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

theorem pFn_run (s : State) :
    ∃ t, runBlock isa pFn s = some t ∧ t.gpr .r8 = linearWord (s.gpr .r8) ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let x := s.gpr .r8
  let u := (x >>> 32).setWidth 32
  let l := x.setWidth 32
  let ro (r : Reg) (st : State) (k : Nat) : BitVec 64 := (((st.gpr r).setWidth 32).rotateRight k).setWidth 64
  let s1 := s.write .r9 (s.gpr .r8 >>> 32)
  let s2 := s1.write .r10 (ro .r8 s1 0)
  let s3 := s2.write .r11 (ro .r9 s2 8)
  let s4 := s3.write .r11 (s3.gpr .r9 ^^^ s3.gpr .r11)
  let s5 := s4.write .r4 (ro .r9 s4 16)
  let s6 := s5.write .r11 (s5.gpr .r11 ^^^ s5.gpr .r4)
  let s7 := s6.write .r4 (ro .r10 s6 8)
  let s8 := s7.write .r0 (ro .r10 s7 16)
  let s9 := s8.write .r4 (s8.gpr .r4 ^^^ s8.gpr .r0)
  let s10 := s9.write .r0 (ro .r10 s9 24)
  let s11 := s10.write .r4 (s10.gpr .r4 ^^^ s10.gpr .r0)
  let s12 := s11.write .r11 (s11.gpr .r11 ^^^ s11.gpr .r4)
  let s13 := s12.write .r0 (ro .r9 s12 24)
  let s14 := s13.write .r10 (s13.gpr .r9 ^^^ s13.gpr .r0)
  let s15 := s14.write .r10 (s14.gpr .r10 ^^^ s14.gpr .r4)
  let s16 := s15.write .r11 (s15.gpr .r11 <<< 32)
  let t := s16.write .r8 (s16.gpr .r11 ||| s16.gpr .r10)
  have W : ∀ (st : State) (r : Reg) (v : BitVec 64), (st.write r v).gpr r = v := fun st r v => gpr_write_self _ _ _
  have N : ∀ (st : State) (r r' : Reg) (v : BitVec 64), r' ≠ r → (st.write r v).gpr r' = st.gpr r' :=
    fun st r r' v h => gpr_write_of_ne _ _ h
  refine ⟨t, ?_, ?_, fun r a0 a4 a8 a9 a10 a11 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [pFn, runBlock_cons, exec_lsr_d (by decide : 32 < 64), exec_rotr_w (by decide : 0 < 32),
      exec_rotr_w (by decide : 8 < 32), exec_rotr_w (by decide : 16 < 32), exec_rotr_w (by decide : 24 < 32),
      exec_logic, exec_lsl (by decide : 32 < 64), runStep_some, runBlock_nil]
    rfl
  · have ro_eq : ∀ (r : Reg) (st : State) (k : Nat) (y : BitVec 32), st.gpr r = y.setWidth 64 →
        ro r st k = (y.rotateRight k).setWidth 64 := fun r st k y h => by
      show (((st.gpr r).setWidth 32).rotateRight k).setWidth 64 = _
      rw [h, sw_sw]
    have x1 : s1.gpr .r9 = u.setWidth 64 := (W _ _ _).trans (hi_eq x)
    have x2 : s2.gpr .r10 = l.setWidth 64 := by
      rw [W]; show ((x.setWidth 32).rotateRight 0).setWidth 64 = _; rw [ror0]
    have y2 : s2.gpr .r9 = u.setWidth 64 := (N _ _ _ _ (by decide)).trans x1
    have x3 : s3.gpr .r11 = (u.rotateRight 8).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ y2)
    have y3 : s3.gpr .r9 = u.setWidth 64 := (N _ _ _ _ (by decide)).trans y2
    have x4 : s4.gpr .r11 = (u ^^^ u.rotateRight 8).setWidth 64 := by
      rw [W, y3, x3]
      simp only [BitVec.setWidth_xor]
    have y4 : s4.gpr .r9 = u.setWidth 64 := (N _ _ _ _ (by decide)).trans y3
    have x5 : s5.gpr .r4 = (u.rotateRight 16).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ y4)
    have x6 : s6.gpr .r11 = (u ^^^ u.rotateRight 8 ^^^ u.rotateRight 16).setWidth 64 := by
      rw [W, x5, show s5.gpr .r11 = s4.gpr .r11 from N _ _ _ _ (by decide), x4]
      simp only [BitVec.setWidth_xor]
    have z6 : s6.gpr .r10 = l.setWidth 64 := by
      rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), x2]
    have x7 : s7.gpr .r4 = (l.rotateRight 8).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ z6)
    have z7 : s7.gpr .r10 = l.setWidth 64 := (N _ _ _ _ (by decide)).trans z6
    have x8 : s8.gpr .r0 = (l.rotateRight 16).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ z7)
    have x9 : s9.gpr .r4 = (l.rotateRight 8 ^^^ l.rotateRight 16).setWidth 64 := by
      rw [W, x8, show s8.gpr .r4 = s7.gpr .r4 from N _ _ _ _ (by decide), x7]
      simp only [BitVec.setWidth_xor]
    have z9 : s9.gpr .r10 = l.setWidth 64 := (N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans z7)
    have x10 : s10.gpr .r0 = (l.rotateRight 24).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ z9)
    have x11 : s11.gpr .r4 = (l.rotateRight 8 ^^^ l.rotateRight 16 ^^^ l.rotateRight 24).setWidth 64 := by
      rw [W, x10, show s10.gpr .r4 = s9.gpr .r4 from N _ _ _ _ (by decide), x9]
      simp only [BitVec.setWidth_xor]
    have w11 : s11.gpr .r11 = (u ^^^ u.rotateRight 8 ^^^ u.rotateRight 16).setWidth 64 := by
      rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide),
        N _ _ _ _ (by decide), x6]
    have x12 : s12.gpr .r11 = ((u ^^^ u.rotateRight 8 ^^^ u.rotateRight 16) ^^^
        (l.rotateRight 8 ^^^ l.rotateRight 16 ^^^ l.rotateRight 24)).setWidth 64 := by
      rw [W, w11, show s11.gpr .r4 = _ from x11]
      simp only [BitVec.setWidth_xor]
    have y12 : s12.gpr .r9 = u.setWidth 64 := by
      rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide),
        N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), y4]
    have x13 : s13.gpr .r0 = (u.rotateRight 24).setWidth 64 := (W _ _ _).trans (ro_eq _ _ _ _ y12)
    have x14 : s14.gpr .r10 = (u ^^^ u.rotateRight 24).setWidth 64 := by
      rw [W, x13, show s13.gpr .r9 = s12.gpr .r9 from N _ _ _ _ (by decide), y12]
      simp only [BitVec.setWidth_xor]
    have x15 : s15.gpr .r10 = (u ^^^ u.rotateRight 24 ^^^
        (l.rotateRight 8 ^^^ l.rotateRight 16 ^^^ l.rotateRight 24)).setWidth 64 := by
      rw [W, x14, show s14.gpr .r4 = s11.gpr .r4 from
        (N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans (N _ _ _ _ (by decide))), x11]
      simp only [BitVec.setWidth_xor]
    have x16 : s16.gpr .r11 = ((u ^^^ u.rotateRight 8 ^^^ u.rotateRight 16) ^^^
        (l.rotateRight 8 ^^^ l.rotateRight 16 ^^^ l.rotateRight 24)).setWidth 64 <<< 32 := by
      rw [W, show s15.gpr .r11 = s12.gpr .r11 from
        (N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans (N _ _ _ _ (by decide))), x12]
    have z16 : s16.gpr .r10 = _ := (N _ _ _ _ (by decide)).trans x15
    rw [W, x16, z16, ← BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.setWidth_eq]
    rfl
  · rw [N _ _ _ _ a8, N _ _ _ _ a11, N _ _ _ _ a10, N _ _ _ _ a10, N _ _ _ _ a0, N _ _ _ _ a11, N _ _ _ _ a4,
      N _ _ _ _ a0, N _ _ _ _ a4, N _ _ _ _ a0, N _ _ _ _ a4, N _ _ _ _ a11, N _ _ _ _ a4, N _ _ _ _ a11,
      N _ _ _ _ a11, N _ _ _ _ a10, N _ _ _ _ a9]

/-! ## A round -/

theorem getLsbD_readW64 (m : Mem) (a : Addr) {i : Nat} (hi : i < 64) :
    (m.readW a 64).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (by omega_using [hi]), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega_using []

/-- A byte-reversed load reads the word big-endian. -/
theorem readBE (m : Mem) (p : Addr) : rev64 (m.readW p 64) = Spec.Camellia.wordAt m p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show rev64 = byteRev64 from rfl, byteRev64_getLsbD _ hi, Proof.Camellia.getLsbD_wordAt m p hi,
    getLsbD_readW64 _ _ (by omega_using [])]
  rw [show (8 * (7 - i / 8) + i % 8) / 8 = 7 - i / 8 by omega_using [], show (8 * (7 - i / 8) + i % 8) % 8 = i % 8 by omega_using []]

/-- The registers a round writes, but its output. -/
def fWrites : List Reg := [.r0, .r4, .r8, .r9, .r10, .r11]

/-- The schedule's word `w`. -/
def keyWord (s : State) (w : Nat) : BitVec 64 := Spec.Camellia.wordAt s.mem (s.gpr .r3 + BitVec.ofNat 64 (8 * w))

theorem loadKey_run {s : State} {w : Nat} (hw : 8 * w < 2 ^ 15)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * w)) 8) :
    ∃ t, runBlock isa (loadKey w) s = some t ∧ t.gpr .r4 = keyWord s w ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a := s.write .r0 (BitVec.ofNat 64 (8 * w))
  have ea : a.gpr .r3 + a.gpr .r0 = s.gpr .r3 + BitVec.ofNat 64 (8 * w) := by
    rw [gpr_write_of_ne _ _ (by decide), gpr_write_self]
  have ar : InRegions (a.rd ++ a.wr) (a.gpr .r3 + a.gpr .r0) 8 := by rw [ea]; exact hr
  refine ⟨a.write .r4 (rev64 (a.mem.readW (a.gpr .r3 + a.gpr .r0) 64)), ?_, ?_, fun r h0 h4 => ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [loadKey, runBlock_cons, exec_li hw, runStep_some, runBlock_cons, exec_loadRev_d (by decide) ar,
      runStep_some, runBlock_nil]
  · rw [gpr_write_self, ea, readBE]; rfl
  · rw [gpr_write_of_ne _ _ h4, gpr_write_of_ne _ _ h0]

theorem fRound_run {s : State} {a b : Reg} (hab : a = .r6 ∧ b = .r7 ∨ a = .r7 ∧ b = .r6) {w : Nat}
    (hw : 8 * w < 2 ^ 15) (hc : Consts s)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * w)) 8) :
    ∃ t, runBlock isa (fRound a b w) s = some t ∧
      t.gpr b = s.gpr b ^^^ Spec.Camellia.f (s.gpr a) (keyWord s w) ∧
      (∀ r, r ∉ fWrites → r ≠ b → t.gpr r = s.gpr r) ∧ Consts t ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have hna : a ∉ fWrites ∧ a ≠ .r12 := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hnb : b ∉ fWrites ∧ b ≠ .r12 ∧ b ≠ a := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have nf : ∀ r, r ∉ fWrites → r ≠ .r0 ∧ r ≠ .r4 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
    intro r hr; simp only [fWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr
  obtain ⟨k, ke, k4, kg, kv, km, krd, kwr, ksp, ksy⟩ := loadKey_run hw hr
  let x := k.write .r8 (k.gpr a ^^^ k.gpr .r4)
  have xc : Consts x := hc.of_eq (fun v _ => by rw [show x.vpr v = k.vpr v from rfl, kv])
    ((gpr_write_of_ne _ _ (by decide)).trans (kg _ (by decide) (by decide)))
  obtain ⟨y, ye, y8, yg, yv, ym, yrd, ywr, ysp, ysy⟩ := sLayer_run x xc
  have yc : Consts y := xc.of_eq yv (yg _ (by decide) (by decide) (by decide))
  obtain ⟨z, ze, z8, zg, zv, zm, zrd, zwr, zsp, zsy⟩ := pFn_run y
  let t := z.write b (z.gpr b ^^^ z.gpr .r8)
  have ka : k.gpr a = s.gpr a := kg _ (nf a hna.1).1 (nf a hna.1).2.1
  have kb : k.gpr b = s.gpr b := kg _ (nf b hnb.1).1 (nf b hnb.1).2.1
  have zb : z.gpr b = s.gpr b := by
    have h := nf b hnb.1
    rw [zg _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2, yg _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1,
      gpr_write_of_ne _ _ h.2.2.1, kb]
  have frame : ∀ r, r ∉ fWrites → r ≠ b → t.gpr r = s.gpr r := fun r hr hb => by
    have h := nf r hr
    rw [gpr_write_of_ne _ _ hb, zg _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2,
      yg _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1, gpr_write_of_ne _ _ h.2.2.1, kg _ h.1 h.2.1]
  refine ⟨t, ?_, ?_, frame, ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fRound, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, ke, Option.bind_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil,
      Option.bind_some, ye, Option.bind_some, ze, Option.bind_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_nil]
  · rw [gpr_write_self, zb, z8, y8, show x.gpr .r8 = k.gpr a ^^^ k.gpr .r4 from gpr_write_self _ _ _, ka, k4,
      VG.Proof.Camellia.Serial.f_eq]
  · exact yc.of_eq (fun v _ => by rw [show t.vpr v = z.vpr v from rfl, zv])
      ((gpr_write_of_ne _ _ hnb.2.1.symm).trans (zg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
  · rw [show t.vpr v = z.vpr v from rfl, zv, yv v hv, show x.vpr v = k.vpr v from rfl, kv]
  · exact zm.trans (ym.trans km)
  · exact zrd.trans (yrd.trans krd)
  · exact zwr.trans (ywr.trans kwr)
  · exact zsp.trans (ysp.trans ksp)
  · exact zsy.trans (ysy.trans ksy)

/-! ## Six rounds -/

/-- The schedule's words are in reach. -/
def KeyIn (s : State) : Prop := ∀ i < 34, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * i)) 8

theorem KeyIn.of_eq {s t : State} (h : KeyIn s) (h3 : t.gpr .r3 = s.gpr .r3) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : KeyIn t := fun i hi => by rw [h3, hrd, hwr]; exact h i hi

theorem keyWord_eq {s t : State} (h3 : t.gpr .r3 = s.gpr .r3) (hm : t.mem = s.mem) (w : Nat) :
    keyWord t w = keyWord s w := by rw [keyWord, keyWord, h3, hm]

/-- The halves. -/
def halves (s : State) : BitVec 64 × BitVec 64 := (s.gpr .r6, s.gpr .r7)

/-- The registers the rounds write. -/
def rWrites : List Reg := [.r0, .r4, .r6, .r7, .r8, .r9, .r10, .r11]

theorem pair_run {s : State} {w : Nat} (hw : 8 * (w + 1) < 2 ^ 15) (hw' : w + 1 < 34) (hc : Consts s)
    (hk : KeyIn s) :
    ∃ t, runBlock isa (fRound .r6 .r7 w ++ fRound .r7 .r6 (w + 1)) s = some t ∧
      halves t = Proof.Camellia.pair (keyWord s w) (keyWord s (w + 1)) (halves s) ∧
      (∀ r, r ∉ rWrites → t.gpr r = s.gpr r) ∧ Consts t ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, a7, ag, ac, av, am, ard, awr, asp, asy⟩ :=
    fRound_run (Or.inl ⟨rfl, rfl⟩) (by omega_using [hw]) hc (hk w (by omega_using [hw']))
  have a3 : a.gpr .r3 = s.gpr .r3 := ag _ (by decide) (by decide)
  obtain ⟨b, be, b6, bg, bc, bv, bm, brd, bwr, bsp, bsy⟩ :=
    fRound_run (Or.inr ⟨rfl, rfl⟩) hw ac ((hk.of_eq a3 ard awr) (w + 1) hw')
  have a6 : a.gpr .r6 = s.gpr .r6 := ag _ (by decide) (by decide)
  have b7 : b.gpr .r7 = a.gpr .r7 := bg _ (by decide) (by decide)
  refine ⟨b, ?_, ?_, fun r hr => ?_, bc, fun v hv => (bv v hv).trans (av v hv), bm.trans am, brd.trans ard,
    bwr.trans awr, bsp.trans asp, bsy.trans asy⟩
  · rw [VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · rw [halves, halves, b6, b7, a7, a6, keyWord_eq a3 am, Proof.Camellia.pair]
  · have h : r ∉ fWrites ∧ r ≠ .r6 ∧ r ≠ .r7 := by
      simp only [rWrites, fWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨⟨hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2⟩, hr.2.2.1, hr.2.2.2.1⟩
    rw [bg r h.1 h.2.1, ag r h.1 h.2.2]

theorem six_run {s : State} {w : Nat} (hw : w + 6 ≤ 34) (hc : Consts s) (hk : KeyIn s) :
    ∃ t, runBlock isa (six w) s = some t ∧
      halves t = Proof.Camellia.pair (keyWord s (w + 4)) (keyWord s (w + 5))
        (Proof.Camellia.pair (keyWord s (w + 2)) (keyWord s (w + 3))
          (Proof.Camellia.pair (keyWord s w) (keyWord s (w + 1)) (halves s))) ∧
      (∀ r, r ∉ rWrites → t.gpr r = s.gpr r) ∧ Consts t ∧
      (∀ v, v ∉ temps → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ah, ag, ac, av, am, ard, awr, asp, asy⟩ := pair_run (w := w) (by omega_using [hw]) (by omega_using [hw]) hc hk
  have a3 : a.gpr .r3 = s.gpr .r3 := ag _ (by decide)
  obtain ⟨b, be, bh, bg, bc, bv, bm, brd, bwr, bsp, bsy⟩ :=
    pair_run (w := w + 2) (by omega_using [hw]) (by omega_using [hw]) ac (hk.of_eq a3 ard awr)
  have b3 : b.gpr .r3 = s.gpr .r3 := (bg _ (by decide)).trans a3
  have bm' : b.mem = s.mem := bm.trans am
  obtain ⟨c, ce, ch, cg, cc, cv, cm, crd, cwr, csp, csy⟩ :=
    pair_run (w := w + 4) (by omega_using [hw]) (by omega_using [hw]) bc (hk.of_eq b3 (brd.trans ard) (bwr.trans awr))
  refine ⟨c, ?_, ?_, fun r hr => (cg r hr).trans ((bg r hr).trans (ag r hr)), cc,
    fun v hv => (cv v hv).trans ((bv v hv).trans (av v hv)), cm.trans bm', crd.trans (brd.trans ard),
    cwr.trans (bwr.trans awr), csp.trans (bsp.trans asp), csy.trans (bsy.trans asy)⟩
  · simp only [six, List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [VG.Interleave.runBlock_append, VG.Interleave.runBlock_append]
    rw [show w + 2 * 2 = w + 4 by omega_using [], show w + 2 * 2 + 1 = w + 4 + 1 by omega_using [], show w + 2 + 1 = w + 2 + 1 by rfl]
    rw [ae, Option.bind_some, be, Option.bind_some, ce]
  · rw [ch, bh, ah, keyWord_eq b3 bm', keyWord_eq b3 bm', keyWord_eq a3 am, keyWord_eq a3 am,
      show w + 2 + 1 = w + 3 by omega_using [], show w + 4 + 1 = w + 5 by omega_using []]

/-! ## FL and FLINV -/

theorem ror31 (y : BitVec 32) : y.rotateRight 31 = y.rotateLeft 1 := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
  simp only [show 31 % 32 = 31 from rfl, show 1 % 32 = 1 from rfl]
  exact BitVec.or_comm _ _

theorem fl_run {s : State} {r : Reg} (hr : r = .r6 ∨ r = .r7) {w : Nat} (inv : Bool) (hw : 8 * w < 2 ^ 15)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * w)) 8) :
    ∃ t, runBlock isa (fl r w inv) s = some t ∧
      t.gpr r = (if inv then Spec.Camellia.flinv else Spec.Camellia.fl) (s.gpr r) (keyWord s w) ∧
      (∀ q, q ∉ fWrites → q ≠ r → t.gpr q = s.gpr q) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have hn : r ∉ fWrites := by rcases hr with rfl | rfl <;> decide
  have nf : ∀ q, q ∉ fWrites → q ≠ .r0 ∧ q ≠ .r4 ∧ q ≠ .r8 ∧ q ≠ .r9 ∧ q ≠ .r10 ∧ q ≠ .r11 := by
    intro q hq; simp only [fWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq; exact hq
  obtain ⟨k, ke, k4, kg, kv, km, krd, kwr, ksp, ksy⟩ := loadKey_run hw hk
  have W : ∀ (st : State) (q : Reg) (v : BitVec 64), (st.write q v).gpr q = v := fun st q v => gpr_write_self _ _ _
  have N : ∀ (st : State) (q q' : Reg) (v : BitVec 64), q' ≠ q → (st.write q v).gpr q' = st.gpr q' :=
    fun st q q' v h => gpr_write_of_ne _ _ h
  let X := s.gpr r
  let K := keyWord s w
  let x1 := (X >>> 32).setWidth 32
  let x2 := X.setWidth 32
  let k1 := (K >>> 32).setWidth 32
  let k2 := K.setWidth 32
  have kr : k.gpr r = X := kg _ (nf r hn).1 (nf r hn).2.1
  let a1 := k.write .r9 (k.gpr r >>> 32)
  let a2 := a1.write .r10 (((a1.gpr r).setWidth 32).rotateRight 0 |>.setWidth 64)
  let a3 := a2.write .r11 (a2.gpr .r4 >>> 32)
  let a4 := a3.write .r4 (((a3.gpr .r4).setWidth 32).rotateRight 0 |>.setWidth 64)
  have hr9 : r ≠ .r9 := (nf r hn).2.2.2.1
  have hr10 : r ≠ .r10 := (nf r hn).2.2.2.2.1
  have v9 : a4.gpr .r9 = x1.setWidth 64 := by
    rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), W, kr, hi_eq]
  have v10 : a4.gpr .r10 = x2.setWidth 64 := by
    rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), W, N _ _ _ _ (Ne.symm hr9).symm, kr, ror0]
  have v11 : a4.gpr .r11 = k1.setWidth 64 := by
    rw [N _ _ _ _ (by decide), W, N _ _ _ _ (by decide), N _ _ _ _ (by decide), k4, hi_eq]
  have v4 : a4.gpr .r4 = k2.setWidth 64 := by
    rw [W, N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), k4, ror0]
  have ha : runBlock isa (loadKey w ++ [.lsr .d .r9 r 32, .rotr .w .r10 r 0, .lsr .d .r11 .r4 32,
      .rotr .w .r4 .r4 0]) s = some a4 := by
    rw [VG.Interleave.runBlock_append, ke, Option.bind_some, runBlock_cons, exec_lsr_d (by decide), runStep_some,
      runBlock_cons, exec_rotr_w (by decide), runStep_some, runBlock_cons, exec_lsr_d (by decide), runStep_some,
      runBlock_cons, exec_rotr_w (by decide), runStep_some, runBlock_nil]
  have a4g : ∀ q, q ∉ fWrites → a4.gpr q = s.gpr q := fun q hq => by
    have h := nf q hq
    rw [N _ _ _ _ h.2.1, N _ _ _ _ h.2.2.2.2.2, N _ _ _ _ h.2.2.2.2.1, N _ _ _ _ h.2.2.2.1, kg _ h.1 h.2.1]
  -- The two halves of FL, from a state with x1, x2, k1, k2 in r9, r10, r11, r4.
  have lo_run : ∀ (st : State) (y1 y2 : BitVec 32), st.gpr .r9 = y1.setWidth 64 → st.gpr .r10 = y2.setWidth 64 →
      st.gpr .r11 = k1.setWidth 64 → st.gpr .r4 = k2.setWidth 64 →
      ∃ t, runBlock isa [Instr.logic .and .r0 .r9 .r11, .rotr .w .r0 .r0 31, .logic .xor .r10 .r10 .r0] st = some t ∧
        t.gpr .r9 = y1.setWidth 64 ∧ t.gpr .r10 = (y2 ^^^ (y1 &&& k1).rotateLeft 1).setWidth 64 ∧
        t.gpr .r11 = k1.setWidth 64 ∧ t.gpr .r4 = k2.setWidth 64 ∧
        (∀ q, q ∉ fWrites → t.gpr q = st.gpr q) ∧ t.vpr = st.vpr ∧ t.mem = st.mem ∧ t.rd = st.rd ∧
        t.wr = st.wr ∧ t.sp = st.sp ∧ t.syms = st.syms := by
    intro st y1 y2 h9 h10 h11 h4
    let b1 := st.write .r0 (st.gpr .r9 &&& st.gpr .r11)
    let b2 := b1.write .r0 (((b1.gpr .r0).setWidth 32).rotateRight 31 |>.setWidth 64)
    let b3 := b2.write .r10 (b2.gpr .r10 ^^^ b2.gpr .r0)
    refine ⟨b3, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_rotr_w (by decide), runStep_some,
        runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), h9]
    · rw [W, W, N _ _ _ _ (by decide), N _ _ _ _ (by decide), W, h9, h11, h10, ← BitVec.setWidth_and, sw_sw,
        ror31, BitVec.setWidth_xor]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), h11]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), N _ _ _ _ (by decide), h4]
    · have h := nf q hq
      rw [N _ _ _ _ h.2.2.2.2.1, N _ _ _ _ h.1, N _ _ _ _ h.1]
  have hi_run : ∀ (st : State) (y1 y2 : BitVec 32), st.gpr .r9 = y1.setWidth 64 → st.gpr .r10 = y2.setWidth 64 →
      st.gpr .r11 = k1.setWidth 64 → st.gpr .r4 = k2.setWidth 64 →
      ∃ t, runBlock isa [Instr.logic .or .r0 .r10 .r4, .logic .xor .r9 .r9 .r0] st = some t ∧
        t.gpr .r9 = (y1 ^^^ (y2 ||| k2)).setWidth 64 ∧ t.gpr .r10 = y2.setWidth 64 ∧
        t.gpr .r11 = k1.setWidth 64 ∧ t.gpr .r4 = k2.setWidth 64 ∧
        (∀ q, q ∉ fWrites → t.gpr q = st.gpr q) ∧ t.vpr = st.vpr ∧ t.mem = st.mem ∧ t.rd = st.rd ∧
        t.wr = st.wr ∧ t.sp = st.sp ∧ t.syms = st.syms := by
    intro st y1 y2 h9 h10 h11 h4
    let b1 := st.write .r0 (st.gpr .r10 ||| st.gpr .r4)
    let b2 := b1.write .r9 (b1.gpr .r9 ^^^ b1.gpr .r0)
    refine ⟨b2, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    · rw [W, W, N _ _ _ _ (by decide), h9, h10, h4, ← BitVec.setWidth_or, BitVec.setWidth_xor]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), h10]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), h11]
    · rw [N _ _ _ _ (by decide), N _ _ _ _ (by decide), h4]
    · have h := nf q hq
      rw [N _ _ _ _ h.2.2.2.1, N _ _ _ _ h.1]
  have join_run : ∀ (st : State) (y1 y2 : BitVec 32), st.gpr .r9 = y1.setWidth 64 → st.gpr .r10 = y2.setWidth 64 →
      ∃ t, runBlock isa [Instr.lsl .r9 .r9 32, .logic .or r .r9 .r10] st = some t ∧ t.gpr r = y1 ++ y2 ∧
        (∀ q, q ∉ fWrites → q ≠ r → t.gpr q = st.gpr q) ∧ t.vpr = st.vpr ∧ t.mem = st.mem ∧ t.rd = st.rd ∧
        t.wr = st.wr ∧ t.sp = st.sp ∧ t.syms = st.syms := by
    intro st y1 y2 h9 h10
    let b1 := st.write .r9 (st.gpr .r9 <<< 32)
    let b2 := b1.write r (b1.gpr .r9 ||| b1.gpr .r10)
    refine ⟨b2, ?_, ?_, fun q hq hqr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    · rw [W, W, N _ _ _ _ (by decide), h9, h10, ← BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
        BitVec.setWidth_eq]
    · rw [N _ _ _ _ hqr, N _ _ _ _ (nf q hq).2.2.2.1]
  have fl_eq : Spec.Camellia.fl X K =
      (x1 ^^^ ((x2 ^^^ (x1 &&& k1).rotateLeft 1) ||| k2)) ++ (x2 ^^^ (x1 &&& k1).rotateLeft 1) := rfl
  have flinv_eq : Spec.Camellia.flinv X K =
      (x1 ^^^ (x2 ||| k2)) ++ (x2 ^^^ ((x1 ^^^ (x2 ||| k2)) &&& k1).rotateLeft 1) := rfl
  let pre : List Instr := loadKey w ++ [.lsr .d .r9 r 32, .rotr .w .r10 r 0, .lsr .d .r11 .r4 32,
      .rotr .w .r4 .r4 0]
  let lo : List Instr := [Instr.logic .and .r0 .r9 .r11, .rotr .w .r0 .r0 31, .logic .xor .r10 .r10 .r0]
  let hi : List Instr := [Instr.logic .or .r0 .r10 .r4, .logic .xor .r9 .r9 .r0]
  let jn : List Instr := [Instr.lsl .r9 .r9 32, .logic .or r .r9 .r10]
  cases inv
  · obtain ⟨b, be, b9, b10, b11, b4, bg, bv, bm, brd, bwr, bsp, bsy⟩ := lo_run a4 x1 x2 v9 v10 v11 v4
    obtain ⟨c, ce, c9, c10, _, _, cg, cv, cm, crd, cwr, csp, csy⟩ := hi_run b _ _ b9 b10 b11 b4
    obtain ⟨d, de, dr, dg, dv, dm, drd, dwr, dsp, dsy⟩ := join_run c _ _ c9 c10
    refine ⟨d, ?_, ?_, fun q hq hqr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have e : fl r w false = pre ++ (lo ++ (hi ++ jn)) := by simp [fl, pre, lo, hi, jn]
      rw [e, VG.Interleave.runBlock_append, ha, Option.bind_some, VG.Interleave.runBlock_append, be,
        Option.bind_some, VG.Interleave.runBlock_append, ce, Option.bind_some, de]
    · rw [dr]; exact fl_eq.symm
    · rw [dg q hq hqr, cg q hq, bg q hq, a4g q hq]
    · rw [dv, cv, bv]; exact kv
    · rw [dm, cm, bm]; exact km
    · rw [drd, crd, brd]; exact krd
    · rw [dwr, cwr, bwr]; exact kwr
    · rw [dsp, csp, bsp]; exact ksp
    · rw [dsy, csy, bsy]; exact ksy
  · obtain ⟨b, be, b9, b10, b11, b4, bg, bv, bm, brd, bwr, bsp, bsy⟩ := hi_run a4 x1 x2 v9 v10 v11 v4
    obtain ⟨c, ce, c9, c10, _, _, cg, cv, cm, crd, cwr, csp, csy⟩ := lo_run b _ _ b9 b10 b11 b4
    obtain ⟨d, de, dr, dg, dv, dm, drd, dwr, dsp, dsy⟩ := join_run c _ _ c9 c10
    refine ⟨d, ?_, ?_, fun q hq hqr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have e : fl r w true = pre ++ (hi ++ (lo ++ jn)) := by simp [fl, pre, lo, hi, jn]
      rw [e, VG.Interleave.runBlock_append, ha, Option.bind_some, VG.Interleave.runBlock_append, be,
        Option.bind_some, VG.Interleave.runBlock_append, ce, Option.bind_some, de]
    · rw [dr]; exact flinv_eq.symm
    · rw [dg q hq hqr, cg q hq, bg q hq, a4g q hq]
    · rw [dv, cv, bv]; exact kv
    · rw [dm, cm, bm]; exact km
    · rw [drd, crd, brd]; exact krd
    · rw [dwr, cwr, bwr]; exact kwr
    · rw [dsp, csp, bsp]; exact ksp
    · rw [dsy, csy, bsy]; exact ksy

/-! ## The block -/

/-- The two big-endian words in the block buffer are the decoded block's halves. -/
theorem decoded_halves (m : Mem) (p : Addr) :
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p) >>> 64).setWidth 64 = rev64 (m.readW p 64) ∧
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)).setWidth 64 =
      rev64 (m.readW (p + BitVec.ofNat 64 8) 64) := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [readBE, Proof.Camellia.getLsbD_wordAt _ _ hi]
    have h := congrArg (fun b : Byte => b.getLsbD (i % 8))
      (Proof.Camellia.byteOf_hi (Spec.Camellia.blockAt m p) (i := 7 - i / 8) (by omega_using []))
    simp only [Proof.Camellia.byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i % 8 < 8 by omega_using [], decide_true, Bool.true_and,
      show 56 - 8 * (7 - i / 8) + i % 8 = i by omega_using [hi], Spec.Camellia.blockAt, Vector.getElem_ofFn] at h
    simpa only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and,
      Spec.Camellia.blockAt] using h
  · rw [readBE, Proof.Camellia.getLsbD_wordAt _ _ hi]
    have h := congrArg (fun b : Byte => b.getLsbD (i % 8))
      (Proof.Camellia.byteOf_lo (Spec.Camellia.blockAt m p) (i := 7 - i / 8) (by omega_using []))
    simp only [Proof.Camellia.byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i % 8 < 8 by omega_using [], decide_true, Bool.true_and,
      show 56 - 8 * (7 - i / 8) + i % 8 = i by omega_using [hi], Spec.Camellia.blockAt, Vector.getElem_ofFn] at h
    rw [VG.Offset.add_add]
    simpa only [show 8 + (7 - i / 8) = 8 + 7 - i / 8 by omega_using [hi],
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Spec.Camellia.blockAt] using h

/-- Two stored little-endian words are the big-endian output block. -/
theorem stored_bytes {m : Mem} {p : Addr} {hi lo : BitVec 64}
    (h0 : m.readW p 64 = rev64 hi) (h1 : m.readW (p + BitVec.ofNat 64 8) 64 = rev64 lo) :
    Spec.Aes.bytesAt m p 16 = (Spec.Camellia.encodeBlock (hi ++ lo)).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi16 _
  have hn : i < 16 := by simpa [Spec.Aes.bytesAt] using hi16
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList]
  rw [Proof.Camellia.encodeBlock_getElem _ _ hn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : i < 8
  · simp only [h, ite_true]
    have b : m (p + BitVec.ofNat 64 i) = (m.readW p 64).extractLsb' (8 * i) 8 := by
      change m (p + BitVec.ofNat 64 i) = (m.read p 8).extractLsb' (8 * i) 8
      exact (Mem.extractLsb'_read m p h).symm
    rw [h0] at b
    rw [b]
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    change (byteRev64 hi).getLsbD (8 * i + j) = _
    rw [byteRev64_getLsbD _ (by omega_using [hj, h]), Proof.Camellia.getLsbD_byteOf _ h hj]
    congr 1 <;> omega_using [hj]
  · simp only [h, ite_false]
    have b : m (p + BitVec.ofNat 64 8 + BitVec.ofNat 64 (i - 8)) =
        (m.readW (p + BitVec.ofNat 64 8) 64).extractLsb' (8 * (i - 8)) 8 := by
      change m _ = (m.read (p + BitVec.ofNat 64 8) 8).extractLsb' (8 * (i - 8)) 8
      exact (Mem.extractLsb'_read m _ (by omega_using [hn] : i - 8 < 8)).symm
    rw [h1, VG.Offset.add_add, show 8 + (i - 8) = i by omega_using [h]] at b
    rw [b]
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    change (byteRev64 lo).getLsbD (8 * (i - 8) + j) = _
    rw [byteRev64_getLsbD _ (by omega_using [hn, hj]), Proof.Camellia.getLsbD_byteOf _ (by omega_using [hn]) hj]
    congr 1 <;> omega_using [hj]

/-- The block's address. -/
abbrev blkA (s : State) : Addr := s.gpr sb + BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot)

theorem tailSlot_val : Impl.Camellia.PPC64LE.tailSlot = 386 := rfl

theorem loadBlock_run {s : State} (hk : KeyIn s)
    (hb : ∀ d, d = 0 ∨ d = 8 → InRegions (s.rd ++ s.wr) (blkA s + BitVec.ofNat 64 d) 8) :
    ∃ t, runBlock isa loadBlock s = some t ∧
      halves t = ((Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s)) >>> 64).setWidth 64 ^^^
          keyWord s 0,
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))).setWidth 64 ^^^ keyWord s 1) ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have N : ∀ (st : State) (q q' : Reg) (v : BitVec 64), q' ≠ q → (st.write q v).gpr q' = st.gpr q' :=
    fun st q q' v h => gpr_write_of_ne _ _ h
  have dh := decoded_halves s.mem (blkA s)
  let a1 := s.write .r0 (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot))
  have e1 : a1.gpr sb + a1.gpr .r0 = blkA s := by rw [N _ _ _ _ (by decide), gpr_write_self]
  let a2 := a1.write .r6 (rev64 (a1.mem.readW (a1.gpr sb + a1.gpr .r0) 64))
  let a3 := a2.write .r0 (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot + 8))
  have e3 : a3.gpr sb + a3.gpr .r0 = blkA s + BitVec.ofNat 64 8 := by
    rw [N _ _ _ _ (by decide), gpr_write_self, N _ _ _ _ (by decide), N _ _ _ _ (by decide), VG.Offset.add_add]
  let a4 := a3.write .r7 (rev64 (a3.mem.readW (a3.gpr sb + a3.gpr .r0) 64))
  have a4k : KeyIn a4 := hk.of_eq ((N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans
    ((N _ _ _ _ (by decide)).trans (N _ _ _ _ (by decide))))) rfl rfl
  obtain ⟨b, be, b4, bg, bv, bm, brd, bwr, bsp, bsy⟩ := loadKey_run (w := 0) (by decide) (a4k 0 (by decide))
  let c := b.write .r6 (b.gpr .r6 ^^^ b.gpr .r4)
  have ck : KeyIn c := a4k.of_eq ((N _ _ _ _ (by decide)).trans (bg _ (by decide) (by decide))) brd bwr
  obtain ⟨d, de, d4, dg, dv, dm, drd, dwr, dsp, dsy⟩ := loadKey_run (w := 1) (by decide) (ck 1 (by decide))
  let t := d.write .r7 (d.gpr .r7 ^^^ d.gpr .r4)
  have a43 : a4.gpr .r3 = s.gpr .r3 :=
    (N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans ((N _ _ _ _ (by decide)).trans (N _ _ _ _ (by decide))))
  have kb : keyWord a4 0 = keyWord s 0 := keyWord_eq a43 rfl 0
  have kd : keyWord c 1 = keyWord s 1 :=
    keyWord_eq ((N _ _ _ _ (by decide)).trans ((bg _ (by decide) (by decide)).trans a43)) bm 1
  refine ⟨t, ?_, ?_, fun r h0 h4 h6 h7 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : loadBlock = [.li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot), .loadRev .d .r6 sb .r0,
        .li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot + 8), .loadRev .d .r7 sb .r0] ++
        (loadKey 0 ++ ([.logic .xor .r6 .r6 .r4] ++ (loadKey 1 ++ [.logic .xor .r7 .r7 .r4]))) := by
      simp [loadBlock]
    have h4 : runBlock isa [.li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot), .loadRev .d .r6 sb .r0,
        .li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot + 8), .loadRev .d .r7 sb .r0] s = some a4 := by
      rw [runBlock_cons, exec_li (by rw [tailSlot_val]; decide), runStep_some, runBlock_cons,
        exec_loadRev_d (by decide) (by rw [e1, ← BitVec.add_zero (blkA s)]; exact hb 0 (Or.inl rfl)),
        runStep_some, runBlock_cons, exec_li (by rw [tailSlot_val]; decide), runStep_some, runBlock_cons,
        exec_loadRev_d (by decide) (by rw [e3]; exact hb 8 (Or.inr rfl)), runStep_some, runBlock_nil]
    rw [e, VG.Interleave.runBlock_append, h4, Option.bind_some, VG.Interleave.runBlock_append, be,
      Option.bind_some, VG.Interleave.runBlock_append, runBlock_cons, exec_logic, runStep_some, runBlock_nil,
      Option.bind_some, VG.Interleave.runBlock_append, de, Option.bind_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil]
  · have g6 : t.gpr .r6 = (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s)) >>> 64).setWidth 64 ^^^
        keyWord s 0 := by
      rw [N _ _ _ _ (by decide), dg _ (by decide) (by decide), gpr_write_self, b4, kb, bg _ (by decide) (by decide),
        N _ _ _ _ (by decide), N _ _ _ _ (by decide), gpr_write_self, e1, dh.1]
      rfl
    have g7 : t.gpr .r7 = (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))).setWidth 64 ^^^
        keyWord s 1 := by
      rw [gpr_write_self, d4, kd, dg _ (by decide) (by decide), N _ _ _ _ (by decide),
        bg _ (by decide) (by decide), gpr_write_self, e3, dh.2]
      rfl
    show (t.gpr .r6, t.gpr .r7) = _
    rw [g6, g7]
  · rw [N _ _ _ _ h7, dg _ h0 h4, N _ _ _ _ h6, bg _ h0 h4, N _ _ _ _ h7, N _ _ _ _ h0, N _ _ _ _ h6, N _ _ _ _ h0]
  · rw [show t.vpr = d.vpr from rfl, dv, show c.vpr = b.vpr from rfl, bv]; rfl
  · rw [show t.mem = d.mem from rfl, dm, show c.mem = b.mem from rfl, bm]; rfl
  · rw [show t.rd = d.rd from rfl, drd, show c.rd = b.rd from rfl, brd]; rfl
  · rw [show t.wr = d.wr from rfl, dwr, show c.wr = b.wr from rfl, bwr]; rfl
  · rw [show t.sp = d.sp from rfl, dsp, show c.sp = b.sp from rfl, bsp]; rfl
  · rw [show t.syms = d.syms from rfl, dsy, show c.syms = b.syms from rfl, bsy]; rfl

theorem whitening_run {s : State} {w : Nat} (hw : w + 1 < 34) (hk : KeyIn s)
    (hb : ∀ d, d = 0 ∨ d = 8 → InRegions s.wr (blkA s + BitVec.ofNat 64 d) 8) :
    ∃ t, runBlock isa (whitening w) s = some t ∧
      Spec.Aes.bytesAt t.mem (blkA s) 16 =
        (Spec.Camellia.encodeBlock ((s.gpr .r7 ^^^ keyWord s w) ++ (s.gpr .r6 ^^^ keyWord s (w + 1)))).toList ∧
      Frame [⟨blkA s, 16⟩] s.mem t.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have N : ∀ (st : State) (q q' : Reg) (v : BitVec 64), q' ≠ q → (st.write q v).gpr q' = st.gpr q' :=
    fun st q q' v h => gpr_write_of_ne _ _ h
  obtain ⟨a, ae, a4, ag, av, am, ard, awr, asp, asy⟩ := loadKey_run (w := w) (by omega_using [hw]) (hk w (by omega_using [hw]))
  let b := a.write .r7 (a.gpr .r7 ^^^ a.gpr .r4)
  have b3 : b.gpr .r3 = s.gpr .r3 := (N _ _ _ _ (by decide)).trans (ag _ (by decide) (by decide))
  obtain ⟨c, ce, c4, cg, cv, cm, crd, cwr, csp, csy⟩ :=
    loadKey_run (w := w + 1) (by omega_using [hw]) ((hk.of_eq b3 ard awr) (w + 1) hw)
  let d := c.write .r6 (c.gpr .r6 ^^^ c.gpr .r4)
  let V7 := s.gpr .r7 ^^^ keyWord s w
  let V6 := s.gpr .r6 ^^^ keyWord s (w + 1)
  have d7 : d.gpr .r7 = V7 := by
    rw [N _ _ _ _ (by decide), cg _ (by decide) (by decide), gpr_write_self, a4, ag _ (by decide) (by decide)]
  have d6 : d.gpr .r6 = V6 := by
    rw [gpr_write_self, c4, cg _ (by decide) (by decide), N _ _ _ _ (by decide), ag _ (by decide) (by decide),
      keyWord_eq b3 am]
  have dsb : d.gpr sb = s.gpr sb := by
    rw [N _ _ _ _ (by decide), cg _ (by decide) (by decide), N _ _ _ _ (by decide), ag _ (by decide) (by decide)]
  have dwr : d.wr = s.wr := cwr.trans awr
  let e1 := d.write .r0 (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot))
  have x1 : e1.gpr sb + e1.gpr .r0 = blkA s := by rw [N _ _ _ _ (by decide), gpr_write_self, dsb]
  let m1 := e1.mem.writeW (e1.gpr sb + e1.gpr .r0) (rev64 (e1.gpr .r7))
  let e2 : State := { e1 with mem := m1 }
  let e3 := e2.write .r0 (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot + 8))
  have x3sb : e3.gpr sb = s.gpr sb :=
    (N e2 .r0 sb _ (by decide)).trans ((N d .r0 sb (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot))
      (by decide)).trans dsb)
  have x3 : e3.gpr sb + e3.gpr .r0 = blkA s + BitVec.ofNat 64 8 := by
    rw [x3sb, gpr_write_self, VG.Offset.add_add]
  have w1 : InRegions e1.wr (e1.gpr sb + e1.gpr .r0) 8 := by
    rw [x1, show e1.wr = s.wr from dwr, ← BitVec.add_zero (blkA s)]
    exact hb 0 (Or.inl rfl)
  have w3 : InRegions e3.wr (e3.gpr sb + e3.gpr .r0) 8 := by
    rw [x3, show e3.wr = s.wr from dwr]
    exact hb 8 (Or.inr rfl)
  let m2 := e3.mem.writeW (e3.gpr sb + e3.gpr .r0) (rev64 (e3.gpr .r6))
  let t : State := { e3 with mem := m2 }
  have mt : t.mem = (d.mem.writeW (blkA s) (rev64 V7)).writeW (blkA s + BitVec.ofNat 64 8) (rev64 V6) := by
    show m2 = _
    rw [show m2 = e3.mem.writeW (e3.gpr sb + e3.gpr .r0) (rev64 (e3.gpr .r6)) from rfl, x3,
      show e3.gpr .r6 = d.gpr .r6 from (N e2 .r0 .r6 _ (by decide)).trans
        (N d .r0 .r6 (BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot)) (by decide)), d6,
      show e3.mem = m1 from rfl, show m1 = e1.mem.writeW (e1.gpr sb + e1.gpr .r0) (rev64 (e1.gpr .r7)) from rfl, x1,
      show e1.gpr .r7 = d.gpr .r7 from N d .r0 .r7 _ (by decide), d7]
    rfl
  have sep : Region.Disjoint ⟨blkA s, 8⟩ ⟨blkA s + BitVec.ofNat 64 8, 8⟩ := by
    have h := VG.Offset.disjoint (s.gpr sb) (d := 8 * Impl.Camellia.PPC64LE.tailSlot) (n := 8)
      (e := 8 * Impl.Camellia.PPC64LE.tailSlot + 8) (k := 8) (Or.inl (by omega_using [])) (by rw [tailSlot_val]; decide)
      (by rw [tailSlot_val]; decide)
    rwa [← VG.Offset.add_add] at h
  refine ⟨t, ?_, ?_, ?_, fun r h0 h4 h6 h7 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : whitening w = loadKey w ++ ([.logic .xor .r7 .r7 .r4] ++ (loadKey (w + 1) ++
        ([.logic .xor .r6 .r6 .r4] ++ [.li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot), .storeRev .d .r7 sb .r0,
          .li .r0 (8 * Impl.Camellia.PPC64LE.tailSlot + 8), .storeRev .d .r6 sb .r0]))) := by
      simp [whitening]
    rw [e, VG.Interleave.runBlock_append, ae, Option.bind_some, VG.Interleave.runBlock_append, runBlock_cons,
      exec_logic, runStep_some, runBlock_nil, Option.bind_some, VG.Interleave.runBlock_append, ce,
      Option.bind_some, VG.Interleave.runBlock_append, runBlock_cons, exec_logic, runStep_some, runBlock_nil,
      Option.bind_some, runBlock_cons, exec_li (by rw [tailSlot_val]; decide), runStep_some, runBlock_cons,
      exec_storeRev_d (by decide) w1,
      runStep_some, runBlock_cons, exec_li (by rw [tailSlot_val]; decide), runStep_some, runBlock_cons,
      exec_storeRev_d (by decide) w3,
      runStep_some, runBlock_nil]
  · refine stored_bytes ?_ ?_
    · rw [mt, Mem.readW_writeW_sep (by exact sep) (by decide), Mem.readW_writeW_self64]
    · rw [mt, Mem.readW_writeW_self64]
  · rw [mt, show d.mem = s.mem from cm.trans am]
    refine Frame.trans (Proof.Camellia.frame_writeW _ (Region.sub_prefix (by decide : 8 ≤ 16)))
      (Proof.Camellia.frame_writeW _ ?_)
    have h := VG.Offset.sub_base (blkA s) (d := 8) (n := 8) (k := 16) (by decide)
    exact h
  · show e3.gpr r = s.gpr r
    rw [N _ _ _ _ h0]
    show e1.gpr r = s.gpr r
    rw [N _ _ _ _ h0, N _ _ _ _ h6, cg _ h0 h4, N _ _ _ _ h7, ag _ h0 h4]
  · show d.vpr = s.vpr
    rw [show d.vpr = c.vpr from rfl, cv, show b.vpr = a.vpr from rfl, av]
  · show d.rd = s.rd
    rw [show d.rd = c.rd from rfl, crd, show b.rd = a.rd from rfl, ard]
  · exact dwr
  · show d.sp = s.sp
    rw [show d.sp = c.sp from rfl, csp, show b.sp = a.sp from rfl, asp]
  · show d.syms = s.syms
    rw [show d.syms = c.syms from rfl, csy, show b.syms = a.syms from rfl, asy]

/-! ## The tables -/

/-- Table `k` as `lxvd2xTbl` loads it. -/
abbrev tval (k : Nat) : BitVec 128 := tableWords.getD (2 * k) 0 ++ tableWords.getD (2 * k + 1) 0

theorem tval_ok : ∀ k < 13, TabOk (tval k) (tables.getD k m0f) := by
  intro k hk; intro j hj; revert j; revert k; decide

theorem tval_mask : vdword (tval 13) 0 = 0x0f0f0f0f0f0f0f0f := by decide

theorem tableWords_length : tableWords.length = 28 := rfl

theorem treg_inj : ∀ a < 14, ∀ b < 14, treg a = treg b → a = b := by decide

/-- After loading the tables `0 … n - 1`. -/
theorem loadT_run (s : State) (n : Nat) (hn : n ≤ 14) (h10 : s.gpr .r10 = s.syms tableSym) :
    ∃ t, runBlock isa ((List.range n).flatMap fun k =>
        [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) s = some t ∧
      (∀ k < n, t.vpr (treg k) = tval k) ∧
      (∀ v, (∀ k < n, v ≠ treg k) → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, av, avo, ag, am, ard, awr, asp, asy⟩ := ih (by omega_using [hn])
    let b := a.write .r11 (BitVec.ofNat 64 (16 * n))
    let c := b.writeV (treg n) (tval n)
    have hb10 : b.gpr .r10 = b.syms tableSym := by
      rw [show b.syms = s.syms from asy, gpr_write_of_ne _ _ (by decide), ag _ (by decide), h10]
    have hb11 : (b.gpr .r11).toNat = 16 * n := by
      rw [gpr_write_self, BitVec.toNat_ofNat]; omega_using [hn]
    have hc : exec (.lxvd2xTbl (treg n) .r10 .r11 tableSym tableWords) b = some c := by
      have e1 : 16 * n / 8 = 2 * n := by omega_using []
      have e2 : 16 * n % 8 = 0 := by omega_using []
      have e3 : 2 * n + 2 ≤ 28 := by omega_using [hn]
      have e4 : (Reg.r10 ≠ .r0) := by decide
      simp only [exec, hb10, hb11, e1, e2, e3, e4, tableWords_length, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte]
      rfl
    refine ⟨c, ?_, fun k hk => ?_, fun v hv => ?_, fun r hr => ?_, am, ard, awr, asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons, exec_li (by omega_using [hn]), runStep_some,
        runBlock_cons, hc, runStep_some, runBlock_nil]
    · rw [vpr_writeV]
      by_cases e : k = n
      · subst e; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd (treg_inj k (by omega_using [hn, hk]) n (by omega_using [hn]) h) e)]
        exact av k (by omega_using [hk, e])
    · rw [vpr_writeV, ite_eq_right_iff.mpr (fun h => absurd h (hv n (by omega_using [])))]
      exact avo v fun k hk => hv k (by omega_using [hk])
    · exact (gpr_write_of_ne _ _ hr).trans (ag r hr)

theorem loadTables_run (s : State) :
    ∃ t, runBlock isa loadTables s = some t ∧ Consts t ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a : State := { s.write .r10 (s.syms tableSym) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) }
  have a10 : a.gpr .r10 = a.syms tableSym := by
    show (s.write .r10 (s.syms tableSym)).gpr .r10 = s.syms tableSym; exact gpr_write_self _ _ _
  obtain ⟨b, be, bv, _, bg, bm, brd, bwr, bsp, bsy⟩ := loadT_run a 14 (by decide) a10
  let c := b.write .r12 (vdword (b.vpr .v0) 0)
  refine ⟨c, ?_, ⟨fun k hk => ?_, ?_⟩, fun r h10 h11 h12 => ?_, bm, brd, bwr, bsp, bsy⟩
  · rw [loadTables, List.cons_append, runBlock_cons]
    simp only [exec, ne_eq, show ¬(Reg.r10 = .r0) by decide, not_false_eq_true, ↓reduceIte]
    rw [runStep_some, VG.Interleave.runBlock_append, be, Option.bind_some, runBlock_cons, exec_mfvsrd, runStep_some,
      runBlock_nil]
  · rw [show c.vpr (treg k) = b.vpr (treg k) from rfl, bv k (by omega_using [hk])]; exact tval_ok k hk
  · rw [gpr_write_self, show b.vpr .v0 = b.vpr (treg 13) from rfl, bv 13 (by decide), tval_mask]
  · rw [gpr_write_of_ne _ _ h12, bg r h11]; exact gpr_write_of_ne _ _ h10

theorem flPair_run {s : State} {w : Nat} (hw : w + 1 < 34) (hc : Consts s) (hk : KeyIn s) :
    ∃ t, runBlock isa (flPair w) s = some t ∧
      halves t = (Spec.Camellia.fl (halves s).1 (keyWord s w), Spec.Camellia.flinv (halves s).2 (keyWord s (w + 1))) ∧
      (∀ r, r ∉ rWrites → t.gpr r = s.gpr r) ∧ Consts t ∧ t.vpr = s.vpr ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, a6, ag, av, am, ard, awr, asp, asy⟩ := fl_run (Or.inl rfl) false (by omega_using [hw]) (hk w (by omega_using [hw]))
  have a3 : a.gpr .r3 = s.gpr .r3 := ag _ (by decide) (by decide)
  obtain ⟨b, be, b7, bg, bv, bm, brd, bwr, bsp, bsy⟩ :=
    fl_run (Or.inr rfl) true (by omega_using [hw]) ((hk.of_eq a3 ard awr) (w + 1) hw)
  have frame : ∀ r, r ∉ rWrites → b.gpr r = s.gpr r := fun r hr => by
    have h : r ∉ fWrites ∧ r ≠ .r6 ∧ r ≠ .r7 := by
      simp only [rWrites, fWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨⟨hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2⟩, hr.2.2.1, hr.2.2.2.1⟩
    rw [bg r h.1 h.2.2, ag r h.1 h.2.1]
  refine ⟨b, ?_, ?_, frame, hc.of_eq (fun v _ => by rw [bv, av]) (frame _ (by decide)), by rw [bv, av],
    bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp, bsy.trans asy⟩
  · rw [flPair, VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · have b6 : b.gpr .r6 = a.gpr .r6 := bg _ (by decide) (by decide)
    have a7 : a.gpr .r7 = s.gpr .r7 := ag _ (by decide) (by decide)
    show (b.gpr .r6, b.gpr .r7) = _
    rw [b6, a6, b7, a7, keyWord_eq a3 am]
    rfl

theorem group_fl (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) {i : Nat} (h : i + 1 < g) :
    Proof.Camellia.group g E d i =
      let d := Proof.Camellia.pair (E (6 + 8 * i)) (E (7 + 8 * i)) (Proof.Camellia.pair (E (4 + 8 * i)) (E (5 + 8 * i))
        (Proof.Camellia.pair (E (2 + 8 * i)) (E (3 + 8 * i)) d))
      (Spec.Camellia.fl d.1 (E (8 + 8 * i)), Spec.Camellia.flinv d.2 (E (9 + 8 * i))) := by
  simp only [Proof.Camellia.group, h, ite_true]

theorem group_last (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) {i : Nat} (h : ¬ i + 1 < g) :
    Proof.Camellia.group g E d i =
      Proof.Camellia.pair (E (6 + 8 * i)) (E (7 + 8 * i)) (Proof.Camellia.pair (E (4 + 8 * i)) (E (5 + 8 * i))
        (Proof.Camellia.pair (E (2 + 8 * i)) (E (3 + 8 * i)) d)) := by
  simp only [Proof.Camellia.group, h, ite_false]

theorem groups3 (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    Proof.Camellia.groups 3 E d =
      Proof.Camellia.group 3 E (Proof.Camellia.group 3 E (Proof.Camellia.group 3 E d 0) 1) 2 := by
  simp [Proof.Camellia.groups, List.range_succ]

theorem groups4 (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    Proof.Camellia.groups 4 E d = Proof.Camellia.group 4 E
      (Proof.Camellia.group 4 E (Proof.Camellia.group 4 E (Proof.Camellia.group 4 E d 0) 1) 2) 3 := by
  simp [Proof.Camellia.groups, List.range_succ]

/-- The invariant the rounds keep. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ rWrites → t.gpr r = s.gpr r
  consts : Consts t
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.consts, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp, h'.syms.trans h.syms⟩

theorem Keeps.r3 {s t : State} (h : Keeps s t) : t.gpr .r3 = s.gpr .r3 := h.gpr _ (by decide)

theorem Keeps.keyIn {s t : State} (h : Keeps s t) (hk : KeyIn s) : KeyIn t := hk.of_eq h.r3 h.rd h.wr

theorem Keeps.key {s t : State} (h : Keeps s t) (w : Nat) : keyWord t w = keyWord s w := keyWord_eq h.r3 h.mem w

/-- Group `i` of six rounds and FL, FLINV. -/
theorem groupFl_run {s : State} (g i : Nat) (hi : i + 1 < g) (hw : 8 * i + 10 ≤ 34) (hc : Consts s) (hk : KeyIn s) :
    ∃ t, runBlock isa (six (2 + 8 * i) ++ flPair (8 + 8 * i)) s = some t ∧
      halves t = Proof.Camellia.group g (keyWord s) (halves s) i ∧ Keeps s t := by
  obtain ⟨a, ae, ah, ag, ac, _, am, ard, awr, asp, asy⟩ := six_run (w := 2 + 8 * i) (by omega_using [hw]) hc hk
  have ka : Keeps s a := ⟨ag, ac, am, ard, awr, asp, asy⟩
  obtain ⟨b, be, bh, bg, bc, _, bm, brd, bwr, bsp, bsy⟩ := flPair_run (w := 8 + 8 * i) (by omega_using [hw]) ac (ka.keyIn hk)
  have kb : Keeps a b := ⟨bg, bc, bm, brd, bwr, bsp, bsy⟩
  refine ⟨b, ?_, ?_, ka.trans kb⟩
  · rw [VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · rw [bh, ah, group_fl _ _ _ hi, ka.key, ka.key, show 8 + 8 * i + 1 = 9 + 8 * i by omega_using [],
      show 2 + 8 * i + 1 = 3 + 8 * i by omega_using [], show 2 + 8 * i + 2 = 4 + 8 * i by omega_using [],
      show 2 + 8 * i + 3 = 5 + 8 * i by omega_using [], show 2 + 8 * i + 4 = 6 + 8 * i by omega_using [],
      show 2 + 8 * i + 5 = 7 + 8 * i by omega_using []]

/-- The last group of six rounds. -/
theorem groupLast_run {s : State} (g i : Nat) (hi : ¬ i + 1 < g) (hw : 8 * i + 8 ≤ 34) (hc : Consts s)
    (hk : KeyIn s) :
    ∃ t, runBlock isa (six (2 + 8 * i)) s = some t ∧
      halves t = Proof.Camellia.group g (keyWord s) (halves s) i ∧ Keeps s t := by
  obtain ⟨a, ae, ah, ag, ac, _, am, ard, awr, asp, asy⟩ := six_run (w := 2 + 8 * i) (by omega_using [hw]) hc hk
  refine ⟨a, ae, ?_, ⟨ag, ac, am, ard, awr, asp, asy⟩⟩
  rw [ah, group_last _ _ _ hi, show 2 + 8 * i + 1 = 3 + 8 * i by omega_using [], show 2 + 8 * i + 2 = 4 + 8 * i by omega_using [],
    show 2 + 8 * i + 3 = 5 + 8 * i by omega_using [], show 2 + 8 * i + 4 = 6 + 8 * i by omega_using [],
    show 2 + 8 * i + 5 = 7 + 8 * i by omega_using []]

/-! ## The block's rounds -/

/-- The prewhitened halves of the block. -/
def start (s : State) : BitVec 64 × BitVec 64 :=
  ((Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s)) >>> 64).setWidth 64 ^^^ keyWord s 0,
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))).setWidth 64 ^^^ keyWord s 1)

theorem prefix_run {s : State} (g : Nat) (hg : 2 < g) (hk : KeyIn s)
    (hb : ∀ d, d = 0 ∨ d = 8 → InRegions (s.rd ++ s.wr) (blkA s + BitVec.ofNat 64 d) 8) :
    ∃ t, runBlock isa (loadTables ++ loadBlock ++ prefixRounds ++ ([.subi .r9 .r28 18] : List Instr)) s = some t ∧
      halves t = Proof.Camellia.group 3 (keyWord s)
        (Proof.Camellia.group g (keyWord s) (Proof.Camellia.group g (keyWord s) (start s) 0) 1) 2 ∧
      t.gpr .r9 = s.gpr .r28 - BitVec.ofNat 64 18 ∧
      (∀ r, r ∉ rWrites → r ≠ .r12 → t.gpr r = s.gpr r) ∧ Consts t ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ac, ag, am, ard, awr, asp, asy⟩ := loadTables_run s
  have a3 : a.gpr .r3 = s.gpr .r3 := ag _ (by decide) (by decide) (by decide)
  have ab : blkA a = blkA s := by rw [blkA, blkA, ag _ (by decide) (by decide) (by decide)]
  obtain ⟨b, be, bh, bg, bv, bm, brd, bwr, bsp, bsy⟩ := loadBlock_run (hk.of_eq a3 ard awr)
    (fun d hd => by rw [ab, ard, awr]; exact hb d hd)
  have bc : Consts b := ac.of_eq (fun v _ => by rw [bv]) (bg _ (by decide) (by decide) (by decide) (by decide))
  have b3 : b.gpr .r3 = s.gpr .r3 := (bg _ (by decide) (by decide) (by decide) (by decide)).trans a3
  have bk : KeyIn b := hk.of_eq b3 (brd.trans ard) (bwr.trans awr)
  have bkey : ∀ w, keyWord b w = keyWord s w := keyWord_eq b3 (bm.trans am)
  obtain ⟨c, ce, ch, kc⟩ := groupFl_run (s := b) g 0 (by omega_using [hg]) (by omega_using []) bc bk
  obtain ⟨d, de, dh, kd⟩ := groupFl_run (s := c) g 1 (by omega_using [hg]) (by omega_using []) kc.consts (kc.keyIn bk)
  obtain ⟨e, ee, eh, ke⟩ := groupLast_run (s := d) 3 2 (by omega_using []) (by omega_using []) kd.consts (kd.keyIn (kc.keyIn bk))
  let t := e.write .r9 (e.gpr .r28 - BitVec.ofNat 64 18)
  have kbe := (kc.trans kd).trans ke
  have e28 : e.gpr .r28 = s.gpr .r28 := by
    rw [kbe.gpr _ (by decide), bg _ (by decide) (by decide) (by decide) (by decide),
      ag _ (by decide) (by decide) (by decide)]
  refine ⟨t, ?_, ?_, ?_, fun r hr h12 => ?_, kbe.consts.of_eq (fun _ _ => rfl) (gpr_write_of_ne _ _ (by decide)),
    kbe.mem.trans (bm.trans am), kbe.rd.trans (brd.trans ard), kbe.wr.trans (bwr.trans awr),
    kbe.sp.trans (bsp.trans asp), kbe.syms.trans (bsy.trans asy)⟩
  · have hp : prefixRounds = (six (2 + 8 * 0) ++ flPair (8 + 8 * 0)) ++ ((six (2 + 8 * 1) ++ flPair (8 + 8 * 1)) ++
        six (2 + 8 * 2)) := by simp [prefixRounds]
    rw [VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, ae,
      Option.bind_some, be, Option.bind_some, hp, VG.Interleave.runBlock_append, ce, Option.bind_some,
      VG.Interleave.runBlock_append, de, Option.bind_some, ee, Option.bind_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · have ke' : ∀ w, keyWord d w = keyWord s w := fun w => ((kc.trans kd).key w).trans (bkey w)
    have kc' : ∀ w, keyWord c w = keyWord s w := fun w => (kc.key w).trans (bkey w)
    show (e.gpr .r6, e.gpr .r7) = _
    have hb' : halves b = start s := by
      rw [bh, am, ab, keyWord_eq a3 am, keyWord_eq a3 am, start]
    have f1 : keyWord d = keyWord s := funext ke'
    have f2 : keyWord c = keyWord s := funext kc'
    have f3 : keyWord b = keyWord s := funext bkey
    rw [show (e.gpr .r6, e.gpr .r7) = halves e from rfl, eh, dh, ch, hb', f1, f2, f3]
  · rw [gpr_write_self, e28]
  · have h9 : r ≠ .r9 := fun h => hr (by simp [rWrites, h])
    rw [gpr_write_of_ne _ _ h9, kbe.gpr r hr]
    have h0 : r ≠ .r0 := fun h => hr (by simp [rWrites, h])
    have h4 : r ≠ .r4 := fun h => hr (by simp [rWrites, h])
    have h6 : r ≠ .r6 := fun h => hr (by simp [rWrites, h])
    have h7 : r ≠ .r7 := fun h => hr (by simp [rWrites, h])
    have h10 : r ≠ .r10 := fun h => hr (by simp [rWrites, h])
    have h11 : r ≠ .r11 := fun h => hr (by simp [rWrites, h])
    rw [bg r h0 h4 h6 h7, ag r h10 h11 h12]

/-! ## The core -/

open VG.Proof.Modes.PPC64LE (ScrIn coreRegion blkRegion blkAddr CoreSpec kept KeptBut)

/-- The key is ready: the number of rounds in `r28` and the schedule at `r3`,
apart from the core's slots and the regions `ws`. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  Proof.Camellia.PPC64LE.Mode.KeyArgs s (coreRegion core B :: ws) k

theorem slots_val : Impl.Camellia.PPC64LE.slots = 414 := rfl

theorem kept_ne : ∀ r ∈ kept, r ∉ rWrites ∧ r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 := by decide

theorem group4_2 (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    Proof.Camellia.group 4 E d 2 =
      (Spec.Camellia.fl (Proof.Camellia.group 3 E d 2).1 (E 24),
        Spec.Camellia.flinv (Proof.Camellia.group 3 E d 2).2 (E 25)) := by
  simp [Proof.Camellia.group]

theorem cipher_words {s : State} {k : Nat × List (BitVec 64)} {p : Addr} (hp : s.gpr .r3 = p)
    (hR : k.1 = 18 ∨ k.1 = 24) (hws : k.2 = Proof.Camellia.schedWords s.mem p k.1) (A : Addr) :
    Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2) (Spec.Aes.bytesAt s.mem A 16) =
      (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (k.1 / 6) (keyWord s)
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem A)))).toList := by
  rw [Proof.Camellia.cipher_bytes hR]
  apply congrArg (fun x : BitVec 128 => (Spec.Camellia.encodeBlock x).toList)
  refine Proof.Camellia.Serial.cryptWords_congr _ (by rcases hR with h | h <;> simp [h]) _ _ _ fun i hi => ?_
  rw [hws, Proof.Camellia.schedWords_getD _ _ (by rcases hR with h | h <;> simp [h, Spec.Camellia.scheduleLength] at hi ⊢ <;> omega_using [hi]),
    keyWord, hp]

/-- The registers `crypt` writes. -/
def cWrites : List Reg := [.r0, .r4, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem cWrites_ne : ∀ r : Reg, r ∉ cWrites →
    r ∉ rWrites ∧ r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 := by
  intro r; cases r <;> decide

theorem kept_cWrites : ∀ r ∈ kept, r ∉ cWrites := by decide

/-- `crypt` with the schedule's words at `r3`, wherever they are: the block
enciphered with them (`cryptWords`). -/
theorem crypt_run {s : State} {B : Addr} {R : Nat} (hB : s.gpr sb = B) (hs : ScrIn s B core.total)
    (keyIn : KeyIn s) (h28 : s.gpr .r28 = BitVec.ofNat 64 R) (hR : R = 18 ∨ R = 24) :
    WP isa crypt s fun u => (∀ r, r ∉ cWrites → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Frame [⟨blkA s, 16⟩] s.mem u.mem ∧
      Spec.Aes.bytesAt u.mem (blkA s) 16 =
        (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6) (keyWord s)
          (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))))).toList := by
  have hwr : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region) ∈ s.wr := hs.wr
  have hfB : B.toNat + 8 * (Impl.Camellia.PPC64LE.slots + 8) ≤ 2 ^ 64 := hs.fit
  have blkA_eq : blkA s = B + BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot) := by rw [blkA, hB]
  have hbw : ∀ d, d = 0 ∨ d = 8 → InRegions s.wr (blkA s + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [blkA_eq, VG.Offset.add_add]
    exact ⟨_, hwr, VG.Offset.contains_base B (by rw [tailSlot_val, slots_val]; omega_using [hd])
      (by rw [tailSlot_val]; omega_using [hd])⟩
  have hbr : ∀ d, d = 0 ∨ d = 8 → InRegions (s.rd ++ s.wr) (blkA s + BitVec.ofNat 64 d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hbw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hg : 2 < R / 6 := by rcases hR with h | h <;> rw [h] <;> decide
  obtain ⟨t, te, th, t9, tg, tc, tm, trd, twr, tsp, tsy⟩ := prefix_run (R / 6) hg keyIn hbr
  have tsb : t.gpr sb = s.gpr sb := tg _ (by decide) (by decide)
  have t3 : t.gpr .r3 = s.gpr .r3 := tg _ (by decide) (by decide)
  have tk : KeyIn t := keyIn.of_eq t3 trd twr
  have tkey : keyWord t = keyWord s := funext (keyWord_eq t3 tm)
  have tb : blkA t = blkA s := by rw [blkA, blkA, tsb]
  have tbw : ∀ d, d = 0 ∨ d = 8 → InRegions t.wr (blkA t + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [tb, twr]; exact hbw d hd
  change WP isa (.seq (.block _) (.ite _ _ _)) s _
  refine VG.WP.seq (WP.of_runBlock ⟨t, te, ?_⟩)
  have t9' : t.gpr .r9 = BitVec.ofNat 64 (R - 18) := by
    rw [t9, h28]; rcases hR with h | h <;> rw [h] <;> rfl
  refine VG.WP.ite (decide (R - 18 = 0)) (eval_zero_ofNat t .r9 (by rcases hR with h | h <;> rw [h] <;> decide) t9')
    (fun h18 => ?_) (fun h24 => ?_)
  · have e18 : R = 18 := by rcases hR with h | h <;> simp [h] at h18 ⊢
    obtain ⟨u, ue, ub, uf, ug, _, urd, uwr, _, _⟩ := whitening_run (w := 24) (by decide) tk tbw
    refine WP.of_runBlock ⟨u, ue, fun r hr => ?_, urd.trans trd, uwr.trans twr, ?_, ?_⟩
    · have h := cWrites_ne r hr
      rw [ug r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2, tg r h.1 h.2.1]
    · rw [← tm, ← tb]; exact uf
    · have cw : Proof.Camellia.cryptWords 3 (keyWord s) (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))) =
          ((Proof.Camellia.groups 3 (keyWord s) (start s)).2 ^^^ keyWord s 24) ++
            ((Proof.Camellia.groups 3 (keyWord s) (start s)).1 ^^^ keyWord s 25) := rfl
      have hh : halves t = _ := th
      rw [e18, show (18 : Nat) / 6 = 3 from rfl] at hh
      rw [e18, show (18 : Nat) / 6 = 3 from rfl, cw, groups3, ← hh, ← tb, ub, tkey]
      rfl
  · have e24 : R = 24 := by rcases hR with h | h <;> simp [h] at h24 ⊢
    obtain ⟨x, xe, xh, xg, xc, _, xm, xrd, xwr, xsp, xsy⟩ := flPair_run (w := 24) (by decide) tc tk
    have kx : Keeps t x := ⟨xg, xc, xm, xrd, xwr, xsp, xsy⟩
    obtain ⟨y, ye, yh, ky⟩ := groupLast_run (s := x) 4 3 (by decide) (by decide) xc (kx.keyIn tk)
    have kxy := kx.trans ky
    have yb : blkA y = blkA t := by rw [blkA, blkA, kxy.gpr _ (by decide)]
    obtain ⟨u, ue, ub, uf, ug, _, urd, uwr, _, _⟩ := whitening_run (s := y) (w := 32) (by decide) (kxy.keyIn tk)
      (fun d hd => by rw [yb, kxy.wr]; exact tbw d hd)
    have ye' : runBlock isa (six 26) x = some y := ye
    refine WP.of_runBlock ⟨u, ?_, fun r hr => ?_, urd.trans (kxy.rd.trans trd), uwr.trans (kxy.wr.trans twr),
      ?_, ?_⟩
    · rw [VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, xe, Option.bind_some, ye', Option.bind_some,
        ue]
    · have h := cWrites_ne r hr
      rw [ug r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2, kxy.gpr r h.1, tg r h.1 h.2.1]
    · rw [← tm, ← kxy.mem, ← tb, ← yb]; exact uf
    · have cw : Proof.Camellia.cryptWords 4 (keyWord s) (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (blkA s))) =
          ((Proof.Camellia.groups 4 (keyWord s) (start s)).2 ^^^ keyWord s 32) ++
            ((Proof.Camellia.groups 4 (keyWord s) (start s)).1 ^^^ keyWord s 33) := rfl
      have hh : halves t = _ := th
      rw [e24, show (24 : Nat) / 6 = 4 from rfl] at hh
      have xkey : keyWord x = keyWord s := funext fun w => (kx.key w).trans (congrFun tkey w)
      have ykey : keyWord y = keyWord s := funext fun w => (kxy.key w).trans (congrFun tkey w)
      rw [tkey] at xh
      rw [xkey] at yh
      rw [e24, show (24 : Nat) / 6 = 4 from rfl, cw, groups4, group4_2, ← hh, ← xh, ← yh,
        ← tb, ← yb, ub, ykey]
      rfl

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B core.total) (hk : Ready s B ws k) :
    WP isa core.crypt s fun t => t.gpr sb = B ∧ (∀ r ∈ kept, t.gpr r = s.gpr r) ∧ Ready t B ws k ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt t.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hk' := hk
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, -⟩ := hk'
  have keyIn : KeyIn s := fun i hi => by
    rw [hp]; exact ⟨_, List.mem_append_left _ hin, VG.Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])⟩
  have hblk : blkAddr core B 0 = blkA s := by
    rw [blkA, hB]; show B + BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot) + BitVec.ofNat 64 (4 * 4 * 0) = _
    rw [VG.Offset.add_add, Nat.mul_zero, Nat.add_zero]
  have hsub : Region.Sub ⟨blkA s, 16⟩ (coreRegion core B) := by
    rw [blkA, hB]
    exact VG.Offset.sub_base B (by show 8 * Impl.Camellia.PPC64LE.tailSlot + 16 ≤ 8 * Impl.Camellia.PPC64LE.slots
                                   rw [tailSlot_val, slots_val]; omega_using [])
  refine WP.mono (crypt_run hB hs keyIn h28 hR) fun u ⟨ug, urd, uwr, uf, ub⟩ => ?_
  have uk : ∀ r ∈ kept, u.gpr r = s.gpr r := fun r hr => ug r (kept_cWrites r hr)
  have fc : Frame [coreRegion core B] s.mem u.mem := uf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, hsub⟩
  refine ⟨(ug _ (by decide)).trans hB, uk, ?_, fc, fun j hj => ?_, urd, uwr⟩
  · refine Proof.Camellia.PPC64LE.Mode.keyArgs_congr hk (fun r hr _ _ _ => uk r hr) urd
      (fc.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · have hj0 : j = 0 := by have : j < 1 := hj; omega_using [this]
    subst hj0
    show Spec.Aes.bytesAt u.mem (blkAddr core B 0) 16 =
      Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2) (Spec.Aes.bytesAt s.mem (blkAddr core B 0) 16)
    rw [hblk, ub, cipher_words hp hR hws]

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hR : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : Proof.Camellia.PPC64LE.Mode.KeyArgs s rs k) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion core B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.of_runBlock ⟨s, rfl, ?_, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  obtain ⟨p, hp, h28, hRo, hws, hin, hfit, hdis⟩ := hk
  refine ⟨p, hp, h28, hRo, hws, hin, hfit, fun r hr => ?_⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (hdis _ hR).sub_right (Region.sub_prefix (by show 8 * Impl.Camellia.PPC64LE.slots ≤ 8 * (Impl.Camellia.PPC64LE.slots + 8); omega_using []))
  · exact hdis r hr

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready s B ws k) (hk : KeptBut s s') (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) :
    Ready s' B ws k := by
  refine Proof.Camellia.PPC64LE.Mode.keyArgs_congr h hk hrd (hf.sub fun r hr => ?_)
  rcases hd r hr with _ | h'
  · obtain ⟨r', hr', hs'⟩ := hsub r hr
    exact ⟨r', List.mem_cons_of_mem _ hr', hs'⟩
  · have hb : Region.Sub (blkRegion core B) (coreRegion core B) :=
      VG.Offset.sub_base B (by show 8 * Impl.Camellia.PPC64LE.tailSlot + 4 * 4 * 1 ≤ 8 * Impl.Camellia.PPC64LE.slots
                               rw [tailSlot_val, slots_val]; omega_using [])
    exact ⟨_, List.mem_cons_self, fun x hx => hb x (h' x hx)⟩

/-- The single-block core meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := Proof.Camellia.PPC64LE.Mode.KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Camellia.cipher, core]
  layout := ⟨by decide, .inr rfl, by decide, by decide, by decide⟩
  keyArgs_congr h e r _ _ f := Proof.Camellia.PPC64LE.Mode.keyArgs_congr h e r f
  ready_frame h e r _ _ f hs hd := ready_frame h e r f hs hd
  prepare_wp hB _ hR hk := prepare_wp hB hR hk
  crypt_wp hB hs hk := crypt_wp hB hs hk

/-! ## Decryption

`decCore` copies the schedule's words in decryption's order to the scratch
buffer's first slots (`copy_run`, `decPrepare_wp`), and runs `crypt` on the
copy (`decCrypt_wp`, by `crypt_run`), `r3` kept in `keepSlot` meanwhile. -/

theorem decIdx_eq : decIdx = Proof.Camellia.decPerm := rfl

theorem decIdx_lt (g : Nat) (hg : g = 3 ∨ g = 4) : ∀ i < 8 * g + 2, decIdx g i < 8 * g + 2 := by
  rcases hg with rfl | rfl <;> decide

/-- Decryption on a block in memory: `cryptWords` on the words in `decPerm`'s order. -/
theorem invCipher_bytes {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : Mem) (p : Addr) :
    Spec.Camellia.invCipher (Spec.Camellia.subkeysOfWords R ws) (Spec.Aes.bytesAt m p 16) =
      (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6)
        (fun i => ws.getD (Proof.Camellia.decPerm (R / 6) i) 0)
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)))).toList := by
  rw [Spec.Camellia.invCipher, Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.ofFn_toList,
    Spec.Camellia.decryptBlock, Proof.Camellia.decryptWith_eq hR]

/-- The decryption core's key is ready: as `Ready`, and the words in
decryption's order at the scratch buffer's first slots. -/
def DecReady (s : State) (B : Addr) (ws : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  Ready s B ws k ∧ ∀ i < 8 * (k.1 / 6) + 2,
    Spec.Camellia.wordAt s.mem (B + BitVec.ofNat 64 (8 * i)) = k.2.getD (Proof.Camellia.decPerm (k.1 / 6) i) 0

/-- The copy's first `n` words. -/
theorem copy_run {s : State} {g : Nat} (hg : g = 3 ∨ g = 4) {p B : Addr} (hp : s.gpr .r3 = p)
    (hB : s.gpr sb = B) (hin : (⟨p, 272⟩ : Region) ∈ s.rd)
    (hwr : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩) :
    ∀ n ≤ 8 * g + 2, ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        ([.load .d .r4 .r3 (8 * decIdx g i), .store .d .r4 sb (8 * i)] : List Instr)) s = some t ∧
      (∀ r, r ≠ .r4 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B, 8 * n⟩] s.mem t.mem ∧
      ∀ i < n, t.mem.readW (B + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * decIdx g i)) 64 := by
  have hsl := slots_val
  have hg34 : 8 * g + 2 ≤ 34 := by rcases hg with rfl | rfl <;> decide
  intro n
  induction n with
  | zero => intro _; exact ⟨s, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨t, te, tg, trd, twr, tf, tr⟩ := ih (by omega_using [hn])
    have hdn : decIdx g n < 8 * g + 2 := decIdx_lt g hg n (by omega_using [hn])
    have t3 : t.gpr .r3 = p := (tg _ (by decide)).trans hp
    have tB : t.gpr sb = B := (tg _ (by decide)).trans hB
    have hsrc : (⟨p, 272⟩ : Region).Contains (p + BitVec.ofNat 64 (8 * decIdx g n)) 8 :=
      VG.Offset.contains_base p (by omega_using [hg, hdn]) (by omega_using [hg, hdn])
    have hdst : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region).Contains (B + BitVec.ofNat 64 (8 * n)) 8 :=
      VG.Offset.contains_base B (by rw [hsl]; omega_using [hg, hn]) (by omega_using [hg, hn])
    have hl : InRegions (t.rd ++ t.wr) (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 8 := by
      rw [t3, trd]; exact ⟨_, List.mem_append_left _ hin, hsrc⟩
    have tdis : ∀ r' ∈ [(⟨B, 8 * n⟩ : Region)], Region.Disjoint ⟨p, 272⟩ r' := fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hd.sub_right (Region.sub_prefix (by rw [hsl]; omega_using [hg, hn]))
    have tv : t.mem.readW (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * decIdx g n)) 64 := by
      rw [t3]; exact tf.readW hsrc tdis (by decide)
    have hs : InRegions (t.write .r4 (t.mem.readW (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 64)).wr
        ((t.write .r4 (t.mem.readW (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 64)).gpr sb +
          BitVec.ofNat 64 (8 * n)) 8 := by
      rw [gpr_write_of_ne _ _ (by decide), tB]; exact ⟨_, twr ▸ hwr, hdst⟩
    refine ⟨{ t.write .r4 (t.mem.readW (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 64) with
        mem := t.mem.writeW (B + BitVec.ofNat 64 (8 * n)) (t.mem.readW (t.gpr .r3 + BitVec.ofNat 64 (8 * decIdx g n)) 64) },
      ?_, fun r hr => ?_, trd, twr, ?_, fun i hi => ?_⟩
    · rw [List.range_succ, List.flatMap_append, VG.Interleave.runBlock_append, te, Option.bind_some,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, runBlock_cons,
        exec_load_d (by decide) ⟨by omega_using [hg, hdn], by omega_using []⟩ hl, runStep_some, runBlock_cons,
        exec_store_d (by decide) ⟨by omega_using [hg, hn], by omega_using []⟩ hs, runStep_some, runBlock_nil,
        gpr_write_of_ne _ _ (by decide), tB, gpr_write_self]
      rfl
    · exact (gpr_write_of_ne _ _ hr).trans (tg r hr)
    · refine (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (VG.Offset.contains_base B (by omega_using []) (by omega_using [hg, hn]))
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])
    · show (t.mem.writeW _ _).readW _ 64 = _
      by_cases hin' : i < n
      · rw [Mem.readW_writeW_sep (VG.Offset.sep B (.inl (by omega_using [hin'])) (by omega_using [hg, hn, hi]) (by omega_using [hg, hn])) (by decide)]
        exact tr i hin'
      · obtain rfl : i = n := by omega_using [hi, hin']
        rw [Mem.readW_writeW_self64, tv]

theorem kept_r4_r9 : ∀ r ∈ kept, r ≠ .r4 ∧ r ≠ .r9 := by decide

theorem decPrepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B decCore.total) (hR' : (⟨B, 8 * decCore.total⟩ : Region) ∈ rs)
    (hk : Proof.Camellia.PPC64LE.Mode.KeyArgs s rs k) :
    WP isa decCore.prepare s fun s' => DecReady s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion decCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk0 := hk
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, hdis⟩ := hk0
  have hsl := slots_val
  have hwr : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region) ∈ s.wr := hs.wr
  have hd : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ := hdis _ hR'
  have hkc : Proof.Camellia.PPC64LE.Mode.KeyArgs s (coreRegion core B :: rs) k := by
    refine ⟨p, hp, h28, hR, hws, hin, hfit, fun r hr => ?_⟩
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hd.sub_right (Region.sub_prefix (by show 8 * Impl.Camellia.PPC64LE.slots ≤ 8 * (Impl.Camellia.PPC64LE.slots + 8); omega_using []))
    · exact hdis r hr
  have fin : ∀ g, g = 3 ∨ g = 4 → k.1 / 6 = g →
      WP isa (.block (copyWords g)) (s.write .r9 (s.gpr .r28 - BitVec.ofNat 64 18)) fun s' =>
        DecReady s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        Frame [coreRegion decCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro g hg hkg
    have hg34 : 8 * g + 2 ≤ 34 := by rcases hg with rfl | rfl <;> decide
    obtain ⟨t, te, tg, trd, twr, tf, tr⟩ := copy_run (s := s.write .r9 (s.gpr .r28 - BitVec.ofNat 64 18)) hg
      ((gpr_write_of_ne _ _ (by decide)).trans hp) ((gpr_write_of_ne _ _ (by decide)).trans hB) hin hwr hd
      (8 * g + 2) (Nat.le_refl _)
    have tg' : ∀ r, r ≠ .r4 → r ≠ .r9 → t.gpr r = s.gpr r := fun r h4 h9 =>
      (tg r h4).trans (gpr_write_of_ne _ _ h9)
    have fc : Frame [coreRegion core B] s.mem t.mem := tf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _,
        Region.sub_prefix (by show _ ≤ 8 * Impl.Camellia.PPC64LE.slots; rw [hsl]; omega_using [hg])⟩
    refine WP.of_runBlock ⟨t, te, ⟨?_, fun i hi => ?_⟩, (tg' _ (by decide) (by decide)).trans hB,
      fun r hr => tg' r (kept_r4_r9 r hr).1 (kept_r4_r9 r hr).2, fc, trd, twr⟩
    · exact Proof.Camellia.PPC64LE.Mode.keyArgs_congr hkc
        (fun r hr _ _ _ => tg' r (kept_r4_r9 r hr).1 (kept_r4_r9 r hr).2) trd
        (fc.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    · rw [hkg] at hi ⊢
      have hl : decIdx g i < Spec.Camellia.scheduleLength k.1 := by
        simp only [Spec.Camellia.scheduleLength, hkg]; exact decIdx_lt g hg i hi
      rw [← readBE, tr i hi, readBE, hws, ← decIdx_eq, Proof.Camellia.schedWords_getD _ _ hl]
      rfl
  change WP isa (.seq (.block [.subi .r9 .r28 18]) (.ite (.zero .d .r9) (.block (copyWords 3)) (.block (copyWords 4))))
    s _
  refine VG.WP.seq (WP.of_runBlock ⟨s.write .r9 (s.gpr .r28 - BitVec.ofNat 64 18), ?_, ?_⟩)
  · rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  have a9 : (s.write .r9 (s.gpr .r28 - BitVec.ofNat 64 18)).gpr .r9 = BitVec.ofNat 64 (k.1 - 18) := by
    rw [gpr_write_self, h28]; rcases hR with h | h <;> rw [h] <;> rfl
  refine VG.WP.ite (decide (k.1 - 18 = 0))
    (eval_zero_ofNat _ .r9 (by rcases hR with h | h <;> rw [h] <;> decide) a9) (fun h18 => ?_) (fun h24 => ?_)
  · exact fin 3 (.inl rfl) (by rcases hR with h | h <;> simp [h] at h18 ⊢)
  · exact fin 4 (.inr rfl) (by rcases hR with h | h <;> simp [h] at h24 ⊢)

theorem decCrypt_wp {s : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B decCore.total) (hk : DecReady s B ws k) :
    WP isa decCore.crypt s fun t => t.gpr sb = B ∧ (∀ r ∈ kept, t.gpr r = s.gpr r) ∧ DecReady t B ws k ∧
      Frame [coreRegion decCore B] s.mem t.mem ∧
      (∀ j < decCore.G, Spec.Aes.bytesAt t.mem (blkAddr decCore B j) (4 * decCore.bw) =
        Spec.Camellia.invCipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr decCore B j) (4 * decCore.bw))) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨hk, hw⟩ := hk
  have hk' := hk
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, -⟩ := hk'
  have hsl := slots_val
  have hts := tailSlot_val
  have hfB : B.toNat + 8 * (Impl.Camellia.PPC64LE.slots + 8) ≤ 2 ^ 64 := hs.fit
  have hwr : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region) ∈ s.wr := hs.wr
  have hg : k.1 / 6 = 3 ∨ k.1 / 6 = 4 := by rcases hR with h | h <;> rw [h] <;> decide
  have hg34 : 8 * (k.1 / 6) + 2 ≤ 34 := by rcases hg with h | h <;> rw [h] <;> decide
  have hkS : (8 * keepSlot : Nat) = 272 := rfl
  have kA : (⟨B, 8 * (Impl.Camellia.PPC64LE.slots + 8)⟩ : Region).Contains (B + BitVec.ofNat 64 (8 * keepSlot)) 8 :=
    VG.Offset.contains_base B (by rw [hsl, hkS]; decide) (by rw [hkS]; decide)
  have hst : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * keepSlot)) 8 := by rw [hB]; exact ⟨_, hwr, kA⟩
  -- the state that runs `crypt`: `r3` in its slot, and the copy's address in `r3`
  let a₁ : State := { s with mem := s.mem.writeW (s.gpr sb + BitVec.ofNat 64 (8 * keepSlot)) (s.gpr .r3) }
  have aM : a₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (8 * keepSlot)) (s.gpr .r3) := by
    show s.mem.writeW (s.gpr sb + _) _ = _; rw [hB]
  have aB : (a₁.write .r3 (a₁.gpr sb)).gpr sb = B := (gpr_write_of_ne _ _ (by decide)).trans hB
  have a3 : (a₁.write .r3 (a₁.gpr sb)).gpr .r3 = B := (gpr_write_self _ _ _).trans hB
  have a28 : (a₁.write .r3 (a₁.gpr sb)).gpr .r28 = BitVec.ofNat 64 k.1 := (gpr_write_of_ne _ _ (by decide)).trans h28
  have ag : ∀ r, r ≠ .r3 → (a₁.write .r3 (a₁.gpr sb)).gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have keyIn : KeyIn (a₁.write .r3 (a₁.gpr sb)) := fun i hi => by
    rw [a3]; exact ⟨_, List.mem_append_right _ hwr, VG.Offset.contains_base B (by rw [hsl]; omega_using [hi]) (by omega_using [hi])⟩
  have hsA : ScrIn (a₁.write .r3 (a₁.gpr sb)) B core.total := ⟨hwr, hfB⟩
  -- the regions `decCrypt` writes
  let W : Region := ⟨B + BitVec.ofNat 64 (8 * keepSlot), 8⟩
  have eblk : blkA s = B + BitVec.ofNat 64 (8 * 386) := by rw [blkA, hB, hts]
  have ba : blkA (a₁.write .r3 (a₁.gpr sb)) = blkA s := by rw [blkA, blkA, aB, hB]
  have fa : Frame [W] s.mem a₁.mem := by
    rw [aM]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have wd : ∀ i, i < 34 → Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ W := fun i hi =>
    VG.Offset.disjoint B (.inl (by rw [hkS]; omega_using [hi])) (by omega_using [hi]) (by rw [hkS]; decide)
  have bd : Region.Disjoint ⟨blkA s, 16⟩ W := by
    rw [eblk]; exact VG.Offset.disjoint B (.inr (by rw [hkS]; decide)) (by decide) (by rw [hkS]; decide)
  change WP isa (.seq (.block [.store .d .r3 sb (8 * keepSlot), .logic .or .r3 sb sb])
    (.seq crypt (.block [.load .d .r3 sb (8 * keepSlot)]))) s _
  refine VG.WP.seq (WP.of_runBlock ⟨a₁.write .r3 (a₁.gpr sb), ?_,
    VG.WP.seq (WP.mono (crypt_run aB hsA keyIn a28 hR) fun u ⟨ug, urd, uwr, uf, ub⟩ => ?_)⟩)
  · rw [runBlock_cons, exec_store_d (by decide) ⟨by decide, by decide⟩ hst, runStep_some, runBlock_cons,
      exec_or_self, runStep_some, runBlock_nil]
  have uB : u.gpr sb = B := (ug sb (by decide)).trans aB
  rw [ba] at uf ub
  have hl : InRegions (u.rd ++ u.wr) (u.gpr sb + BitVec.ofNat 64 (8 * keepSlot)) 8 := by
    rw [uB, uwr]; exact ⟨_, List.mem_append_right _ hwr, kA⟩
  have uR3 : u.mem.readW (B + BitVec.ofNat 64 (8 * keepSlot)) 64 = s.gpr .r3 := by
    rw [uf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact bd.symm) (by decide)]
    show a₁.mem.readW _ 64 = _
    rw [aM, Mem.readW_writeW_self64]
  have fsu : Frame [W, ⟨blkA s, 16⟩] s.mem u.mem :=
    (fa.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
      (uf.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have fc : Frame [coreRegion decCore B] s.mem u.mem := fsu.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact VG.Offset.sub_base B (by show 8 * keepSlot + 8 ≤ 8 * Impl.Camellia.PPC64LE.slots; rw [hsl, hkS]; decide)
    · rw [eblk]; exact VG.Offset.sub_base B (by show 8 * 386 + 16 ≤ 8 * Impl.Camellia.PPC64LE.slots; rw [hsl]; decide)
  have vg : ∀ r ∈ kept, (u.write .r3 (u.mem.readW (u.gpr sb + BitVec.ofNat 64 (8 * keepSlot)) 64)).gpr r = s.gpr r := by
    intro r hr
    by_cases h3 : r = .r3
    · subst h3; rw [gpr_write_self, uB, uR3]
    · rw [gpr_write_of_ne _ _ h3, ug r (kept_cWrites r hr), ag r h3]
  refine WP.of_runBlock ⟨u.write .r3 (u.mem.readW (u.gpr sb + BitVec.ofNat 64 (8 * keepSlot)) 64), ?_,
    (gpr_write_of_ne _ _ (by decide)).trans uB, vg, ⟨?_, fun i hi => ?_⟩, fc, fun j hj => ?_, urd, uwr⟩
  · rw [runBlock_cons, exec_load_d (by decide) ⟨by decide, by decide⟩ hl, runStep_some, runBlock_nil]
  · exact Proof.Camellia.PPC64LE.Mode.keyArgs_congr hk (fun r hr _ _ _ => vg r hr) urd
      (fc.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
  · have hi34 : i < 34 := by omega_using [hR, hi]
    show Spec.Camellia.wordAt u.mem _ = _
    rw [Proof.Camellia.wordAt_frame fsu fun r hr => ?_]
    · exact hw i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact wd i hi34
      · rw [eblk]; exact VG.Offset.disjoint B (.inl (by omega_using [hi34])) (by omega_using [hi34]) (by decide)
  · have hj0 : j = 0 := by have : j < 1 := hj; omega_using [this]
    subst hj0
    have hblk : blkAddr decCore B 0 = blkA s := by
      rw [eblk]; show B + BitVec.ofNat 64 (8 * Impl.Camellia.PPC64LE.tailSlot) + BitVec.ofNat 64 (4 * 4 * 0) = _
      rw [VG.Offset.add_add, hts]
    have kw : ∀ i < 8 * (k.1 / 6) + 2, keyWord (a₁.write .r3 (a₁.gpr sb)) i =
        k.2.getD (Proof.Camellia.decPerm (k.1 / 6) i) 0 := fun i hi => by
      rw [keyWord, a3]
      show Spec.Camellia.wordAt a₁.mem _ = _
      rw [Proof.Camellia.wordAt_frame fa fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact wd i (by omega_using [hR, hi])]
      exact hw i hi
    have bl : Spec.Camellia.blockAt a₁.mem (blkA s) = Spec.Camellia.blockAt s.mem (blkA s) :=
      congrArg Vector.ofFn (funext fun i => fa.bytes (R := ⟨blkA s, 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact bd) (by show (16 : Nat) ≤ 2 ^ 64; decide) i.isLt)
    show Spec.Aes.bytesAt u.mem (blkAddr decCore B 0) 16 =
      Spec.Camellia.invCipher (Spec.Camellia.subkeysOfWords k.1 k.2) (Spec.Aes.bytesAt s.mem (blkAddr decCore B 0) 16)
    rw [hblk, ub, invCipher_bytes hR]
    show (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (k.1 / 6) (keyWord (a₁.write .r3 (a₁.gpr sb)))
      (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt a₁.mem (blkA s))))).toList = _
    rw [bl, Proof.Camellia.Serial.cryptWords_congr (k.1 / 6) hg _ _ _ kw]

theorem decReady_frame {s s' : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : DecReady s B ws k) (hk : KeptBut s s') (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion decCore B) r ∨ Region.Sub r (blkRegion decCore B)) :
    DecReady s' B ws k := by
  refine ⟨ready_frame h.1 hk hrd hf hsub hd, fun i hi => ?_⟩
  obtain ⟨-, -, -, hR, -⟩ := h.1
  have hi34 : i < 34 := by rcases hR with e | e <;> rw [e] at hi <;> omega_using [hi]
  have hsl := slots_val
  rw [Proof.Camellia.wordAt_frame hf fun r hr => ?_]
  · exact h.2 i hi
  · rcases hd r hr with hc | hb
    · exact hc.symm.sub_right (VG.Offset.sub_base B (by show 8 * i + 8 ≤ 8 * Impl.Camellia.PPC64LE.slots; rw [hsl]; omega_using [hi34])) |>.symm
    · exact (VG.Offset.disjoint B (d := 8 * i) (n := 8) (e := 8 * 386) (k := 16) (.inl (by omega_using [hi34])) (by omega_using [hi34])
        (by decide)).sub_right hb

/-- The single-block decryption core meets what the modes need. -/
def decCoreSpec : CoreSpec decCore where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.invCipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := Proof.Camellia.PPC64LE.Mode.KeyArgs
  Ready := DecReady
  cipher_len _ _ := by simp [Spec.Camellia.invCipher, decCore, core]
  layout := ⟨by decide, .inr rfl, by decide, by decide, by decide⟩
  keyArgs_congr h e r _ _ f := Proof.Camellia.PPC64LE.Mode.keyArgs_congr h e r f
  ready_frame h e r _ _ f hs hd := decReady_frame h e r f hs hd
  prepare_wp hB hs hR hk := decPrepare_wp hB hs hR hk
  crypt_wp hB hs hk := decCrypt_wp hB hs hk

end VG.Proof.Camellia.PPC64LE.Serial
