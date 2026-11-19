module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.AesGcmSiv.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.TCB.AArch64.Target
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
public import VerifiedGarbage.Proof.GcmSiv.Words
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Save
meta import VerifiedGarbage.Proof.GcmSiv.Words
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds

/-! ### `AesGcmSiv.AArch64.Fn`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on AArch64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` leaves in `x27`
whether the received tag at `W` equals the computed one at `W + 224`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − x27`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_append)
open VG.Proof.AesGcm.AArch64 (add_ofNat_assoc ofNat_sub eval_zero eval_nonzero Others in_of_covers
  length_bytesAt succ_ofNat read_one)

/-- `x27` from the words of the tags: 1 if they are equal, 0 if not. -/
theorem ok_val (d : BitVec 64) :
    (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64) - BitVec.ofNat 64 (if d = 0 then 0 else 1) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases h : d = 0 <;> simp only [h, ↓reduceIte] <;> decide

theorem cmp_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .x27 = BitVec.ofNat 64 (if bytesAt t.mem p.W 16 = bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16
        then 1 else 0) ∧
      Others [.x9, .x10, .x11, .x12, .x27] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain r₀ : InRegions (t.rd ++ t.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 1760 by decide)
  obtain r₈ := E.perm.wR (show 8 + 8 ≤ 1760 by decide)
  obtain u₀ := E.perm.wR (show 224 + 8 ≤ 1760 by decide)
  obtain u₈ := E.perm.wR (show 232 + 8 ≤ 1760 by decide)
  refine ⟨_, by simp only [cmp]; grun [E.x19, BitVec.add_zero, r₀, r₈, u₀, u₈, gpr_addWithCarry, c_addWithCarry,
    mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry, c_write], ?_,
    fun r hr => ?_, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · have key := Proof.AesGcm.AArch64.words_eq t.mem p.W (p.W + BitVec.ofNat 64 224)
    rw [add_ofNat_assoc] at key
    simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      Size.bits, Nat.reduceAdd, show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv,
      Nat.reduceMul]
    refine (congrArg (HSub.hSub (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64))
      (Proof.AesGcm.AArch64.carry_val _)).trans ((ok_val _).trans ?_)
    simp only [Mem.readW, BitVec.setWidth_eq] at key
    simp only [key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, gpr_addWithCarry, hr]

/-! ## The mask -/

abbrev maskBody : List Instr := maskB

theorem byte_and (a : BitVec (8 * 1)) (k : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) &&& BitVec.setWidth 32 k))) =
      a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 64 by omega_arith, show i < 32 by omega_arith,
    hi, decide_true, Bool.true_and]

theorem maskStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A) (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A &&& (s.gpr .x11).setWidth 8) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain wa := Proof.AesGcm.AArch64.in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody, maskB,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      Impl.AesGcm.AArch64.ptr, ha, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, byte_and, read_one,
    Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .x12 = D) (hn : s.gpr .x13 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hnl : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) (.nonzero .x .x13)) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) n) ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) i) ∧
      Others [.x12, .x13, .x14] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega_arith, by rw [hd]; simp, by rw [hn, Nat.sub_zero], by simp [maskBytes, bytesAt, writeBytes_nil],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x13', g', sp', rd', wr'⟩ := maskStep_ok t (A := D + BitVec.ofNat 64 i)
    (by rw [x12, BitVec.add_zero]) (by rw [wr]; exact in_of_covers hw hi (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain hlen : (maskBytes s.mem D ((s.gpr .x11).setWidth 8) i).length = i := by
    simp [maskBytes, length_bytesAt]
  obtain h11 : t.gpr .x11 = s.gpr .x11 := g _ (by decide)
  obtain hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) (i + 1)) := by
    rw [mem', mem, dst_kept' (by omega_arith) _ hlen, h11]
    simp only [maskBytes]
    rw [Proof.AesGcm.AArch64.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem D _ _ (by rw [List.length_map, length_bytesAt]; omega_arith),
      List.length_map, length_bytesAt]
  obtain x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  obtain ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega_arith)
  obtain gg : Others [.x12, .x13, .x14] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega_arith, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩


/-! ## Sixteen bytes at a time -/

theorem vbyte_and (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [vbyte, BitVec.getLsbD_extractLsb', hj]

/-- Sixteen bytes masked in place: `writeBytes` of them masked. -/
theorem writeW_mask (m : Mem) (A : Addr) (kb : Byte) :
    m.writeW A (m.readW A 128 &&& ofVBytes fun _ => kb) = writeBytes m A ((bytesAt m A 16).map (· &&& kb)) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_map, length_bytesAt, Nat.reduceDiv, Nat.reduceMul,
    BitVec.setWidth_eq]
  split
  · rename_i h
    obtain hb := Proof.Cmac.getD_bytesAt m A (n := 16) h
    obtain hl : (x - A).toNat < (bytesAt m A 16).length := by rw [length_bytesAt]; exact h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
      Option.getD_some, hb]
    show vbyte _ _ = _
    rw [vbyte_and, Proof.Aes.AArch64.Aese.vbyte_readW _ _ h, VG.AArch64.vbyte_ofVBytes _ h]
  · rfl

theorem maskVStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 = A) (w : InRegions s.wr A 16) :
    WP isa (.block maskV) s fun s' => s'.mem = s.mem.writeW A (s.mem.readW A 128 &&& s.v .v16) ∧
      s'.gpr .x12 = A + BitVec.ofNat 64 16 ∧ s'.gpr .x14 = s.gpr .x14 - 1 ∧ s'.v .v16 = s.v .v16 ∧
      Others [.x12, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain wa := Proof.AesGcm.AArch64.in_left (rd := s.rd) w
  simp only [maskV]
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (t := .v17) (off := 0) (by decide) (by decide)
    (by rw [ha, BitVec.add_zero]; exact wa), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq (t := .v17) (off := 0) (by decide) (by decide)
    (by simpa only [gpr_setV, wr_setV, ha, BitVec.add_zero] using w), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, mem_setV, gpr_setV, v_setV_self, ha, BitVec.add_zero, Mem.writeW, Mem.readW,
      BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul, v_setV_of_ne _ _ (show VReg.v16 ≠ VReg.v17 by decide)]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits]
    show s.gpr .x12 + _ = _
    rw [ha]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ (show VReg.v16 ≠ VReg.v17 by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]
    rfl

/-- The bytes past what `writeBytes` wrote. -/
theorem bytesAt_writeBytes_after (m : Mem) (D : Addr) (xs : List Byte) (k : Nat) (h : xs.length + k < 2 ^ 64) :
    bytesAt (writeBytes m D xs) (D + BitVec.ofNat 64 xs.length) k = bytesAt m (D + BitVec.ofNat 64 xs.length) k := by
  refine GcmSiv.ext_getD (by simp [length_bytesAt]) fun j hj => ?_
  rw [length_bytesAt] at hj
  rw [Proof.Cmac.getD_bytesAt _ _ hj, Proof.Cmac.getD_bytesAt _ _ hj, Offset.add_add]
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show xs.length + j < 2 ^ 64 by omega_arith)]
  rw [ite_eq_right (by omega_arith)]

theorem maskVLoop_ok (s : State) {D : Addr} {q : Nat} {kb : Byte} (hd : s.gpr .x12 = D)
    (hq : s.gpr .x14 = BitVec.ofNat 64 q) (hq1 : 1 ≤ q) (hql : 16 * q < 2 ^ 64) (hv : s.v .v16 = ofVBytes fun _ => kb)
    (hw : Covers [⟨D, 16 * q⟩] s.wr) :
    WP isa (.loop (.block maskV) (.nonzero .x .x14)) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * q)) ∧ s'.gpr .x12 = D + BitVec.ofNat 64 (16 * q) ∧
      Others [.x12, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskV) (c := .nonzero .x .x14)
    (fun (k : Nat) (t : State) => ∃ i, k = q - i ∧ i < q ∧ t.gpr .x12 = D + BitVec.ofNat 64 (16 * i) ∧
      t.gpr .x14 = BitVec.ofNat 64 (q - i) ∧ t.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * i)) ∧
      t.v .v16 = s.v .v16 ∧ Others [.x12, .x14] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (q - 0) _
    ⟨0, rfl, by omega_arith, by rw [hd]; simp, by rw [hq, Nat.sub_zero], by simp [maskBytes, bytesAt, writeBytes_nil],
      rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x14, mem, v16, g, sp, rd, wr⟩
  refine WP.mono (maskVStep_ok t (A := D + BitVec.ofNat 64 (16 * i)) x12
    (by rw [wr]; exact Proof.AesGcm.AArch64.in_off hw (show 16 * i + 16 ≤ 16 * q by omega_arith) hql))
    fun t' ⟨mem', x12', x14', v16', g', sp', rd', wr'⟩ => ?_
  obtain hlen : (maskBytes s.mem D kb (16 * i)).length = 16 * i := by simp [maskBytes, length_bytesAt]
  obtain hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * (i + 1))) := by
    obtain hb := bytesAt_writeBytes_after s.mem D (maskBytes s.mem D kb (16 * i)) 16 (by rw [hlen]; omega_arith)
    obtain hap := writeBytes_append s.mem D (maskBytes s.mem D kb (16 * i))
      ((bytesAt s.mem (D + BitVec.ofNat 64 (16 * i)) 16).map (· &&& kb)) (by simp [length_bytesAt]; omega_arith)
    rw [hlen] at hb hap
    rw [mem', v16, hv, writeW_mask, mem, hb, hap]
    simp only [maskBytes]
    rw [show 16 * (i + 1) = 16 * i + 16 by omega_arith, Proof.Cmac.bytesAt_add, List.map_append]
  obtain x14'' : t'.gpr .x14 = BitVec.ofNat 64 (q - (i + 1)) := by
    rw [x14', x14, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  obtain ev := eval_nonzero (r := .x14) (a := q - (i + 1)) x14'' (by omega_arith)
  obtain gg : Others [.x12, .x14] s t' := fun r hr => by rw [g' r hr, g r hr]
  obtain x12'' : t'.gpr .x12 = D + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [x12', Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega_arith]
  by_cases he : i + 1 = q
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x12'', he], gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, q - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x12'', x14'', hmem,
      by rw [v16', v16], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8) = xs := by
  rw [show (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `x27` is whether `c` holds. -/
structure MaskPost (p : Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env p t'
  x27 : t'.gpr .x27 = t.gpr .x27
  frame : Frame [⟨p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = if c then bytesAt t.mem p.D p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {c : Prop} [Decidable c]
    (hok : t.gpr .x27 = BitVec.ofNat 64 (if c then 1 else 0)) :
    WP isa mask t (MaskPost p c t) := by
  have hn := L.n_lt
  obtain hq16 : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le _ _
  let kb : Byte := (0#64 - t.gpr .x27).setWidth 8
  -- What `mask` leaves: the data masked.
  obtain fin : ∀ t', t'.mem = writeBytes t.mem p.D (maskBytes t.mem p.D kb p.n) → Env p t' →
      t'.gpr .x27 = t.gpr .x27 → MaskPost p c t t' := fun t' hm E' h27 => by
    obtain hl : (maskBytes t.mem p.D kb p.n).length = p.n := by simp [maskBytes, length_bytesAt]
    refine ⟨E', h27, by rw [hm]; exact Proof.AesGcm.AArch64.writeBytes_frame' _ hl, ?_⟩
    obtain e := Proof.AesGcm.AArch64.bytesAt_writeBytes_self t.mem p.D (maskBytes t.mem p.D kb p.n) (by omega_arith)
    rw [hl] at e
    rw [hm, e]
    simp only [maskBytes, kb, hok]
    split
    · exact map_and_ff _
    · rw [map_and_zero, length_bytesAt]
  -- The mask, the pointer and the counts.
  obtain hpre : WP isa (.block [Impl.AesGcm.AArch64.imm .x9 0, .sub .x .x11 .x9 .x27, Impl.AesGcm.AArch64.mov .x12 .x25,
      .vop (.dup .b16 .v16 .x11), .lsr .x .x14 .x26 4, .lsl .x .x9 .x14 4, .sub .x .x13 .x26 .x9]) t fun t₁ =>
      t₁.gpr .x11 = 0#64 - t.gpr .x27 ∧ t₁.gpr .x12 = p.D ∧ t₁.gpr .x14 = BitVec.ofNat 64 (p.n / 16) ∧
      t₁.gpr .x13 = BitVec.ofNat 64 (p.n - 16 * (p.n / 16)) ∧ t₁.v .v16 = (ofVBytes fun _ => kb) ∧
      Others [.x9, .x11, .x12, .x13, .x14] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    rw [show ([Impl.AesGcm.AArch64.imm .x9 0, .sub .x .x11 .x9 .x27, Impl.AesGcm.AArch64.mov .x12 .x25,
        .vop (.dup .b16 .v16 .x11), .lsr .x .x14 .x26 4, .lsl .x .x9 .x14 4, .sub .x .x13 .x26 .x9] : List Instr) =
        [Impl.AesGcm.AArch64.imm .x9 0, .sub .x .x11 .x9 .x27, Impl.AesGcm.AArch64.mov .x12 .x25] ++
        (.vop (.dup .b16 .v16 .x11) :: [.lsr .x .x14 .x26 4, .lsl .x .x9 .x14 4, .sub .x .x13 .x26 .x9]) from rfl,
      WP.block_append_iff]
    refine WP.run ⟨_, by grun [], rfl⟩ fun u hu => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.run ⟨_, by grun [], rfl⟩ fun u₂ hu₂ => ?_⟩
    subst hu hu₂
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, gpr_setV, State.read]
    · simp [gpr_write, gpr_setV, E.x25]
    · simp [gpr_write, gpr_setV, State.read, E.x26, Proof.AesGcm.AArch64.lsr_ofNat _ _ hn]
    · simp only [gpr_write, gpr_setV, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits,
        E.x26]
      rw [Proof.AesGcm.AArch64.lsr_ofNat _ _ hn, ofNat_lsl, Proof.AesGcm.AArch64.ofNat_sub (by omega_arith) hn]
      congr 2; omega_arith
    · simp [v_write, gpr_write, State.read, kb]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
  refine WP.seq (WP.mono hpre fun t₁ ⟨x11₁, x12₁, x14₁, x13₁, v16₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  obtain x27₁ : t₁.gpr .x27 = t.gpr .x27 := ho₁ _ (by decide)
  -- Sixteen bytes at a time.
  obtain hvec : WP isa (.ite (.zero .x .x14) (.block []) (.loop (.block maskV) (.nonzero .x .x14))) t₁ fun t₂ =>
      t₂.mem = writeBytes t.mem p.D (maskBytes t.mem p.D kb (16 * (p.n / 16))) ∧
      t₂.gpr .x12 = p.D + BitVec.ofNat 64 (16 * (p.n / 16)) ∧ Others [.x12, .x14] t₁ t₂ ∧ t₂.sp = t₁.sp ∧
      t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_zero x14₁ (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using h
      refine WP.block_nil ⟨?_, by rw [x12₁, h0]; simp, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [h0, hm₁]; simp [maskBytes, bytesAt, writeBytes_nil]
    · have h1 : 1 ≤ p.n / 16 := by simp at h; omega_arith
      exact WP.mono (maskVLoop_ok t₁ x12₁ x14₁ h1 (by omega_arith) v16₁
        (Proof.AesGcm.AArch64.covers_prefix E₁.perm.d hq16)) fun t₂ ⟨m₂, x12₂, o₂, sp₂, rd₂, wr₂⟩ =>
          ⟨by rw [m₂, hm₁], x12₂, o₂, sp₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono hvec fun t₂ ⟨m₂, x12₂, o₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain E₂ : Env p t₂ := E₁.keep (fun r hr => o₂ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  obtain x13₂ : t₂.gpr .x13 = BitVec.ofNat 64 (p.n - 16 * (p.n / 16)) := by rw [o₂ _ (by decide), x13₁]
  obtain x11₂ : t₂.gpr .x11 = 0#64 - t.gpr .x27 := by rw [o₂ _ (by decide), x11₁]
  obtain x27₂ : t₂.gpr .x27 = t.gpr .x27 := by rw [o₂ _ (by decide), x27₁]
  obtain hlq : (maskBytes t.mem p.D kb (16 * (p.n / 16))).length = 16 * (p.n / 16) := by
    simp [maskBytes, length_bytesAt]
  -- The last bytes, one at a time.
  refine WP.ite (decide (p.n - 16 * (p.n / 16) = 0)) (eval_zero x13₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n - 16 * (p.n / 16) = 0 := by simpa using h
    refine WP.block_nil (fin t₂ ?_ E₂ x27₂)
    rw [m₂, show 16 * (p.n / 16) = p.n by omega_arith]
  · have h1 : 1 ≤ p.n - 16 * (p.n / 16) := by simp at h; omega_arith
    refine WP.mono (maskLoop_ok t₂ x12₂ x13₂ h1 (by omega_arith)
      (by rw [wr₂, wr₁]; exact Proof.AesGcm.AArch64.covers_off E.perm.d (by omega_arith) hn))
      fun t₃ ⟨m₃, o₃, sp₃, rd₃, wr₃⟩ => ?_
    refine fin t₃ ?_ (E₂.keep (fun r hr => o₃ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃)
      (by rw [o₃ _ (by decide), x27₂])
    obtain hb := bytesAt_writeBytes_after t.mem p.D (maskBytes t.mem p.D kb (16 * (p.n / 16)))
      (p.n - 16 * (p.n / 16)) (by rw [hlq]; omega_arith)
    obtain hap := writeBytes_append t.mem p.D (maskBytes t.mem p.D kb (16 * (p.n / 16)))
      ((bytesAt t.mem (p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n - 16 * (p.n / 16))).map (· &&& kb))
      (by simp [length_bytesAt]; omega_arith)
    rw [hlq] at hb hap
    rw [m₃, m₂, x11₂]
    simp only [maskBytes] at hb hap ⊢
    rw [hb, hap, ← List.map_append, ← Proof.Cmac.bytesAt_add, show 16 * (p.n / 16) + (p.n - 16 * (p.n / 16)) = p.n by
      omega_arith]

end VG.Proof.AesGcmSiv.AArch64

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`)
and what the state may access (`args_of_seal`, `args_of_open`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, keeps the arguments in `x19`–`x26` and `tag` at `W + 216`
(`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (saved)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left SavedAt savedR save_ok savedMem_frame savedAt_save in_off
  Others)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .x0
  W := stackArg s 0
  N := s.gpr .x2
  A := s.gpr .x3
  D := s.gpr .x5
  T := s.gpr .x7
  SP := s.sp
  R := (s.gpr .x1).toNat
  al := (s.gpr .x4).toNat
  n := (s.gpr .x6).toNat

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, _, b1, b2, b3, b4, b5, b6, _, hR⟩ := h
  exact ⟨b1, b6, b2, b3, b4, d2, d1, d4, d3, d6, d5, d9, b5, d8, d7, hR, BitVec.isLt _, BitVec.isLt _⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨s.gpr .x2, 12⟩] (s.rd ++ s.wr)) (hA : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3808⟩] s.wr)
    (hT : Covers [⟨s.gpr .x7, 16⟩] (s.rd ++ s.wr)) : Perm (prmOf s) s :=
  ⟨hk, hN, hA, hD, hW, hT⟩

/-- `seal`'s layout and permissions, its tag to write, and its stack argument
to read. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩, args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨s.gpr .x7, 16⟩, ⟨stackArg s 0, 3808⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (covers_left (mwr _ (by simp))), mwr _ (by simp), mrd _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag to read, and its
stack argument to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x7, 16⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨stackArg s 0, 3808⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the entry writes: the save area and `tag`'s address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 96⟩

/-- `tag`'s address, at `W + 216`. -/
abbrev TagSlot (p : Prm) (m : Mem) : Prop := m.readW (p.W + BitVec.ofNat 64 216) 64 = p.T

/-- `entry`. -/
theorem entry_ok {s : State} (P : Perm (prmOf s) s) (hA : Covers [args s] (s.rd ++ s.wr)) :
    WP isa (.block entry) s fun s₁ => Env (prmOf s) s₁ ∧ SavedAt s₁.mem (prmOf s).W s ∧
      Frame [entryR (prmOf s).W] s.mem s₁.mem ∧ TagSlot (prmOf s) s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.block_append (WP.block_append (WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s₀ hs₀ => ?_))
  subst hs₀
  obtain hW₀ : (s.write .x .x9 (s.mem.readW s.sp 64)).gpr .x9 = (prmOf s).W := by
    simp [gpr_write, prmOf, stackArg, stackArgAddr]
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok _ .x9 hW₀ (by simpa only [wr_write] using P.w1760)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain hWv : (prmOf s).W = s.mem.readW s.sp 64 := by simp [prmOf, stackArg, stackArgAddr, Mem.readW]
  obtain w216 : InRegions s₁.wr (s.mem.readW s.sp 64 + BitVec.ofNat 64 216) 8 := by
    rw [wr₁, ← hWv]; simpa only [wr_write] using in_off P.w (show 216 + 8 ≤ 1760 by decide) (by decide)
  refine WP.run ⟨_, by grun [g₁, BitVec.add_zero, w216], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  obtain hs : ∀ r ∈ saved, (s.write .x .x9 (s.mem.readW s.sp 64)).gpr r.1 = s.gpr r.1 := by
    intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  obtain sv : SavedAt s₁.mem (prmOf s).W s := by
    rw [m₁]; exact fun p hp => (savedAt_save _ _ _ p hp).trans (hs p hp)
  obtain fS : Frame [entryR (prmOf s).W] s.mem s₁.mem := by
    rw [m₁]; simp only [mem_write]
    exact (savedMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  obtain c216 : (entryR (prmOf s).W).Contains ((prmOf s).W + BitVec.ofNat 64 216) (64 / 8) := by
    rw [show (prmOf s).W + BitVec.ofNat 64 216 = ((prmOf s).W + BitVec.ofNat 64 128) + BitVec.ofNat 64 88 from
      (Offset.add_add_eq _ (by omega_arith)).symm]
    exact Offset.contains_base _ (by decide) (by decide)
  obtain e : ∀ (m : Mem) (a : Addr) (v : BitVec 64), m.write a 8 v = m.writeW a v := fun m a v => by
    simp [Mem.writeW]
  rw [← hWv] at *
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [sp_write]; rw [sp₁]; rfl,
    P.of_eq (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)⟩, ?_, ?_, ?_, ?_, ?_⟩
  iterate 8 (simp [gpr_write, g₁, prmOf, ofNat_toNat64, stackArg, stackArgAddr, Mem.readW])
  · simp only [mem_write, e]
    exact sv.frame ((Frame.refl [(⟨(prmOf s).W + BitVec.ofNat 64 216, 8⟩ : Region)] _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · simp only [mem_write, e]
    exact fS.writeW (List.mem_singleton_self _) _ c216
  · simp only [mem_write, e, TagSlot, Mem.readW_writeW_self64]
    simp [gpr_write, g₁, prmOf]
  · simp only [rd_write]; exact rd₁
  · simp only [wr_write]; exact wr₁

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.W 16 = bytesAt s.mem p.T 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain r₀ := E.perm.wR (show 216 + 8 ≤ 1760 by decide)
  obtain t₀ : InRegions (s.rd ++ s.wr) p.T 8 := by simpa using in_off (d := 0) (n := 8) E.perm.t (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) E.perm.t (by decide) (by decide)
  obtain w₀ : InRegions s.wr p.W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 1760 by decide)
  obtain w₈ := E.perm.wW (show 8 + 8 ≤ 1760 by decide)
  obtain hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  obtain hs : Mem.Sep (p.T + BitVec.ofNat 64 8) (64 / 8) p.W (64 / 8) :=
    L.t_w.sep (Offset.contains_base p.T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base p.W (d := 0) (n := 8) (k := 3808) (by decide) (by decide))
  refine ⟨_, by simp only [recv]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem)
    (hTw : Covers [⟨p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.T 16 = bytesAt s.mem p.W 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain r₀ := E.perm.wR (show 216 + 8 ≤ 1760 by decide)
  obtain t₀ : InRegions s.wr p.T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  obtain w₀ : InRegions (s.rd ++ s.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 1760 by decide)
  obtain w₈ := E.perm.wR (show 8 + 8 ≤ 1760 by decide)
  obtain hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  obtain hs : Mem.Sep (p.W + BitVec.ofNat 64 8) (64 / 8) p.T (64 / 8) :=
    L.t_w.symm.sep (Offset.contains_base p.W (d := 8) (n := 8) (k := 3808) (by decide) (by decide))
      (by simpa using Offset.contains_base p.T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by simp only [tagOut]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, or the key schedule. -/
tactic_template "disj_tac" L:term : tactic => `(tactic| (
                   simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
                   repeat' apply And.intro
                   all_goals first
                     | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
                     | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
                     | (with_reducible refine Lay.d_w' $L ?_) <;> decide
                     | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
                     | (with_reducible refine Lay.k_w' $L ?_) <;> decide
                     | (with_reducible refine Lay.n_w' $L ?_) <;> decide
                     | (with_reducible refine Lay.a_w' $L ?_) <;> decide
                     | with_reducible exact Lay.k_d $L
                     | with_reducible exact Lay.n_d $L
                     | with_reducible exact Lay.a_d $L
                     | (with_reducible refine Lay.t_w' $L ?_) <;> decide
                     | with_reducible exact Lay.t_d $L
                     | with_reducible exact (Lay.t_d $L).symm
                     | with_reducible exact (Lay.d_w $L).symm))

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.AArch64.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega_arith)]

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `tag`'s address in `W`, after code that misses it. -/
theorem TagSlot.frame {p : Prm} {m m' : Mem} (h : TagSlot p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r) : TagSlot p m' := by
  unfold TagSlot at *
  rw [hf.readW (r := ⟨p.W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) hd (by decide), h]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (h : sealPre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨L, P, hTw, hA⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₁ ⟨E₁, sv₁, f₁, sl₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (keys_ok v L E₁)) fun s₂ ⟨Ky, _, kw⟩ => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  -- The copy of the tag, and `restore`.
  obtain sl₅ : TagSlot (prmOf s) s₅.mem :=
    (((sl₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L)
  obtain w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, kw, wr₁]
  obtain ⟨s₆, run₆, fT, hT₆, -, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env sl₅ (by rw [w₅]; exact hTw)
  obtain E₆ : Env (prmOf s) s₆ := Cr.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  obtain sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 88 ≤ 1760 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok (s₀ := s) E₆.x19 E₆.sp E₆.w1760R sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R) (Spec.GcmSiv.keyLen (prmOf s).R)
      (bytesAt s.mem (prmOf s).N 12) (bytesAt s.mem (prmOf s).D (prmOf s).n) (bytesAt s.mem (prmOf s).A (prmOf s).al) =
    (bytesAt s'.mem (prmOf s).D (prmOf s).n, bytesAt s'.mem (prmOf s).T 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega_arith)]
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  obtain n₂ : bytesAt s₂.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₂ : bytesAt s₂.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega_arith)]
  obtain d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_arith), bytesAt_keep f₁ (by disj_tac L) (by omega_arith)]
  obtain d₄ : bytesAt s₄.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega_arith), bytesAt_keep Po.frame (by disj_tac L) (by omega_arith), d₂]
  obtain key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  obtain t₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [L.w0] at t₅
  have tg := Tg.out
  rw [L.w0] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 224`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok Others)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  obtain ⟨L, P, hA⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₀ ⟨E₀, sv₀, f₀, sl₀, _, _⟩ => ?_)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, -, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L E₀ sl₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env (prmOf s) s₁ := E₀.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  obtain fR' : Frame [⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by rw [L.w0]; exact fR
  obtain sv₁ : SavedAt s₁.mem (prmOf s).W s := sv₀.frame fR' (by disj_tac L)
  obtain f₁ : Frame [entryR (prmOf s).W, ⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩, by simp, fun _ h => h⟩)
  obtain hT₁ : bytesAt s₁.mem (prmOf s).W 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [hR₁, bytesAt_keep f₀ (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  obtain a₃ : bytesAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  obtain hG₃ : Spec.Gcm.blockAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  obtain hY₃ : Spec.Gcm.blockAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  -- Its tag at `W + 224`.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 224) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, x27₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ x27₆) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  obtain sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok (s₀ := s) (Mk.env.write (by decide) _).x19 (Mk.env.write (by decide) _).sp
    (Mk.env.write (by decide) _).w1760R (by simp only [mem_write]; exact sv₇)) fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  obtain n₃ : bytesAt s₃.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by decide), bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₃' : bytesAt s₃.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega_arith)]
  obtain d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_arith), bytesAt_keep f₁ (by disj_tac L) (by omega_arith)]
  obtain tag₂ : bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), L.w0, hT₁]
  obtain tag₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide), bytesAt_keep Po.frame (by disj_tac L) (by decide),
      bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [L.w0] at tag₂ tag₅
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
    rw [ciph_keep Po.frame (by disj_tac L) hRb, ciph_cryR L Cr.frame]
  obtain d₆ : bytesAt s₆.mem (prmOf s).D (prmOf s).n = bytesAt s₃.mem (prmOf s).D (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega_arith), bytesAt_keep Po.frame (by disj_tac L) (by omega_arith)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  obtain ax : s'.gpr .x0 = s₆.gpr .x27 := by
    rw [hx0]; simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero]; exact Mk.x27
  rw [x27₆, tg, tag₅] at ax
  show openPost (openResult s) s' (prmOf s).D (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
            (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
          bytesAt s.mem (prmOf s).T 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
        (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
      bytesAt s.mem (prmOf s).T 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (prmOf s).T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) := Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.AArch64

end

end

/-!
# AES-GCM-SIV on AArch64: the tag, counter mode and the functions are constant time

Untrusted: everything here is checked by Lean. Each call of `vg_aes_ctr32`
has the same arguments in both runs, which encrypt the same number of
blocks; the code around the calls, the comparison and the mask pass the
taint analysis (`open` never branches on whether the tag is right). The
loads of `W` from the stack and of `tag`'s address from `W` give the same
address in both runs (by correctness), and the taint analysis checks the
code after them (`entry_rel`, `rel_ldrT`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_ite rel_taint ct_of GcmImpl CtrCall ctr_call ctr_callLe ctr_relLe eval_zero in_off
  RelCT.block_split
  eval_nonzero Others add_ofNat_assoc ofNat_sub lsr_ofNat)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 224) : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 224) : RelCT isa (Eq2 τ₁ τ₂) (tag v.callees o) TT := by
  have w : ∀ {τ : State}, Env p τ → WP isa (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++
      [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 64 240)
        (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 o) (p.W + BitVec.ofNat 64 1760) p.R 1 (p.Wn - 1760) ∧ Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok E ho
      have E' : Env p t₁ := E.keep (fun r hr => ho₁ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, tagCall L E' ho x0 x1 x2 x3 x4 x5, E'⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) (tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.block [.ldr .w .x9 .x19 cbO, .addImm .w .x9 .x9 1, .str .w .x9 .x19 cbO, Impl.AesGcm.AArch64.ptr .x27 .x27 16,
      .subImm .x .x28 .x28 16, .lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {j : Nat} (hj : 16 * (j + 1) ≤ p.n) (a27 : τ₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j))
    (b27 : τ₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j))
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) :
    RelCT isa (Eq2 τ₁ τ₂) (cryptBlock v.callees) TT := by
  have w : ∀ {τ : State}, Env p τ → τ.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) →
      τ.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.D + BitVec.ofNat 64 (16 * j))
          (p.W + BitVec.ofNat 64 1760) p.R 1 (p.Wn - 1760) ∧ Env p t₁ ∧ t₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
          t₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun E h27 h28 => by
    obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok E h27
    have E' : Env p t₁ := E.keep (fun r hr => ho₁ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, blkCall L E' hj x0 x1 x2 x3 x4 x5, E', by rw [ho₁ _ (by decide), h27],
      by rw [ho₁ _ (by decide), h28]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112)
      (p.D + BitVec.ofNat 64 (16 * j)) (p.W + BitVec.ofNat 64 1760) p.R 1 (p.Wn - 1760) ∧ Env p t ∧
      t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧ t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) →
      WP isa (callCtr v.callees) t fun u => Env p u ∧ u.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
        u.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun ⟨cc, E, h27, h28⟩ =>
    WP.mono (ctr_call v.ctr cc) fun _ P => ⟨E.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), h27], by rw [P.saved _ (by decide) (by decide), h28]⟩
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) blkA_check) (w E₁ a27 a28)
    (w E₂ b27 b28) fun u₁ u₂ A₁ A₂ => ?_
  exact rel_seq (rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.1.sp_eq A₂.2.1)) (wc A₁) (wc A₂)
    fun w₁ w₂ ⟨F₁, c27₁, c28₁⟩ ⟨F₂, c27₂, c28₂⟩ => rel_env F₁ F₂ [.x27, .x28] (by simp [c27₁, c27₂, c28₁, c28₂])
      blkP_check

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : Prm) (j : Nat) (t : State) : Prop where
  env : Env p t
  x27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)
  x28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok (v : GcmImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State}
    (B : BL p j t) :
    WP isa (cryptBlock v.callees) t fun t' => BL p (j + 1) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (j + 1)) / 16) := by
  have hn := L.n_lt
  obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok B.env B.x27
  have E₁ : Env p t₁ := B.env.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr (blkCall L E₁ hj x0 x1 x2 x3 x4 x5)) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x28]
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 1760 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 1760 by decide)
  refine WP.run ⟨_, by grun [E₂.x19, c₀, c₁, h27₂, h28₂], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  refine ⟨⟨E₂.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, ?_⟩, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, add_ofNat_assoc]
    congr 2
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega_arith) (by omega_arith)]; congr 1
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega_arith) (by omega_arith), lsr_ofNat _ _ (by omega_arith)]; congr 2

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (B : BL p 0 t)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (p.n / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock v.callees) (.nonzero .x .x9))) t
      (BL p (p.n / 16)) := by
  have hn := L.n_lt
  refine WP.ite (decide (p.n / 16 = 0)) (eval_zero h9 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega_arith, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (cryptBlockL_ok v L (j := j) (by omega_arith) B') fun t'' ⟨B'', x9⟩ => ?_
    have ev := eval_nonzero x9 (by omega_arith)
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega_arith), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega_arith), p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, B''⟩

theorem cryptHead_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block cryptHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.seq (.block [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
      Impl.AesGcm.AArch64.mov .x13 .x28]) Impl.AesGcm.AArch64.xorLoop) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, Env p σ → WP isa (.block cryptHead) σ fun t₁ => BL p 0 t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 16) := fun E => by
    obtain ⟨t₁, run₁, -, x27₁, x28₁, x9₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, ⟨E.keep (fun r hr => ho₁ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁,
      by rw [x27₁, Nat.mul_zero, BitVec.add_zero], by rw [x28₁, Nat.mul_zero, Nat.sub_zero]⟩, x9₁⟩
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (wh E₁) (wh E₂)
    fun u₁ u₂ ⟨B₁, x9₁⟩ ⟨B₂, x9₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega_arith)) (eval_zero x9₂ (by omega_arith))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (cryptMidL_ok v L B₁ x9₁) (cryptMidL_ok v L B₂ x9₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t₁ ∧ BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega_arith, B₁, B₂⟩
    refine rel_wpQ (cryptBlock_rel v L J₁.env J₂.env (j := j) (by omega_arith) J₁.x27 J₂.x27 J₁.x28 J₂.x28)
      (cryptBlockL_ok v L (by omega_arith) J₁) (cryptBlockL_ok v L (by omega_arith) J₂) fun a b ⟨K₁, x9₁⟩ ⟨K₂, x9₂⟩ => ?_
    have ev₁ := eval_nonzero x9₁ (by omega_arith)
    have ev₂ := eval_nonzero x9₂ (by omega_arith)
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : j + 1 ≠ p.n / 16 := by simp at hc; omega_arith
    exact ⟨p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, K₁, K₂⟩
  -- The last bytes.
  have x28₁ : w₁.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₁.x28]; congr 1; omega_arith
  have x28₂ : w₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₂.x28]; congr 1; omega_arith
  refine rel_ite (eval_zero x28₁ (by omega_arith)) (eval_zero x28₂ (by omega_arith))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun _ => ?_)
  refine rel_seq (tag_rel v L C₁.env C₂.env (o := 224) (by decide)) (tag_ok v L C₁.env (o := 224) (by decide))
    (tag_ok v L C₂.env (o := 224) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.x27, .x28] (by simp [T₁.x27, T₂.x27, T₁.x28, T₂.x28, C₁.x27, C₂.x27, C₁.x28, C₂.x28])
    cryptTailRest_check

/-! ## The functions -/

/-- `ldr x9, [sp]`: `W` in `x9`. -/
theorem ldr9_ok {s : State} (hA : Covers [args s] (s.rd ++ s.wr)) :
    WP isa (.block [.ldrSp .x9 0]) s fun s' => s'.gpr .x9 = stackArg s 0 ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write, stackArg, stackArgAddr, Mem.readW], fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩

theorem ldr9_check : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 0]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem entryRest_check : ∃ h, (taint.check (Taint.ofRegs [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (.block (Impl.AesGcm.AArch64.save .x9 ++ [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x2,
      Impl.AesGcm.AArch64.mov .x21 .x0, Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x23 .x3,
      Impl.AesGcm.AArch64.mov .x24 .x4, Impl.AesGcm.AArch64.mov .x25 .x5, Impl.AesGcm.AArch64.mov .x26 .x6,
      .str .x .x7 .x19 tagPO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.seq (.block cmp) (.seq mask (.block ([Impl.AesGcm.AArch64.mov .x0 .x27] ++ Impl.AesGcm.AArch64.restore)))) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) : prmOf σ₁ = prmOf σ₂ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  simp only [prmOf, h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) (hA₁ : Covers [args σ₁] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [args σ₂] (σ₂.rd ++ σ₂.wr)) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  show RelCT isa _ (.block ([.ldrSp .x9 0] ++ Impl.AesGcm.AArch64.save .x9 ++ _)) _
  rw [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] hsp (by simp) ldr9_check) (ldr9_ok hA₁) (ldr9_ok hA₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, sp₁, _, _⟩ ⟨x9₂, g₂, sp₂, _, _⟩ => ?_)
  refine rel_taint _ (by rw [sp₁, sp₂, hsp]) ?_ entryRest_check
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂, hw]
  · rw [g₁ r h9, g₂ r h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The entry of the second run, with the first's public arguments. -/
theorem entry_pub {σ₁ σ₂ : State} (hp : onePub σ₁ σ₂) (P : Perm (prmOf σ₂) σ₂)
    (hA : Covers [args σ₂] (σ₂.rd ++ σ₂.wr)) :
    WP isa (.block entry) σ₂ fun s => Env (prmOf σ₁) s ∧ TagSlot (prmOf σ₁) s.mem := by
  rw [prmOf_eq hp]
  exact WP.mono (entry_ok P hA) fun _ h => ⟨h.1, h.2.2.2.1⟩

/-- `ldr x9, [x19, #216]`: `tag`'s address in `x9`. -/
theorem ldrT_ok {p : Prm} {s : State} (E : Env p s) (hT : TagSlot p s.mem) :
    WP isa (.block [.ldr .x .x9 .x19 tagPO]) s fun s' => s'.gpr .x9 = p.T ∧ Env p s' := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 1760 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  refine WP.run ⟨_, by grun [E.x19, r₀, hT'], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write], E.write (by decide) _⟩

theorem ldrT_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block [.ldr .x .x9 .x19 tagPO]) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- `ldr x9, [x19, #216]` and then `l`, which the taint analysis checks with
`x9` public, in two runs with the same public arguments. -/
theorem rel_ldrT {p : Prm} {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) (T₁ : TagSlot p σ₁.mem)
    (T₂ : TagSlot p σ₂.mem) {l : List Instr}
    (hc : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9])) (.block l) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (([.ldr .x .x9 .x19 tagPO] : List Instr) ++ l)) TT :=
  RelCT.block_split (rel_seq (rel_env E₁ E₂ [] (by simp) ldrT_check) (ldrT_ok E₁ T₁) (ldrT_ok E₂ T₂)
    fun _ _ ⟨x9₁, E₁'⟩ ⟨x9₂, E₂'⟩ => rel_env E₁' E₂' [.x9] (by simp [x9₁, x9₂]) hc)

theorem sealEnd_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9]))
    (.block (tagOut.tail ++ Impl.AesGcm.AArch64.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9])) (.block recv.tail) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -, hA₁⟩ := args_of_seal h₁
  obtain ⟨-, P₂, -, hA₂⟩ := args_of_seal h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  refine rel_seq (keys_rel v L E₁ E₂) (keys_ok v L E₁) (keys_ok v L E₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (polyval_rel v L K₁.env K₂.env) (polyval_ok v L K₁.env K₁.hkey K₁.acc)
    (polyval_ok v L K₂.env K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  refine rel_seq (tag_rel v L P₁.env P₂.env (o := 0) (by decide)) (tag_ok v L P₁.env (o := 0) (by decide))
    (tag_ok v L P₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  refine rel_seq (crypt_rel v L T₁.env T₂.env) (crypt_ok v L T₁.env) (crypt_ok v L T₂.env)
    fun d₁ d₂ C₁ C₂ => ?_
  have sl : ∀ {τ a b c d : State}, TagSlot (prmOf σ₁) τ.mem → KeysPost (prmOf σ₁) τ a → PolyPost (prmOf σ₁) a b →
      TagPost (prmOf σ₁) 0 b c → CryptPost (prmOf σ₁) c d → TagSlot (prmOf σ₁) d.mem := fun S K P T C =>
    (((S.frame K.frame (by disj_tac L)).frame P.frame (by disj_tac L)).frame T.frame (by disj_tac L)).frame C.frame
      (by disj_tac L)
  exact rel_ldrT (l := tagOut.tail ++ Impl.AesGcm.AArch64.restore) C₁.env C₂.env (sl S₁ K₁ P₁ T₁ C₁)
    (sl S₂ K₂ P₂ T₂ C₂) sealEnd_check

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, hA₁⟩ := args_of_open h₁
  obtain ⟨-, P₂, hA₂⟩ := args_of_open h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  have wr : ∀ {τ : State}, Env (prmOf σ₁) τ → TagSlot (prmOf σ₁) τ.mem → WP isa (.block recv) τ (Env (prmOf σ₁)) :=
    fun E S => by
      obtain ⟨t, run, -, -, -, ho, sp, rd, wr⟩ := recv_ok L E S
      exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_ldrT (l := recv.tail) E₁ E₂ S₁ S₂ recv_check) (wr E₁ S₁) (wr E₂ S₂) fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel v L R₁ R₂) (keys_ok v L R₁) (keys_ok v L R₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (crypt_rel v L K₁.env K₂.env) (crypt_ok v L K₁.env) (crypt_ok v L K₂.env) fun b₁ b₂ C₁ C₂ => ?_
  have hG : ∀ {σ τ : State}, KeysPost (prmOf σ₁) σ τ → ∀ {u : State}, CryptPost (prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.acc,
      bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine rel_seq (polyval_rel v L C₁.env C₂.env) (polyval_ok v L C₁.env (hG K₁ C₁).1 (hG K₁ C₁).2)
    (polyval_ok v L C₂.env (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  exact rel_seq (tag_rel v L P₁.env P₂.env (o := 224) (by decide)) (tag_ok v L P₁.env (o := 224) (by decide))
    (tag_ok v L P₂.env (o := 224) (by decide)) fun d₁ d₂ T₁ T₂ => rel_env T₁.env T₂.env [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.AArch64
