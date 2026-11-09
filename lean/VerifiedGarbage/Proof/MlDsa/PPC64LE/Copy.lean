module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Copy
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Base
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.PiecesCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Copy
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA on PPC64LE: copies of whole doublewords

`copyW (sb, so) (db, dO) n` (`Impl/MlDsa/PPC64LE/Copy.lean`), with `sb` and
`db` callee-saved: the `8n` bytes at `sb + so` are at `db + dO` after it, it
changes memory only there, and it keeps the callee-saved registers, the
stack pointer and the permissions (`copyW_ok`): the moves of its arguments,
then the doubleword loop of the gathers (`Proof/Gather/PPC64LE/Copy.lean`).
Two runs whose `sb`, `db` and stack pointer agree leak the same
(`copyW_tr`): the moves access no memory, and the loop's addresses are
those of `r3`, `r5` and `r9` after them.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE

open VG VG.PPC64LE VG.WriteBytes
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne)
open VG.Impl.MlDsa.PPC64LE (copyW)
open VG.Impl.MlDsa.PPC64LE.KeyGen (Arg glue)
open VG.Proof.MlKem.PPC64LE (Kept)
open VG.Spec.Sha3 (bytesAt)

/-- Bytes written with `writeBytes` read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- `d ← b + o`, for a base register other than `d`. -/
theorem ptr_ok (d b : Reg) (hb : b ≠ d) {o : Nat} (ho : o < 2 ^ 31) (s : State) :
    WP isa (.block (Arg.instrs d (.ptr (b, o)))) s (· = s.write d (s.gpr b + BitVec.ofNat 64 o)) := by
  rw [Arg.instrs, WP.block_append_iff]
  refine WP.mono (KeyGen.loadImm_ok d ho s) fun s1 e => ?_
  subst e
  refine WP.cons exec_add (WP.block_nil ?_)
  rw [gpr_write_self, gpr_write_of_ne _ _ hb, KeyGen.write_write, BitVec.add_comm]

theorem pres_ne {r : Reg} (h : r ∈ preserved) : r ≠ .r3 ∧ r ≠ .r5 ∧ r ≠ .r9 ∧ r ∉ ([.r0, .r3, .r4, .r5, .r6, .r9] : List Reg) := by
  revert r; decide

/-- The state after the moves of `copyW`'s arguments. -/
abbrev copySt (sb db : Reg) (so dO n : Nat) (s : State) : State :=
  ((s.write .r3 (s.gpr sb + BitVec.ofNat 64 so)).write .r9
    ((s.write .r3 (s.gpr sb + BitVec.ofNat 64 so)).gpr db + BitVec.ofNat 64 dO)).write .r5 (BitVec.ofNat 64 n)

theorem copy_glue {sb db : Reg} {so dO n : Nat} (s3 : sb ≠ .r3) (d9 : db ≠ .r9) (hso : so < 2 ^ 31)
    (hdo : dO < 2 ^ 31) (hn : n < 2 ^ 31) (s : State) :
    WP isa (.block (glue [(.r3, .ptr (sb, so)), (.r9, .ptr (db, dO)), (.r5, .imm n)])) s
      (· = copySt sb db so dO n s) := by
  simp only [glue, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (ptr_ok .r3 sb s3 hso s) fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (ptr_ok .r9 db d9 hdo _) fun s₂ e₂ => ?_
  subst e₂
  exact KeyGen.loadImm_ok .r5 hn _

/-- `copyW`: the `8n` bytes at `sb + so` to `db + dO`, apart. -/
theorem copyW_ok {sb db : Reg} {so dO n : Nat} {s : State} (hsb : sb ∈ preserved) (hdb : db ∈ preserved)
    (hso : so < 2 ^ 31) (hdo : dO < 2 ^ 31) (hn : n < 2 ^ 31) (hn1 : 1 ≤ n)
    (cr : Covers [⟨s.gpr sb + BitVec.ofNat 64 so, 8 * n⟩] (s.rd ++ s.wr))
    (cw : Covers [⟨s.gpr db + BitVec.ofNat 64 dO, 8 * n⟩] s.wr)
    (hd : (⟨s.gpr sb + BitVec.ofNat 64 so, 8 * n⟩ : Region).Disjoint ⟨s.gpr db + BitVec.ofNat 64 dO, 8 * n⟩) :
    WP isa (copyW (sb, so) (db, dO) n) s fun s' =>
      Kept [⟨s.gpr db + BitVec.ofNat 64 dO, 8 * n⟩] s s' ∧
      bytesAt s'.mem (s.gpr db + BitVec.ofNat 64 dO) (8 * n) = bytesAt s.mem (s.gpr sb + BitVec.ofNat 64 so) (8 * n) := by
  obtain ⟨s3, s5, s9, sc⟩ := pres_ne hsb
  obtain ⟨d3, d5, d9, dc⟩ := pres_ne hdb
  unfold copyW
  refine WP.seq (WP.mono (copy_glue s3 d9 hso hdo hn s) fun s₃ e₃ => ?_)
  subst e₃
  refine WP.mono (Gather.PPC64LE.copyWords_wp _ (S := s.gpr sb + BitVec.ofNat 64 so)
    (D := s.gpr db + BitVec.ofNat 64 dO) (k := n) ⟨?_, ?_, gpr_write_self _ _ _, hn1, by omega, cr, cw, hd⟩)
    fun s' ⟨hm, _, _, _, kp⟩ => ?_
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide), gpr_write_self]
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, gpr_write_of_ne _ _ d3]
  simp only [VG.PPC64LE.RegUpd.mem_write] at hm
  have hl : (Spec.Aes.bytesAt s.mem (s.gpr sb + BitVec.ofNat 64 so) (8 * n)).length = 8 * n := by
    simp [Spec.Aes.bytesAt]
  refine ⟨⟨fun r hr => ?_, kp.sp, kp.rd, kp.wr, ?_⟩, ?_⟩
  · obtain ⟨r3, r5, r9, rc⟩ := pres_ne hr
    rw [kp.gpr r rc, gpr_write_of_ne _ _ r5, gpr_write_of_ne _ _ r9, gpr_write_of_ne _ _ r3]
  · rw [hm]
    exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  · rw [hm]
    have := bytesAt_writeBytes_self s.mem (s.gpr db + BitVec.ofNat 64 dO)
      (Spec.Aes.bytesAt s.mem (s.gpr sb + BitVec.ofNat 64 so) (8 * n)) (by rw [hl]; omega)
    rw [hl] at this
    exact this

/-- Two runs of `copyW` whose `sb`, `db` and stack pointer agree leak the same. -/
theorem copyW_tr {sb db : Reg} {so dO n : Nat} (s3 : sb ≠ .r3) (d3 : db ≠ .r3) (d9 : db ≠ .r9) (hso : so < 2 ^ 31)
    (hdo : dO < 2 ^ 31) (hn : n < 2 ^ 31) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.sp = y.sp ∧ x.gpr sb = y.gpr sb ∧ x.gpr db = y.gpr db) :
    RelCT isa P (copyW (sb, so) (db, dO) n) fun _ _ => True := by
  unfold copyW
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = copySt sb db so dO n x)
    (VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem (KeyGen.glue_noMem _))
    fun x y _ => ⟨copy_glue s3 d9 hso hdo hn x, copy_glue s3 d9 hso hdo hn y⟩) ?_
  refine RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r3, .r5, .r9])
    (fun a b ⟨_, x, y, hp, e₁, e₂⟩ => ?_) (by taint_decide)
  subst e₁ e₂
  obtain ⟨hsp, hs, hd⟩ := hP x y hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [copySt, VG.PPC64LE.RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, d3, hs, hd]

end VG.Proof.MlDsa.PPC64LE
