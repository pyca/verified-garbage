module

public import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Saving sign and verify arguments without changing stack inputs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- A 64-bit stack argument at `[sp, #off]`. -/
theorem exec_ldrSp_arg {s : State} {t : Reg} {o : Nat} (ho : o % 8 = 0 ∧ o < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 o) 8) :
    exec (.ldrSp t o) s = some (s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 o) 64)) := by
  simp only [exec, ho, and_self, ite_true, State.load, h, Option.map_some, Mem.readW]

/-- Signing's register arguments, before `digest_len` is read from the stack. -/
def signStores : List Instr :=
  [movi .x3 0, SignVerify.initial .x3 .signature,
    SignVerify.initial .x0 .out, SignVerify.initial .x2 .p, SignVerify.initial .x4 .pLen,
    SignVerify.initial .x5 .nonce, SignVerify.initial .x6 .qLen, SignVerify.initial .x7 .digest]

def signFields : List Instr :=
  signStores ++ [.ldrSp .x3 0, SignVerify.initial .x3 .digestLen]

def verifyFields : List Instr :=
  [movi .x9 0, SignVerify.initial .x9 .out, SignVerify.initial .x9 .nonce,
    SignVerify.initial .x0 .p, SignVerify.initial .x2 .pLen, SignVerify.initial .x3 .qLen,
    SignVerify.initial .x4 .signature, SignVerify.initial .x6 .digest, SignVerify.initial .x7 .digestLen]

def signStoreMem (mem : Mem) (B out key plen nonce qlen digest : Addr) : Mem :=
  ((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) out).writeW
    (off B Field.p.offset) key).writeW (off B Field.pLen.offset) plen).writeW
    (off B Field.nonce.offset) nonce).writeW (off B Field.qLen.offset) qlen).writeW
    (off B Field.digest.offset) digest

def signFieldMem (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) : Mem :=
  (signStoreMem mem B out key plen nonce qlen digest).writeW (off B Field.digestLen.offset) digestLen

def verifyFieldMem (mem : Mem) (B key plen qlen signature digest digestLen : Addr) : Mem :=
  (((((((mem.writeW (off B Field.out.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW (off B Field.p.offset) key).writeW (off B Field.pLen.offset) plen).writeW
    (off B Field.qLen.offset) qlen).writeW (off B Field.signature.offset) signature).writeW
    (off B Field.digest.offset) digest).writeW (off B Field.digestLen.offset) digestLen

theorem field_write_stack (mem : Mem) (B sp : Addr) (v : BitVec 64) (f : Field) {d Z : Nat}
    (hZ : pWorkspace ≤ Z) (hsep : ∀ i < 8, Z ≤ ofs B (off sp d + BitVec.ofNat 64 i)) :
    word (mem.writeW (off B f.offset) v) sp d = word mem sp d := by
  have hf := VG.Proof.Dsa.field_bounds f
  apply Mem.readW_congr
  intro i hi
  exact writeW_outside mem B v (Nat.le_trans hf.2 (by decide)) _ (Or.inr (Nat.le_trans (Nat.le_trans hf.2 hZ) (hsep i hi)))

theorem signFields_ok {s : State} {B sp digestLen : Addr} {Z : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = B) (hsp : s.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : InRegions (s.rd ++ s.wr) (off sp 0) 8)
    (hsep : ∀ i < 8, Z ≤ ofs B (off sp 0 + BitVec.ofNat 64 i))
    (hdl : word s.mem sp 0 = digestLen) :
    WP isa (.block signFields) s fun t =>
      t.mem = signFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
        digestLen ∧ Keep [.x3] s t := by
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold signFields
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
      u.mem = signStoreMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))
      ?_ (by decide) (by decide) (by decide +kernel)) fun u ⟨hum, hku⟩ => ?_
  · unfold signStores SignVerify.initial
    brun [h8, field_enc, hw .signature, hw .out, hw .p, hw .pLen, hw .nonce, hw .qLen, hw .digest]
    rfl
  have hstack : word u.mem sp 0 = digestLen := by
    rw [hum]
    simp only [signStoreMem, field_write_stack _ _ _ _ _ hZ hsep]
    exact hdl
  have hu8 : u.gpr .x8 = B := (hku.gpr .x8 (by decide)).trans h8
  have hru : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 0) 8 := by
    rw [hku.rd, hku.wr, hku.sp, hsp]; exact hr
  have hread : u.mem.readW u.sp 64 = digestLen := by
    rw [hku.sp, hsp, ← hstack]
    simp only [word, off, BitVec.add_zero]
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = u.mem.writeW (off B Field.digestLen.offset) digestLen)
      ?_ (by decide) (by decide) (by decide +kernel)) fun t ⟨htm, hkt⟩ => ⟨?_, (hku.trans hkt).mono (by decide)⟩
  · unfold SignVerify.initial
    brun [exec_ldrSp_arg (show 0 % 8 = 0 ∧ 0 < 32768 by decide) hru, hread, hu8, field_enc,
      (hs.congr hku.wr).st (Nat.le_trans (VG.Proof.Dsa.field_bounds .digestLen).2 hZ)]
  · rw [htm, hum]; rfl

theorem verifyFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block verifyFields) s fun t =>
      t.mem = verifyFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7) ∧
      Keep [.x9] s t := by
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold verifyFields SignVerify.initial
  brun [h8, field_enc, hw .out, hw .nonce, hw .p, hw .pLen, hw .qLen, hw .signature, hw .digest, hw .digestLen]
  rfl

end VG.Proof.Dsa.AArch64
