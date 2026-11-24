module

import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
public import VerifiedGarbage.Proof.Gcm.Clmul.Ops
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.Cmac.Stream

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather

/-- Write the bit lengths in big-endian order to the last authentication block. -/
theorem shortLengths_ok {W : Addr} {al n : Nat} (s : State) (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, shortWork⟩] s.wr)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 al) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hal' : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (.block shortLengths) s fun s' =>
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 336) 16 = Proof.Gcm.lensBlock al n ∧
      Frame [⟨W + BitVec.ofNat 64 336, 16⟩] s.mem s'.mem ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v :=
  Stitch.lengthsAt_ok (offset := 336) s h19 hr h24 h26 hal' hn (by decide) (by decide) (by decide)


open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_ext8 rev64b_rev64b rev64b_read blockAt_store exec_rev64b exec_ldrq
  exec_eor exec_strq)

/-- Combine the authenticated polynomial with the encrypted initial counter and
write the resulting tag to the output pointer passed on the caller's stack. -/
theorem writeTag_ok {maskOff argOff : Nat} (maskAlign : maskOff % 16 = 0)
    (maskBound : maskOff < 65536) (argValid : argOff % 8 = 0 ∧ argOff < 32768) (s : State) (W T : Addr) (g : Spec.Gcm.Block)
    (hw : s.gpr .x19 = W) (hY : s.v .v16 = VRevOp.eval .rev64b (ext8 g g))
    (hmask : InRegions (s.rd ++ s.wr) (W+BitVec.ofNat 64 maskOff) 16)
    (hptr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 argOff) 8)
    (ht : s.mem.readW (s.sp + BitVec.ofNat 64 argOff) 64 = T) (hout : InRegions s.wr T 16) :
    WP isa (.block (writeTag maskOff argOff)) s fun t =>
      Spec.Gcm.blockAt t.mem T = g ^^^ Spec.Gcm.blockAt s.mem (W+BitVec.ofNat 64 maskOff) ∧
      Frame [⟨T,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold writeTag
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := maskOff) maskAlign maskBound ?_, ?_⟩
  · simpa only [gpr_setV, hw, BitVec.add_zero, rd_setV, wr_setV] using hmask
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrSp (off := argOff) argValid ?_, ?_⟩
  · exact hptr
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (off := 0) (by decide) (by decide) ?_, WP.block_nil ?_⟩
  · simpa only [gpr_write_self, wr_write, wr_setV, mem_setV, sp_setV,
      BitVec.add_zero, ht, BitVec.setWidth_eq] using hout
  dsimp only
  simp only [gpr_write, reduceCtorEq, ite_false, ite_true, gpr_setV, mem_write, mem_setV,
    v_write, v_setV, wr_write, wr_setV, rd_write, rd_setV, sp_write, sp_setV,
    BitVec.add_zero, hw, hY, ht, BitVec.setWidth_eq, and_true]
  refine ⟨?_, ?_⟩
  · rw [← rev64b_rev64b (s.mem.read (W+BitVec.ofNat 64 maskOff) 16), ← Stitch.rev64b_xor, blockAt_store,
      Stitch.ext8_xor, ext8_ext8, rev64b_read, ext8_ext8]
  · exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem shortTagAt_ok {k : Nat} (valid : k % 8 = 0 ∧ k < 32768) (s : State) (W T : Addr) (g : Spec.Gcm.Block)
    (hw : s.gpr .x19 = W) (hY : s.v .v16 = ext8 g g)
    (hmask : InRegions (s.rd ++ s.wr) W 16)
    (hptr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (ht : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = T) (hout : InRegions s.wr T 16) :
    WP isa (.block (shortTagAt k)) s fun t =>
      Spec.Gcm.blockAt t.mem T = g ^^^ Spec.Gcm.blockAt s.mem W ∧
      Frame [⟨T,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold shortTagAt
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev64b _ _ _, ?_⟩
  let u := s.setV .v16 (VRevOp.eval .rev64b (s.v .v16))
  have y : u.v .v16 = VRevOp.eval .rev64b (ext8 g g) := by simp only [u,v_setV,ite_true,hY]
  have out := writeTag_ok (maskOff := 0) (argOff := k) (by decide) (by decide) valid
    u W T g hw y (by simpa only [u,rd_setV,wr_setV,BitVec.add_zero] using hmask)
    hptr ht hout
  change WP isa (.block (writeTag 0 k)) u _
  simpa only [u,mem_setV,sp_setV,rd_setV,wr_setV,BitVec.add_zero] using out

theorem shortTagOut_ok (s : State) (W T : Addr) (g : Spec.Gcm.Block)
    (hw : s.gpr .x19 = W) (hY : s.v .v16 = ext8 g g)
    (hmask : InRegions (s.rd ++ s.wr) W 16)
    (hptr : InRegions (s.rd ++ s.wr) (s.sp + 384#64) 8)
    (ht : s.mem.readW (s.sp + 384#64) 64 = T) (hout : InRegions s.wr T 16) :
    WP isa (.block shortTagOut) s fun t =>
      Spec.Gcm.blockAt t.mem T = g ^^^ Spec.Gcm.blockAt s.mem W ∧
      Frame [⟨T,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  shortTagAt_ok (k := 384) (by decide) s W T g hw hY hmask hptr ht hout

open VG.Impl.AesGcm.AArch64 (ptr imm)
open VG.Proof.Gcm.AArch64 (hR dR yR nb)
open VG.Proof.Gcm.AArch64.Pmull (exec_addImm exec_movi0 exec_movz_x)
open VG.Spec.Gcm (blockAt ghashFrom blocksAt)

/-- The fixed hash block's calling convention, with the polynomial arithmetic
discharged once when the PMULL implementation is selected. -/
abbrev HashEightOk := ∀ (s : State), nb s = 8 →
    Covers ([hR s,dR s]++[yR s]) (s.rd++s.wr) → Covers [yR s] s.wr → (yR s).Disjoint (dR s) →
    WP isa (.block hashEight) s fun t =>
      let y := ghashFrom (VG.Proof.Gcm.AArch64.H₀ s) (VG.Proof.Gcm.AArch64.Y₀ s)
        (blocksAt s.mem (VG.Proof.Gcm.AArch64.dp s) 8)
      t.v .v0 = ext8 y y ∧ t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x19 = s.gpr .x19

abbrev HashEightWithOk := ∀ (s : State), nb s = 8 →
    Covers ([hR s,dR s,⟨s.gpr .x5,128⟩]++[yR s]) (s.rd++s.wr) → Covers [yR s] s.wr →
    (yR s).Disjoint (dR s) → Spec.Gcm.Powers8Repr s.mem (s.gpr .x5) (VG.Proof.Gcm.AArch64.H₀ s) →
    WP isa (.block hashEightWith) s fun t =>
      let y := ghashFrom (VG.Proof.Gcm.AArch64.H₀ s) (VG.Proof.Gcm.AArch64.Y₀ s)
        (blocksAt s.mem (VG.Proof.Gcm.AArch64.dp s) 8)
      t.v .v0 = ext8 y y ∧ t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x19 = s.gpr .x19

abbrev shortCore (cached : Bool) := if cached then hashEightWith else hashEight
abbrev CoreOk (cached : Bool) : Prop := if cached then HashEightWithOk else HashEightOk

structure ShortPowers (s : State) (W K : Addr) (size : Nat := shortWork) : Prop where
  read : Covers [⟨s.gpr .x5,128⟩] (s.rd ++ s.wr)
  apart : (⟨s.gpr .x5,128⟩ : Region).Disjoint ⟨W,size⟩
  repr : Spec.Gcm.Powers8Repr s.mem (s.gpr .x5) (blockAt s.mem (K+240#64))

theorem ShortPowers.frame {s t : State} {W K : Addr} {r : Region} {size : Nat} (p : ShortPowers s W K size)
    (fr : Frame [r] s.mem t.mem) (sub : r.Sub ⟨W,size⟩)
    (key : (⟨K+240#64,16⟩ : Region).Disjoint r) (reg : t.gpr .x5 = s.gpr .x5)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : ShortPowers t W K size := by
  refine ⟨by rw [reg,rd,wr]; exact p.read, by rw [reg]; exact p.apart, ?_⟩
  rw [reg,blockAt_frame fr (by simpa only [List.mem_singleton,forall_eq] using key)]
  exact Proof.AesGcm.powers8Repr_congr (fun i hi => fr.bytes (R := ⟨s.gpr .x5,128⟩)
    (by simpa only [List.mem_singleton,forall_eq] using p.apart.sub_right sub) (by change (128 : Nat) ≤ 2^64; decide) hi) p.repr

/-- GHASH the eight authentication blocks after clearing the accumulator in
the adjacent scratch slot. This leaves all eight input blocks intact. -/
theorem shortHashWith_ok {cached : Bool} (hash : CoreOk cached) (s : State) (W K : Addr) (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = K)
    (hwork : Covers [⟨W, shortWork⟩] s.wr)
    (hctx : Covers [⟨K+240#64,16⟩] (s.rd ++ s.wr))
    (hsep : Region.Disjoint ⟨K+240#64,16⟩ ⟨W+352#64,16⟩)
    (powers : cached = true → ShortPowers s W K) :
    WP isa (.block (shortHashWith authO (shortCore cached))) s fun t =>
      let g := ghashFrom (blockAt s.mem (K+240#64)) 0 (blocksAt s.mem (W+224#64) 8)
      t.v .v16 = ext8 g g ∧ Frame [⟨W+352#64,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold shortHashWith
  rw [WP.block_append_iff, WP.block_append_iff]
  let setup : List Instr := [ptr .x0 .x21 240, ptr .x1 .x19 (authO+128), .vop (.movi0 .v0),
    .strq .v0 .x1 0, ptr .x2 .x19 authO, imm .x3 8]
  have init : ∃ u, runBlock isa setup s = some u ∧ u.gpr .x0 = K+240#64 ∧
      u.gpr .x1 = W+352#64 ∧ u.gpr .x2 = W+224#64 ∧ u.gpr .x3 = 8#64 ∧
      u.mem = s.mem.write (W+352#64) 16 0 ∧ u.gpr .x19 = W ∧ u.gpr .x5 = s.gpr .x5 ∧
      u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
    have hw := in_off (d := 352) (n := 16) hwork (by decide) (by decide)
    refine ⟨_, by
      simp only [setup, ptr, imm, authO, runBlock_cons]
      rw [exec_addImm (by decide) _, runStep_some, runBlock_cons, exec_addImm (by decide) _, runStep_some, runBlock_cons,
        exec_movi0, runStep_some, runBlock_cons, exec_strq (by decide) (by decide) ?_, runStep_some, runBlock_cons,
        exec_addImm (by decide) _, runStep_some, runBlock_cons, exec_movz_x (by decide) _, runStep_some]
      · rfl
      · simpa only [wr_setV, wr_write, gpr_setV, gpr_write, reduceCtorEq, ite_true, ite_false,
          BitVec.setWidth_eq, BitVec.add_zero, h19] using hw, ?_⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, gpr_setV, h21,
        h19, mem_setV, mem_write, v_setV_self, sp_write, sp_setV, rd_write, rd_setV, wr_write,
        wr_setV, BitVec.add_zero, and_self]
    decide
  obtain ⟨u, run, u0, u1, u2, u3, um, u19, u5, usp, urd, uwr⟩ := init
  refine WP.of_runBlock ⟨u, run, ?_⟩
  have un : nb u = 8 := by unfold nb; rw [u3]; rfl
  have uh : hR u = ⟨K+240#64,16⟩ := congrArg (fun b => Region.mk b 16) u0
  have uy : yR u = ⟨W+352#64,16⟩ := congrArg (fun b => Region.mk b 16) u1
  have ud : dR u = ⟨W+224#64,128⟩ := by change (Region.mk _ (16 * nb u)) = _; rw [un]; exact congrArg (fun b => Region.mk b 128) u2
  have yc : Covers [yR u] u.wr := by rw [uy, uwr]; exact covers_off hwork (by decide) (by decide)
  have dc : Covers [dR u] u.wr := by rw [ud, uwr]; exact covers_off hwork (by decide) (by decide)
  have hc : Covers [hR u] (u.rd ++ u.wr) := by rwa [uh, urd, uwr]
  have sep : (yR u).Disjoint (dR u) := by rw [uy, ud]; exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have fr : Frame [⟨W+352#64,16⟩] s.mem u.mem := by
    rw [um]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hashVal : ghashFrom (VG.Proof.Gcm.AArch64.H₀ u) (VG.Proof.Gcm.AArch64.Y₀ u) (blocksAt u.mem (VG.Proof.Gcm.AArch64.dp u) 8) = ghashFrom (blockAt s.mem (K+240#64)) 0 (blocksAt s.mem (W+224#64) 8) := by
    change ghashFrom (blockAt u.mem _) (blockAt u.mem _) (blocksAt u.mem _ 8) = _
    rw [show VG.Proof.Gcm.AArch64.hA u = _ from u0, show VG.Proof.Gcm.AArch64.yp u = _ from u1,
      show VG.Proof.Gcm.AArch64.dp u = _ from u2]
    congr 1
    · exact blockAt_frame fr (by simpa only [List.mem_singleton, forall_eq] using hsep)
    · rw [um]; exact blockAt_store s.mem (W+352#64) 0
    · exact blocksAt_frame fr (by simpa only [List.mem_singleton, forall_eq, ← ud, ← uy] using sep.symm) (by decide)
  have folded : WP isa (.block (shortCore cached)) u fun t =>
      let val := ghashFrom (VG.Proof.Gcm.AArch64.H₀ u) (VG.Proof.Gcm.AArch64.Y₀ u) (blocksAt u.mem (VG.Proof.Gcm.AArch64.dp u) 8)
      t.v .v0 = ext8 val val ∧ t.mem = u.mem ∧ t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.gpr .x19 = u.gpr .x19 := by
    cases cached with
    | false => exact hash u un (Covers.append_left (Covers.cons hc (Covers.right dc)) (Covers.right yc)) yc sep
    | true =>
      have pc := (powers rfl).frame fr (Offset.sub_base _ (by decide)) hsep u5 urd uwr
      have repr : Spec.Gcm.Powers8Repr u.mem (u.gpr .x5) (VG.Proof.Gcm.AArch64.H₀ u) := by
        change Spec.Gcm.Powers8Repr u.mem (u.gpr .x5) (blockAt u.mem (u.gpr .x0)); rw [u0]; exact pc.repr
      exact hash u un (Covers.append_left (Covers.cons hc (Covers.cons (Covers.right dc) pc.read)) (Covers.right yc)) yc sep repr
  refine folded.mono ?_
  intro v hv
  obtain ⟨v0, vm, vsp, vrd, vwr, v19⟩ := hv
  rw [WP.block_cons_iff]
  refine ⟨v.setV .v16 (v.v .v0 ||| v.v .v0), rfl, WP.block_nil ?_⟩
  simp only [v_setV_self, BitVec.or_self, v0, hashVal, mem_setV, vm, fr, gpr_setV, v19, u19, sp_setV, vsp,
    usp, rd_setV, vrd, urd, wr_setV, vwr, uwr, and_self]

theorem shortHash_ok (hash : HashEightOk) (s : State) (W K : Addr) (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = K)
    (hwork : Covers [⟨W, shortWork⟩] s.wr)
    (hctx : Covers [⟨K+240#64,16⟩] (s.rd ++ s.wr))
    (hsep : Region.Disjoint ⟨K+240#64,16⟩ ⟨W+352#64,16⟩) :
    WP isa (.block (shortHash authO)) s fun t =>
      let g := ghashFrom (blockAt s.mem (K+240#64)) 0 (blocksAt s.mem (W+224#64) 8)
      t.v .v16 = ext8 g g ∧ Frame [⟨W+352#64,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  shortHashWith_ok (cached := false) hash s W K h19 h21 hwork hctx hsep (by intro e; cases e)

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The short path's fixed input to GHASH contains leading zero blocks and
one padded block for AAD, including when the AAD is empty. Relate the tag
formed from this input and the first AES output to the gather postcondition. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (lensBlock)

/-- The description shared by the gather and contiguous bounded records.
The plaintext comes from the original caller's memory. -/
structure ShortOutput where
  dst : Addr
  len : Addr
  tag : Addr
  plain : List Byte

abbrev ShortOutput.gather (s : State) : ShortOutput := ⟨Dst s,stackArg s 1,Tg s,pt s (Cnt s)⟩

abbrev ShortOutput.post (d : ShortOutput) (s t : State) : Prop :=
  encryptWith (ctxCiph s.mem (K s) (s.gpr .x1).toNat) (ctxH s.mem (K s)) 16
    (bytesAt s.mem (Nn s) (NL s)) d.plain (bytesAt s.mem (Ad s) (AL s)) =
    (bytesAt t.mem d.dst d.len.toNat,bytesAt t.mem d.tag 16)

theorem record_post_of_blocks (k : Nat) (s t : State) (d : ShortOutput) (work : Mem) (auth : Addr) (lead : Nat)
    :
    let a := bytesAt s.mem (Ad s) (AL s)
    let iv := bytesAt s.mem (Nn s) (NL s)
    let cipher := ctxCiph s.mem (K s) (s.gpr .x1).toNat
    let H := ctxH s.mem (K s)
    let ct := bytesAt t.mem d.dst d.len.toNat
    a.length ≤ 16 →
    ct = gctr cipher (inc32 (j0 H iv)) d.plain →
    bytesAt work auth (16*k) = zeros (16 * lead) ++ a ++ zeros (16 - a.length) ++ ct ++
      zeros (padLen ct.length) ++ lensBlock a.length ct.length →
    bytesAt t.mem d.tag 16 = toBytes (ghashFrom H 0 (blocksAt work auth k) ^^^ cipher (j0 H iv)) →
    d.post s t := by
  dsimp only
  intro hlen hct hbuf htag
  rw [Proof.Gcm.blocksAt_eq, hbuf, Proof.Gcm.ghash_lead _ _ hlen] at htag
  unfold ShortOutput.post encryptWith
  rw [← hct]
  dsimp only
  rw [Proof.Gcm.fullTag_eq, List.take_of_length_le (by rw [Proof.Cmac.toBytes_length]), htag]

theorem gather_post_of_blocks (k : Nat) (s t : State) (work : Mem) (auth : Addr) (lead : Nat)
    :
    let a := bytesAt s.mem (Ad s) (AL s)
    let iv := bytesAt s.mem (Nn s) (NL s)
    let cipher := ctxCiph s.mem (K s) (s.gpr .x1).toNat
    let H := ctxH s.mem (K s)
    let ct := bytesAt t.mem (Dst s) (L s)
    a.length ≤ 16 →
    ct = gctr cipher (inc32 (j0 H iv)) (pt s (Cnt s)) →
    bytesAt work auth (16*k) = zeros (16 * lead) ++ a ++ zeros (16 - a.length) ++ ct ++
      zeros (padLen ct.length) ++ lensBlock a.length ct.length →
    bytesAt t.mem (Tg s) 16 = toBytes (ghashFrom H 0 (blocksAt work auth k) ^^^ cipher (j0 H iv)) →
    gatherPost s t :=
  record_post_of_blocks k s t (.gather s) work auth lead

end VG.Proof.AesGcm.AArch64.DirectGather

/-! After the last descriptor has been sealed, the padded AAD and ciphertext
occupy seven blocks. Write the lengths, authenticate, return the tag, and
restore the caller's saved registers. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph inc32 j0 gctr blockAt blocksAt ghashFrom padLen zeros toBytes)

abbrev shortCipher (o : State) := ctxCiph o.mem (K o) (o.gpr .x1).toNat
abbrev shortJ0 (o : State) := j0 (ctxH o.mem (K o)) (bytesAt o.mem (Nn o) (NL o))
abbrev shortAadBytes (o : State) := bytesAt o.mem (Ad o) (AL o)
abbrev shortCt (o s : State) := bytesAt s.mem (Dst o) (L o)

/-- Facts at exit from the descriptor loop. The seven filled blocks precede
the length block and the GHASH accumulator in the short workspace. -/
structure ShortFinishPreFor (o s : State) (W : Addr) (lead : Nat) (d : ShortOutput) (tagOff : Nat) : Prop where
  x19 : s.gpr .x19 = W
  x21 : s.gpr .x21 = K o
  x24 : s.gpr .x24 = BitVec.ofNat 64 (AL o)
  x26 : s.gpr .x26 = BitVec.ofNat 64 d.len.toNat
  sp : s.sp = W
  saved : SavedAt s.mem W o
  work : Covers [⟨W,shortWork⟩] s.wr
  key : Covers [⟨K o+240#64,16⟩] (s.rd ++ s.wr)
  ptr : InRegions (s.rd ++ s.wr) (W+BitVec.ofNat 64 tagOff) 8
  tag : InRegions s.wr (d.tag) 16
  tagAddr : s.mem.readW (W+BitVec.ofNat 64 tagOff) 64 = d.tag
  keyWork : Region.Disjoint ⟨K o+240#64,16⟩ ⟨W,shortWork⟩
  dstWork : ((⟨d.dst,d.len.toNat⟩ : Region)).Disjoint ⟨W,shortWork⟩
  tagWork : ((⟨d.tag,16⟩ : Region)).Disjoint ⟨W,shortWork⟩
  dstTag : ((⟨d.dst,d.len.toNat⟩ : Region)).Disjoint ((⟨d.tag,16⟩ : Region))
  shortAad : AL o ≤ 16
  hashKey : blockAt s.mem (K o+240#64) = ctxH o.mem (K o)
  mask : blockAt s.mem W = shortCipher o (shortJ0 o)
  ct : (bytesAt s.mem d.dst d.len.toNat) = gctr (shortCipher o) (inc32 (shortJ0 o)) d.plain
  auth : bytesAt s.mem (W+224#64) 112 = zeros (16*lead) ++ shortAadBytes o ++ zeros (16-AL o) ++
    (bytesAt s.mem d.dst d.len.toNat) ++ zeros (padLen d.len.toNat)

abbrev ShortFinishPre (o s : State) (W : Addr) (lead : Nat) :=
  ShortFinishPreFor o s W lead (.gather o) 384

theorem singletonFrame {r : Region} {rs : List Region} {m m' : Mem}
    (h : Frame [r] m m') {r' : Region} (hr : r' ∈ rs) (hs : Region.Sub r r') : Frame rs m m' :=
  h.sub fun q hq => by rw [List.mem_singleton.mp hq]; exact ⟨r', hr, hs⟩

/-- The end of the short body meets the public gather postcondition and
restores the registers saved at entry, keeping the short frame allocated. -/
theorem shortFinishUsing_ok {cached : Bool} {d : ShortOutput} {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) (hash : CoreOk cached) (o s : State) (W : Addr) (lead : Nat) (p : ShortFinishPreFor o s W lead d tagOff) (powers : cached = true → ShortPowers s W (K o)) :
    WP isa (.block (shortLengths ++ shortHashWith authO (shortCore cached) ++ shortTagAt tagOff ++ Impl.AesGcm.AArch64.restore)) s fun t =>
      d.post o t ∧ (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ t.sp = W ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨W,shortWork⟩, (⟨d.tag,16⟩ : Region)] s.mem t.mem := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine (shortLengths_ok s p.x19 p.work p.x24 p.x26 (o.gpr .x5).isLt d.len.isLt).mono ?_
  intro l pl
  obtain ⟨lens, lf, regs, lsp, lrd, lwr, _⟩ := pl
  have lw : Covers [⟨W,shortWork⟩] l.wr := lwr ▸ p.work
  have lh : Covers [⟨K o+240#64,16⟩] (l.rd ++ l.wr) := by rw [lrd,lwr]; exact p.key
  have subL : Region.Sub ⟨W+336#64,16⟩ ⟨W,shortWork⟩ := Offset.sub_base _ (by decide)
  have subY : Region.Sub ⟨W+352#64,16⟩ ⟨W,shortWork⟩ := Offset.sub_base _ (by decide)
  refine (shortHashWith_ok hash l W (K o) ((regs _ (by decide)).trans p.x19) ((regs _ (by decide)).trans p.x21)
    lw lh (p.keyWork.sub_right subY) (fun h => (powers h).frame lf subL (p.keyWork.sub_right subL)
      (regs .x5 (by decide)) lrd lwr)).mono ?_
  intro h ph
  obtain ⟨hash, hf, hx, hsp, hrd, hwr⟩ := ph
  have subWork : Frame [⟨W,shortWork⟩] s.mem h.mem :=
    (singletonFrame lf (List.mem_singleton_self _) subL).trans (singletonFrame hf (List.mem_singleton_self _) subY)
  have ptrRead : h.mem.readW (W+BitVec.ofNat 64 tagOff) 64 = d.tag := by
    rw [subWork.readW (r := ⟨W+BitVec.ofNat 64 tagOff,8⟩) (Region.contains_self _ _) (by
      simpa only [List.mem_singleton, forall_eq] using Offset.disjoint_base W (d := tagOff) (n := 8)
        (k := shortWork) (by rcases off with rfl|rfl <;> decide) (by rcases off with rfl|rfl <;> decide)) (by decide), p.tagAddr]
  have hspW := hsp.trans (lsp.trans p.sp)
  have mask0 : InRegions (h.rd ++ h.wr) W 16 := by
    rw [hrd,hwr,lrd,lwr]
    simpa only [BitVec.add_zero] using in_left (rd := s.rd) (in_off (d := 0) (n := 16) p.work (by decide) (by decide))
  refine (shortTagAt_ok (k := tagOff) (by rcases off with rfl|rfl <;> decide) h W (d.tag) _ hx hash mask0 (by rw [hspW,hrd,hwr,lrd,lwr]; exact p.ptr)
    (by rwa [hspW]) (by rw [hwr,lwr]; exact p.tag)).mono ?_
  intro t tt
  obtain ⟨tag, tf, tx, tsp, trd, twr⟩ := tt
  have sfL := p.saved.frame lf (by simpa only [List.mem_singleton, forall_eq] using Offset.disjoint W (d := 128) (n := 88) (e := 336) (k := 16) (.inl (by decide)) (by decide) (by decide))
  have sfH := sfL.frame hf (by simpa only [List.mem_singleton, forall_eq] using Offset.disjoint W (d := 128) (n := 88) (e := 352) (k := 16) (.inl (by decide)) (by decide) (by decide))
  have sf := sfH.frame tf (by simpa only [List.mem_singleton, forall_eq] using p.tagWork.symm.sub_left (Offset.sub_base W (d := 128) (n := 88) (by decide)))
  refine (exit_ok (s₀ := {o with sp := W}) tx (tsp.trans hspW) (Covers.right (by
    rw [twr,hwr,lwr]; exact p.work)) sf (by decide)).mono ?_
  intro z hz
  obtain ⟨abi, zm, _, zrd, zwr⟩ := hz
  have f : Frame [⟨W,shortWork⟩, (⟨d.tag,16⟩ : Region)] s.mem z.mem := by
    rw [zm]
    exact (singletonFrame subWork (List.mem_cons_self ..) (fun _ => id)).trans
      (singletonFrame tf (by simp) (fun _ => id))
  have zct : (bytesAt z.mem d.dst d.len.toNat) = (bytesAt s.mem d.dst d.len.toNat) := bytesAt_frame f (by
    intro r hr; rcases List.mem_cons.mp hr with e | e
    · exact e ▸ p.dstWork
    · exact (List.mem_singleton.mp e) ▸ p.dstTag)
    (Nat.le_of_lt d.len.isLt)
  refine ⟨record_post_of_blocks 8 o z d l.mem (W+224#64) lead ?_ (zct.trans p.ct) ?_ ?_, abi.1, abi.2,
    zrd.trans (trd.trans (hrd.trans lrd)), zwr.trans (twr.trans (hwr.trans lwr)), f⟩
  · simpa only [Proof.Cmac.bytesAt_length] using p.shortAad
  · change _ = _ ++ shortAadBytes o ++ _ ++ (bytesAt z.mem d.dst d.len.toNat) ++ _ ++ _
    rw [zct, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length,
      show (16*8:Nat) = 112+16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add, lens,
      bytesAt_frame lf (by simpa only [List.mem_singleton, forall_eq] using Offset.disjoint W (d := 224) (n := 112) (e := 336) (k := 16) (.inl (by decide)) (by decide) (by decide))
        (by decide), p.auth]
  · have hkey : blockAt l.mem (K o+240#64) = ctxH o.mem (K o) :=
      (blockAt_frame lf (by simpa only [List.mem_singleton, forall_eq] using p.keyWork.sub_right subL)).trans p.hashKey
    have hmask : blockAt h.mem W = shortCipher o (shortJ0 o) := by
      rw [blockAt_frame hf (by simpa only [List.mem_singleton, forall_eq] using Offset.base_disjoint W (k := 16) (e := 352) (n := 16) (by decide) (by decide)),
        blockAt_frame lf (by simpa only [List.mem_singleton, forall_eq] using Offset.base_disjoint W (k := 16) (e := 336) (n := 16) (by decide) (by decide)), p.mask]
    rw [zm, Proof.Cmac.bytesAt_blockAt, tag, hkey, hmask]

theorem shortFinishAt_ok {d : ShortOutput} {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) (hash : HashEightOk) (o s : State) (W : Addr) (lead : Nat) (p : ShortFinishPreFor o s W lead d tagOff) :
    WP isa (.block (shortLengths ++ shortHash authO ++ shortTagAt tagOff ++ Impl.AesGcm.AArch64.restore)) s fun t =>
      d.post o t ∧ (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ t.sp = W ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨W,shortWork⟩, (⟨d.tag,16⟩ : Region)] s.mem t.mem :=
  shortFinishUsing_ok (cached := false) off hash o s W lead p (by intro e; cases e)

theorem shortFinish_ok (hash : HashEightOk) (o s : State) (W : Addr) (lead : Nat) (p : ShortFinishPre o s W lead) :
    WP isa (.block (shortLengths ++ shortHash authO ++ shortTagOut ++ Impl.AesGcm.AArch64.restore)) s fun t =>
      gatherPost o t ∧ (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ t.sp = W ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨W,shortWork⟩, tgR o] s.mem t.mem :=
  shortFinishAt_ok (.inr rfl) hash o s W lead p

end VG.Proof.AesGcm.AArch64.DirectGather
