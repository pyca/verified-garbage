module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `AesGcm.RISCV64.OpenTo.CT`, which only this module used -/

section

/-! ### `AesGcm.RISCV64.OpenTo.Fn`, which this module and modules that import it used -/

section

/-!
# AES-GCM decryption out of place, RISC-V: the arguments and the end

Untrusted: everything here is checked by Lean. The open body out of place
(`openWithB _ true`), which `vg_aes_gcm_open_to_bitsliced` runs
(`OpenToBs.lean`): what it needs of its arguments (`openToPreR`), its
contract with the working space as a fifth stack argument
(`openToRISCV64`), and the end, which zeroes the destination if the result
is 0 (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph openResult j0 inc32 gctr decryptWith)

/-- `vg_aes_gcm_open_to(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, src = a6, len = a7, dst, dst_len, tag, tag_len,
work)`, its last five arguments on the stack: the buffers, which may not
overlap the ones it writes (`dst` and `work`), nor wrap around, an output as
long as the input, the stack below `sp` apart from them all, and `ctx` and
`work` aligned. -/
def openToPreR (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let src : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let dst : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let tag : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
  let scr : Region := ⟨stackArg s 4, 2560⟩
  s.rd = [ctx, nonce, aad, src, tag, args s 5] ∧ s.wr = [dst, scr] ∧
    ctx.Disjoint dst ∧ ctx.Disjoint scr ∧ nonce.Disjoint dst ∧ nonce.Disjoint scr ∧
    aad.Disjoint dst ∧ aad.Disjoint scr ∧ src.Disjoint dst ∧ src.Disjoint scr ∧ dst.Disjoint tag ∧
    dst.Disjoint scr ∧ dst.Disjoint (args s 5) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 5) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
    (stackArg s 4).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧
    stkOk s [ctx, nonce, aad, src, dst, tag, scr, args s 5] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 4).toNat % 8 = 0 ∧ (stackArg s 1).toNat = (s.gpr .a7).toNat

/-- The result of GCM-AD on `vg_aes_gcm_open_to`'s arguments. -/
abbrev openToRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) (stackArg s 3).toNat
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)

/-- `vg_aes_gcm_open_to`: the result in the low 32 bits of `a0`, the
plaintext or zeros at `dst`. It may leak whether it succeeds. -/
def openToRISCV64 : Contract isa where
  pre := openToPreR
  post s s' :=
    match openToRes s with
    | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (stackArg s 0) (s.gpr .a7).toNat = pt
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        bytesAt s'.mem (stackArg s 0) (s.gpr .a7).toNat = List.replicate (s.gpr .a7).toNat 0
  pub s₁ s₂ := onePub 5 s₁ s₂ ∧ (rounds (s₁.gpr .a1) → (openToRes s₁).isSome = (openToRes s₂).isSome)

/-! ## Zeroing the destination -/

/-- The `n` bytes at `D` zeroed, a byte at a time, from `t2 = D` and
`t3 = n`, with `t1 = 0`. -/
theorem wipeLoop_ok (u : State) {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (h₂ : u.gpr .t2 = D) (h₃ : u.gpr .t3 = BitVec.ofNat 64 n) (h₁ : u.gpr .t1 = 0)
    (hw : Covers [⟨D, n⟩] u.wr) :
    WP isa (.ite (.zero .t3) (.block [])
      (.loop (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) (.nonzero .t3))) u
      fun u' => Proof.Zeroize.Prefix u'.mem D n ∧ Frame [⟨D, n⟩] u.mem u'.mem ∧
        (∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp := by
  refine WP.ite (decide (n = 0)) (Steps.eval_zero_ofNat u .t3 hn h₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl,
      rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .t2 = D + BitVec.ofNat 64 i ∧
        v.gpr .t3 = BitVec.ofNat 64 (n - i) ∧ (∀ r, r ≠ .t2 → r ≠ .t3 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ Frame [⟨D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem D i) ?_ (n - 0) _
      ⟨0, rfl, by omega_using [h0], by rw [h₂]; exact (BitVec.add_zero _).symm, by rw [h₃, Nat.sub_zero],
        fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r2, r3, gv, rdv, wrv, spv, fv, pv⟩
    obtain hcn : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi])
    refine Steps.wp_sb (off := 0) (a := D + BitVec.ofNat 64 i) (by decide) (by rw [r2]; exact BitVec.add_zero _)
      (by rw [wrv]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩) fun t₁ u₁ => ?_
    refine Steps.wp_addi (imm := 1) (by decide) fun t₂ u₂ => Steps.wp_subi (imm := 1) (by decide) fun t₃ u₃ =>
      WP.block_nil ?_
    obtain z₁ : (v.gpr .t1).setWidth 8 = (0 : BitVec 8) := by rw [gv _ (by decide) (by decide), h₁]; rfl
    obtain m₃ : t₃.mem = v.mem.writeW (D + BitVec.ofNat 64 i) (0 : BitVec 8) := by
      rw [u₃.mem, u₂.mem, u₁.mem, z₁]
    obtain f' : Frame [⟨D, n⟩] u.mem t₃.mem := by
      rw [m₃]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    obtain p' : Proof.Zeroize.Prefix t₃.mem D (i + 1) := by
      rw [m₃]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega_using [hn, hi])
    obtain g' : ∀ r, r ≠ .t2 → r ≠ .t3 → t₃.gpr r = u.gpr r := fun r a b => by
      rw [u₃.other _ b, u₂.other _ a, u₁.gpr, gv r a b]
    obtain r2' : t₃.gpr .t2 = D + BitVec.ofNat 64 (i + 1) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, r2, Offset.add_add]
    obtain r3' : t₃.gpr .t3 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, r3, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
    obtain rd' : t₃.rd = u.rd := by rw [u₃.rd, u₂.rd, u₁.rd, rdv]
    obtain wr' : t₃.wr = u.wr := by rw [u₃.wr, u₂.wr, u₁.wr, wrv]
    obtain sp' : t₃.sp = u.sp := by rw [u₃.sp, u₂.sp, u₁.sp, spv]
    obtain ev := Steps.eval_nonzero_ofNat t₃ .t3 (k := n - (i + 1)) (by omega_using [hn]) r3'
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g', rd', wr', sp'⟩
    · right
      exact ⟨by rw [ev]; simp; omega_using [hi, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], r2', r3', g', rd', wr', sp',
        f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- `wipe`'s first block: the destination (the source at `W + dataO` plus the
distance at `W + dstO`) into `t2`, `len` (`s11`) into `t3`, and zero into
`t1`. -/
theorem wipeArgs_ok {s : State} {W S D : Addr} {n : Nat} (h31 : s.gpr .s0 = W) (wa : W.toNat % 8 = 0)
    (hW : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hS : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = S)
    (hδ : s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = D - S) (h23 : s.gpr .s11 = BitVec.ofNat 64 n) :
    WP isa (.block [.load .d .t2 .s0 dataO, .load .d .t3 .s0 dstO, .add .t2 .t2 .t3, mov .t3 .s11, .li .t1 0]) s
      fun s₅ => s₅.gpr .t2 = D ∧ s₅.gpr .t3 = BitVec.ofNat 64 n ∧ s₅.gpr .t1 = 0 ∧
        (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
  refine Steps.wp_ld (off := dataO) (a := W + BitVec.ofNat 64 dataO) (by decide) (by rw [h31])
    (Spill.al8 wa (by decide)) (in_off hW (by decide) (by decide)) fun s₁ u₁ => ?_
  refine Steps.wp_ld (off := dstO) (a := W + BitVec.ofNat 64 dstO) (by decide)
    (by rw [u₁.other _ (by decide), h31]) (Spill.al8 wa (by decide))
    (by rw [u₁.rd, u₁.wr]; exact in_off hW (by decide) (by decide)) fun s₂ u₂ => ?_
  refine Steps.wp_add fun s₃ u₃ => Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, by rw [u₅.gpr]; rfl, fun r a b c => ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      hS, hδ, BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]
  · rw [u₅.other _ a, u₄.other _ c, u₃.other _ b, u₂.other _ c, u₁.other _ b]
  · exact ⟨by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩

/-- `wipe`: the `len` (`s11`) bytes at the source (`W + dataO`) plus the
distance (`W + dstO`) zeroed. -/
theorem wipe_ok {s : State} {W S D : Addr} {n : Nat} (h31 : s.gpr .s0 = W) (wa : W.toNat % 8 = 0)
    (hW : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hS : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = S)
    (hδ : s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = D - S) (h23 : s.gpr .s11 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa wipe s fun u => Proof.Zeroize.Prefix u.mem D n ∧ Frame [⟨D, n⟩] s.mem u.mem ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_ok h31 wa hW hS hδ h23) fun s₅ ⟨t2, t3, t1, g, k⟩ => ?_)
  refine WP.mono (wipeLoop_ok s₅ hn hD t2 t3 t1 (by rw [k.wr]; exact hw))
    fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ⟨pz, by rw [← k.mem]; exact fu, fun r a b c => by rw [gu r b c, g r a b c],
      rdu.trans k.rd, wru.trans k.wr, spu.trans k.sp⟩

/-! ## The function -/

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM decryption out of place, RISC-V: constant time

Untrusted: everything here is checked by Lean. The pieces of the proof
`OpenToBs.lean` completes, as `vg_aes_gcm_open_bitsliced`'s, whose body's
proof (`openGoodB_ct`) serves both: the entry,
then `tag_len` (`s8`), public, and the two branches of `tagLenOk`; once the
tag length is allowed, the data is decrypted only if the tags are equal,
which may differ between two runs only as the result does (the contract's
`pub`). At the end the destination is zeroed only if the result is 0: the
addresses `wipe` computes from the slots of `W` are the destination's in
both runs (`wipeArgs_ok`), and its loop is on them.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)

theorem openToRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 3).toNat = true) :
    (openToRes t).isSome = decide (OpenTagOk t (stackArg t 2) (stackArg t 3).toNat) := by
  have e : openToRes t = if OpenTagOk t (stackArg t 2) (stackArg t 3).toNat then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (t.gpr .a0) (t.gpr .a1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat)))
        (bytesAt t.mem (t.gpr .a6) (t.gpr .a7).toNat)) else none := by
    simp only [openToRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : OpenTagOk t (stackArg t 2) (stackArg t 3).toNat
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openToRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRestAt 16 ++ ([.load .d .s8 .t1 24, .load .d .t2 .t1 0, .sub .t2 .t2 .a6,
      .store .d .t2 .s0 dstO] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem wipeArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0, .s11])
    (.block [.load .d .t2 .s0 dataO, .load .d .t3 .s0 dstO, .add .t2 .t2 .t3, mov .t3 .s11, .li .t1 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem wipeLoop_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.t2, .t3])
    (.ite (.zero .t3) (.block [])
      (.loop (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) (.nonzero .t3))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem a0Zero_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block ([] : List Instr)) h).isSome = true := ⟨_, by taint_decide⟩

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so2 {W T Dst : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO2 true W T Dst t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO2 true W T Dst t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM decryption out of place, RISC-V: reading memory only within the buffers

Untrusted: everything here is checked by Lean. The frame that allocates the
working space (`Verified.stackScratchArgs`, `OpenToBs.lean`) copies the
arguments passed on the stack, which needs the contract to read the memory
on entry only within the function's buffers (`openToPre_local`,
`openToPost_local`, `openToLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.OpenTo

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.OpenTo
open VG.Proof.AesGcm (agree_of le15 openResult_local bytesAt_congr)

/-! ## Locality -/

variable (pb : Nat)

theorem openToPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- The twelve words of `vg_aes_gcm_open_to`'s arguments, named. -/
theorem words_eq : ∀ vs : List (BitVec 64), vs.length = (Spec.Gcm.openToSig.words pb).length →
    ∃ ctx rd nonce nl aad al src len dst dl tag tl,
      vs = [ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl] := by
  intro vs hlen
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem openToPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ := words_eq pb vs hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
  exact h hr

/-- `Proof.AesGcm.openToRoundsPost` reads the memory on return only within the buffers. -/
theorem openToPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m m₁ r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tgl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToPre pb) _ m at hpre
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.openToPre, ArgWord.ofRaw, IntTy.bits] at hpre
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  have := Nat.mod_le dl.toNat (2 ^ pb)
  rw [Proof.AesGcm.bytesAt_congr (m₁ := m₁) (m₂ := m₂) (p := dst) (n := (len.setWidth pb).toNat) fun i hi =>
    agree_of hb.2.2.2.2.1 i (by
      rw [← hpre.2, BitVec.toNat_setWidth] at hi; omega_using [this, hi])]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ := words_eq pb vs hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
      (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

/-! ## With the working space as an argument -/

/-! ## With the working space on the stack -/

end VG.Proof.AesGcm.RISCV64.OpenTo
