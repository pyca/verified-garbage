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
# AES-GCM decryption out of place, RISC-V: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` is
`vg_aes_gcm_open`'s body out of place (`openWith true`): its contract with
the working space as a fifth stack argument (`openToRISCV64`), the entry,
which also keeps the distance from the source to the destination at
`W + dstO` (`openToEntry_wp`), the body (`open_body`, `Open.lean`, with the
destination the first stack argument), and the end, which zeroes the
destination if the result is 0 (`wipe_ok`) and restores our caller's
registers (`openTo_wp`).
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

/-- What the body needs of `vg_aes_gcm_open_to`'s arguments. -/
theorem openToPreR.opre {s₀ : State} (h : openToPreR s₀) :
    OPre true s₀ (stackArg s₀ 4) (stackArg s₀ 2) (stackArg s₀ 0) (stackArg s₀ 3).toNat := by
  obtain ⟨hrd, hwr, dcD, dcW, dnD, dnW, daD, daW, dsD, dsW, dDT, dDW, dDA, dtW, dWA, fc, fn, fa, fs, fD, ft, fW, fsp,
    hR, hstk, ca, wa, dl⟩ := h
  obtain mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  obtain hD : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₀.wr := by
    rw [hwr, ← dl]; exact covers_mem (List.mem_cons_self ..)
  obtain hb : ∀ r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
      ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩,
      ⟨stackArg s₀ 2, (stackArg s₀ 3).toNat⟩, ⟨stackArg s₀ 4, 2560⟩], r.Disjoint (below s₀.sp 2048) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain m : ∀ {x : Region}, x ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
        ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨stackArg s₀ 0, (stackArg s₀ 1).toNat⟩,
        ⟨stackArg s₀ 2, (stackArg s₀ 3).toNat⟩, ⟨stackArg s₀ 4, 2560⟩, args s₀ 5] →
        x.Disjoint (below s₀.sp 2048) := fun hx => hstk.buf hx
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m (.head _)
    · exact m (.tail _ (.head _))
    · exact m (.tail _ (.tail _ (.head _)))
    · exact m (.tail _ (.tail _ (.tail _ (.head _))))
    · rw [← dl]; exact m (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · exact m (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    · exact m (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  rw [dl] at dcD dsD dDW fD
  exact ⟨mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp),
    mr (by rw [hrd]; simp), by rw [hwr]; exact covers_mem (by simp), hD, dcW, dnW, daW, dsW, dtW, dDW, dcD, fc,
    fn, fa, fs, fD, fW, (stackArg s₀ 3).isLt, hb, hstk.1, hstk.2.1,
    hR, ca, wa, dsD⟩

/-- The entry of `vg_aes_gcm_open_to`: `oneEntryAt 32 16`, `tag_len` into
`s8`, and `dst - src` into `W + dstO`. -/
theorem openToEntry_wp {s₀ : State} (h : openToPreR s₀) :
    WP isa (.block (openEntryWith true)) s₀ fun s₂ =>
      SO2 true (stackArg s₀ 4) (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 3 := by
  obtain ⟨hrd, hwr, dcD, dcW, dnD, dnW, daD, daW, dsD, dsW, dDT, dDW, dDA, dtW, dWA, fc, fn, fa, fs, fD, ft, fW, fsp,
    hR, hstk, ca, wa, dl⟩ := h
  obtain hW : Covers [⟨stackArg s₀ 4, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 5] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain ain : ∀ i < 5, InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * i)) 8 := fun i hi => by
    have := in_off hA (d := 8 * i) (n := 8) (by omega_using [hi]) (by omega_using [])
    rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this
  obtain dA : (args s₀ 5).Disjoint (oneR (stackArg s₀ 4)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  obtain dAi : ∀ i < 5, (⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (oneR (stackArg s₀ 4)) :=
    fun i hi => by
      obtain hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8 * i) (n := 8) (k := 40) (by omega_using [hi])
      rw [add_ofNat_assoc, Nat.zero_add] at hs
      exact dA.sub_left hs
  obtain spa : s₀.sp.toNat % 8 = 0 := by have := hstk.1; omega_using [this]
  simp only [openEntryWith, openEntryWithB, ↓reduceIte, Bool.false_eq_true]
  refine WP.block_append (WP.mono (WP.keep [.t1, .s0, .s1, .s2, .s3, .s4, .s5, .s7, .s9, .s10, .s11]
    (one1At_wp (off := 32) (tagO := 16) (W := stackArg s₀ 4) (T := stackArg s₀ 2) (.inr (.inr rfl)) (.inr rfl) hW
      wa hstk.1 (ain 4 (by decide)) rfl (ain 2 (by decide)) rfl (dAi 2 (by decide))) (by rfl) rfl)
    fun s₁ ⟨h1, kp⟩ => ?_)
  have hk₁ := h1.keeps
  obtain hv : ∀ i < 5, s₁.mem.readW (s₀.sp + BitVec.ofNat 64 (8 * i)) 64 = stackArg s₀ i := fun i hi => by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAi i hi) (by decide)]
    rfl
  obtain hv3 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 24) 64 = stackArg s₀ 3 := hv 3 (by decide)
  obtain hv0 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = stackArg s₀ 0 := hv 0 (by decide)
  obtain in3 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 24) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 3 (by decide)
  obtain in0 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 0 (by decide)
  refine Steps.wp_ld (off := 24) (a := s₀.sp + BitVec.ofNat 64 24) (by decide) (by rw [h1.t1])
    (Spill.al8 spa (by decide)) in3 fun s₂ u₂ => ?_
  refine Steps.wp_ld (off := 0) (a := s₀.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [u₂.other _ (by decide), h1.t1]) (Spill.al8 spa (by decide)) (by rw [u₂.rd, u₂.wr]; exact in0)
    fun s₃ u₃ => ?_
  refine Steps.wp_sub fun s₄ u₄ => ?_
  obtain e0 : s₄.gpr .s0 = stackArg s₀ 4 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h1.s0]
  refine Steps.wp_sd (off := dstO) (a := stackArg s₀ 4 + BitVec.ofNat 64 dstO) (by decide) (by rw [e0])
    (Spill.al8 wa (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, hk₁.wr]; exact in_off hW (show dstO + 8 ≤ 2560 by decide) (by decide))
    fun s₅ m₅ => WP.block_nil ?_
  obtain t2 : s₄.gpr .t2 = stackArg s₀ 0 - s₀.gpr .a6 := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), kp.gpr (by decide), u₂.mem, hv0]
  obtain mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain hm : s₅.mem = s₁.mem.writeW (stackArg s₀ 4 + BitVec.ofNat 64 dstO) (stackArg s₀ 0 - s₀.gpr .a6) := by
    rw [m₅.mem, t2, mem₄]
  obtain g : ∀ r, r ≠ .s8 → r ≠ .t2 → s₅.gpr r = s₁.gpr r := fun r h8 h2 => by
    rw [m₅.gpr, u₄.other r h2, u₃.other r h2, u₂.other r h8]
  obtain dS : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 248 →
      (⟨stackArg s₀ 4 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint ⟨stackArg s₀ 4 + BitVec.ofNat 64 dstO, 8⟩ :=
    fun h₁ h₂ => Lay.w_w (.inl (by unfold dstO; omega_using [h₂])) (by omega_using [h₂]) (by decide)
  refine ⟨⟨⟨by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, hk₁.rd], by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, hk₁.wr],
      by rw [m₅.sp, u₄.sp, u₃.sp, u₂.sp, hk₁.sp]⟩, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · rw [hm]
    exact h1.saved.frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  · rw [hm]
    exact (h1.frame.sub inW_one).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))
  · rw [hm, Mem.readW_writeW_sep (Region.Disjoint.sep (dS (by decide) (by decide)) (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide)]
    exact h1.aad
  · rw [hm, Mem.readW_writeW_sep (Region.Disjoint.sep (dS (by decide) (by decide)) (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide)]
    exact h1.dat
  · rw [hm, Mem.readW_writeW_self64]
  · rw [g _ (by decide) (by decide)]; exact h1.s0
  · rw [g _ (by decide) (by decide)]; exact h1.s1
  · rw [g _ (by decide) (by decide)]; exact h1.s2
  · rw [g _ (by decide) (by decide)]; exact h1.s3
  · rw [g _ (by decide) (by decide)]; exact h1.s4
  · rw [g _ (by decide) (by decide)]; exact h1.s5
  · rw [g _ (by decide) (by decide)]; exact h1.s7
  · rw [g _ (by decide) (by decide)]; exact h1.s10
  · rw [g _ (by decide) (by decide)]; exact h1.s11
  · rw [g _ (by decide) (by decide)]; exact h1.s9
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hv3]

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

theorem openTo_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : openToRISCV64.pre s₀) :
    WP isa OpenTo.openTo s₀ fun s' => abiPreserved s₀ s' ∧ openToRISCV64.post s₀ s' := by
  have h' : openToPreR s₀ := h
  have hp := h'.opre
  have hW : Covers [⟨stackArg s₀ 4, 2560⟩] s₀.wr := hp.w
  unfold OpenTo.openTo openWith
  refine WP.seq (WP.mono (openToEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  refine open_body hp h2 (by rw [h19]; simp) fun s₅ br => ?_
  obtain hres : openToRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧
      OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat then
      some (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)) else none := by
    simp only [openToRes, openResult, decryptWith]
    by_cases hl : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true
    · simp only [hl, ite_true, true_and]
    · simp only [hl, false_and, ite_false, Bool.false_eq_true]
  show WP isa (.seq (.ite (.zero .a0) wipe (.block [])) (.block restore)) s₅ _
  obtain hW₅ : Covers [⟨stackArg s₀ 4, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [br.rd, br.wr]; exact Covers.right hW
  -- the destination zeroed if the result is 0
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => s₆.gpr .s0 = stackArg s₀ 4 ∧ s₆.sp = s₀.sp ∧ s₆.rd = s₀.rd ∧
      s₆.wr = s₀.wr ∧ SavedAt s₆.mem (stackArg s₀ 4) s₀ ∧ s₆.gpr .a0 = s₅.gpr .a0 ∧
      (Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat →
        bytesAt s₆.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat = bytesAt s₅.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat) ∧
      (¬(Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat) →
        bytesAt s₆.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat = List.replicate (s₀.gpr .a7).toNat 0)) ?_
    fun s₆ ⟨h31, hsp, hrd, hwr, hsv, ha0, hg, hb⟩ => ?_)
  · by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat
    · refine WP.ite false (by rw [Steps.eval_zero, (br.good hx).1]; rfl) (fun hf => absurd hf (by decide))
        (fun _ => WP.block_nil ⟨br.s0, br.sp, br.rd, br.wr, br.saved, rfl, fun _ => rfl, fun hn => absurd hx hn⟩)
    · refine WP.ite true (by rw [Steps.eval_zero, (br.bad hx).1]; rfl) (fun _ => ?_) (fun hf => absurd hf (by decide))
      obtain hdw : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₅.wr := by rw [br.wr]; exact hp.dst
      refine WP.mono (wipe_ok (S := s₀.gpr .a6) br.s0 hp.wa hW₅ br.dat (br.dst rfl) (by rw [br.s11]; simp)
        (s₀.gpr .a7).isLt hp.fD hdw) fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ?_
      obtain g0 : u.gpr .s0 = stackArg s₀ 4 := by rw [gu _ (by decide) (by decide) (by decide)]; exact br.s0
      obtain ga : u.gpr .a0 = s₅.gpr .a0 := gu _ (by decide) (by decide) (by decide)
      obtain sv : SavedAt u.mem (stackArg s₀ 4) s₀ := br.saved.frame fu fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dDW.sub_right (Lay.wSub (d := 128) (n := 104) (by decide))).symm
      exact ⟨g0, spu.trans br.sp, rdu.trans br.rd, wru.trans br.wr, sv, ga, fun hn => absurd hn hx,
        fun _ => bytesAt_zeros pz⟩
  · refine WP.mono (restore_ok h31 hp.wa (by rw [hrd, hwr]; exact Covers.right hW) hsv hsp)
      fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, ?_⟩
    unfold openToRISCV64
    dsimp only
    rw [hm, h3, ha0]
    by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat
    · rw [hres, ite_eq_left_of_eq_true _ _ (eq_true hx)]
      exact ⟨by rw [(br.good hx).1]; rfl, (hg hx).trans (br.good hx).2⟩
    · rw [hres, ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact ⟨by rw [(br.bad hx).1]; rfl, hb hx⟩

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM decryption out of place, RISC-V: constant time

Untrusted: everything here is checked by Lean. As `vg_aes_gcm_open`'s
(`CTOpen.lean`), whose body's proof (`openGood_ct`) serves both: the entry,
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

theorem openToHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 32]) h).isSome = true := ⟨_, by taint_decide⟩

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

/-- The head of `vg_aes_gcm_open_to`'s entry: `W`, at `sp + 32`, into `t1`. -/
theorem oneA32_ok {s₀ : State} {W : Addr} (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 32) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 32) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 32]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := 32) (a := s₀.sp + BitVec.ofNat 64 32) (by decide) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega_using [hsa]) (by decide)) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem openTo_one {t₀ s : State} (h : openToPreR t₀)
    (h1 : SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s) (h19 : s.gpr .s8 = stackArg t₀ 3) :
    OneO true (t₀.gpr .a0) (stackArg t₀ 4) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 2) (stackArg t₀ 3) (stackArg t₀ 0) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat := by
  have hp := h.opre
  have hk₀ := hp.stk
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hN : DataOk (stackArg t₀ 4 + BitVec.ofNat 64 16) (stackArg t₀ 4) s (t₀.gpr .a2) (t₀.gpr .a3).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.nonce, (t₀.gpr .a3).isLt, hp.fn, hp.dnW.sub_right (Lay.wSub (by decide)),
      hp.dnW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hA : DataOk (stackArg t₀ 4 + BitVec.ofNat 64 16) (stackArg t₀ 4) s (t₀.gpr .a4) (t₀.gpr .a5).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.aad, (t₀.gpr .a5).isLt, hp.fa, hp.daW.sub_right (Lay.wSub (by decide)),
      hp.daW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hT : Covers [⟨stackArg t₀ 2, (stackArg t₀ 3).toNat⟩] (s.rd ++ s.wr) := by
    rw [hk₁.rd, hk₁.wr]; exact hp.tag
  exact ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    h1.env hp.ctx hp.w hk₀, hN, hA, hp.dsrc.of_eq hk₁.rd hk₁.wr hk₁.sp, h1.aad, h1.dat⟩, h1.s9, h19, hT,
    ⟨hp.ddst.of_eq hk₁.rd hk₁.wr hk₁.sp, hp.alias⟩, h1.dst⟩, h1.s4, by rw [h1.s5]; exact toN⟩

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

theorem openTo_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa openToRISCV64.pre openToRISCV64.pub OpenTo.openTo := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openToPreR σ₁ := h₁
  have hp₁ := h₁'.opre
  have hR := hp₁.rounds
  let I₀ : State → Prop := fun s => openToPreR s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ stackArg s 3 = stackArg σ₁ 3 ∧
    stackArg s 4 = stackArg σ₁ 4 ∧ (openToRes s).isSome = (openToRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qa 3 (by decide)).symm, (qa 4 (by decide)).symm,
    (qres hR).symm⟩, ?_⟩
  unfold OpenTo.openTo openWith openWithB
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 3
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openToEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 4 else σ₁.gpr r
    have hl : openEntryWithB false true = [.addSp .t1 0, .load .d .t1 .t1 32] ++ (oneRestAt 16 ++
        ([.load .d .s8 .t1 24, .load .d .t2 .t1 0, .sub .t2 .t2 .a6, .store .d .t2 .s0 dstO] : List Instr)) := by
      simp only [openEntryWithB, ↓reduceIte, Bool.false_eq_true, oneEntryAt_eq, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openToHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, _, _, ea4, _⟩
      have hsa : s.sp.toNat % 16 = 0 := hs.opre.al
      obtain ⟨hrd, -⟩ := id hs
      have hA : Covers [args s 5] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
      have hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := by
        have := in_off hA (d := 32) (n := 8) (by decide) (by decide)
        rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this
      refine WP.mono (oneA32_ok (W := stackArg s 4) hsa hin rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea4, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openToRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 3 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 3) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 3).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 3).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := hp₁.lay
  let res := (openToRes σ₁).isSome
  let J₃ : State → Prop := fun s => s.gpr .s0 = stackArg σ₁ 4 ∧ s.sp = σ₁.sp ∧ s.gpr .s11 = σ₁.gpr .a7 ∧
    s.gpr .a0 = BitVec.ofNat 64 (if res then 1 else 0) ∧
    s.mem.readW (stackArg σ₁ 4 + BitVec.ofNat 64 dataO) 64 = σ₁.gpr .a6 ∧
    s.mem.readW (stackArg σ₁ 4 + BitVec.ofNat 64 dstO) 64 = stackArg σ₁ 0 - σ₁.gpr .a6 ∧
    Covers [⟨stackArg σ₁ 4, 2560⟩] (s.rd ++ s.wr) ∧ Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] s.wr
  refine CT.seq (J := J₃) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_)) (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .a2) (n := (σ₁.gpr .a3).toNat) (Ad := σ₁.gpr .a4) (A := σ₁.gpr .a5)
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) (o := true) (Dst := stackArg σ₁ 0) L₀ hR
        (hp₁.dtW.sub_right (Lay.wSub (by decide))) t1 t16 res)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      have o := openTo_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea2, ea3, ea4, esp] at o
      refine ⟨o, open_head hpre.opre h4 (by rw [h19₄.trans h19]; simp) hok₀ (T' := .block [])
        fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8]
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome = true then 1 else 0)
      rw [← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · -- what both branches leave: the result, which both runs agree on, and the slots `wipe` reads
    obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩, h1, h19, g, k, h25⟩ := hs
    have hp := hpre.opre
    have hW₀ : Covers [⟨stackArg σ₁ 4, 2560⟩] (t₀.rd ++ t₀.wr) := by rw [← ea4]; exact Covers.right hp.w
    have hD₀ : Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] t₀.wr := by rw [← ea0, ← e10]; exact hp.dst
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩, h1, h19,
      g, k, h25⟩) (fun ht => ?_) (fun hf => ?_)
    · have hbad : ok = false := by
        cases e : ok
        · rfl
        · simp [e] at ht
      have hres : res = false := by
        show (openToRes σ₁).isSome = false
        simp only [openToRes, Spec.Gcm.openResult]
        rw [show Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat = false from hbad]
        rfl
      refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea4]
      · rw [u.sp, k.sp, h1.keeps.sp, esp]
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s11, e10]
      · rw [u.gpr, hres]; rfl
      · rw [u.mem, k.mem, ← ea4, h1.dat, e9]
      · rw [u.mem, k.mem, ← ea4, h1.dst rfl, ea0, e9]
      · rw [u.rd, u.wr, k.rd, k.wr, h1.keeps.rd, h1.keeps.wr]; exact hW₀
      · rw [u.wr, k.wr, h1.keeps.wr]; exact hD₀
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      refine WP.mono (open_good hp h4 (by rw [h19₄.trans h19]; simp) hok₀) fun s' bo =>
        ⟨by rw [bo.s0, ea4], by rw [bo.sp, esp], by rw [bo.s11, e10], ?_, by rw [← ea4, bo.dat, e9],
          by rw [← ea4, bo.dst rfl, ea0, e9], by rw [bo.rd, bo.wr]; exact hW₀, by rw [bo.wr]; exact hD₀⟩
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome then 1 else 0)
      rw [bo.a0, ← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  -- the end: the destination zeroed if the result is 0, then `restore`
  have ev₀ : ∀ s, J₃ s → isa.eval (.zero .a0) s = some (decide ((if res then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, h3, _⟩ => eval_zero h3 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 4 ∧ s.sp = σ₁.sp)
    (CT.ite _ ev₀ (fun _ => ?_) (fun _ => CT.skip)) (fun s hs => ?_) ?_
  · -- `wipe`: its first block, then its loop on the destination
    let J₄ : State → Prop := fun s => s.sp = σ₁.sp ∧ s.gpr .s0 = stackArg σ₁ 4 ∧ s.gpr .t2 = stackArg σ₁ 0 ∧
      s.gpr .t3 = BitVec.ofNat 64 (σ₁.gpr .a7).toNat
    unfold wipe
    refine CT.seq (J := J₄) ?_ (fun s ⟨h31, hsp, h23, _, hS, hδ, hW, _⟩ => WP.mono
      (wipeArgs_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp))
      fun s' ⟨t2, t3, _, g', k'⟩ => ⟨k'.sp.trans hsp, by rw [g' _ (by decide) (by decide) (by decide), h31], t2, t3⟩) ?_
    · obtain ⟨_, hc⟩ := wipeArgs_taint
      exact CT.taintEq _ (fun r => if r = .s0 then stackArg σ₁ 4 else σ₁.gpr .a7) σ₁.sp
        (fun s ⟨h31, hsp, h23, _⟩ => ⟨hsp, by simp [h31, h23]⟩) hc
    · obtain ⟨_, hc⟩ := wipeLoop_taint
      exact CT.taintEq _ (fun r => if r = .t2 then stackArg σ₁ 0 else BitVec.ofNat 64 (σ₁.gpr .a7).toNat) σ₁.sp
        (fun s ⟨hsp, _, h2, h3⟩ => ⟨hsp, by simp [h2, h3]⟩) hc
  · obtain ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩ := hs
    refine WP.ite _ (ev₀ s ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩) (fun _ => ?_) (fun _ => WP.block_nil ⟨h31, hsp⟩)
    have fD : (stackArg σ₁ 0).toNat + (σ₁.gpr .a7).toNat ≤ 2 ^ 64 := hp₁.fD
    exact WP.mono (wipe_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp) (σ₁.gpr .a7).isLt
      fD hdw) fun u ⟨_, _, gu, _, _, spu⟩ => ⟨by rw [gu _ (by decide) (by decide) (by decide)]; exact h31,
        spu.trans hsp⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM decryption out of place, RISC-V: `Verified`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` decrypts
from `src` straight to `dst` in one pass (`OpenTo/Fn.lean`, `OpenTo/CT.lean`),
proved with its working space as a last argument, after the others on the
stack (`openTo_verified`, against `Sig.scratchContract`), and then in a frame
that allocates it (`openTo_framed`, `Verified.stackScratchArgs`), as
`vg_aes_gcm_open` (`Proof/AesGcm/RISCV64/Verified.lean`). The frame copies
the arguments passed on the stack, which needs the contract to read the
memory on entry only within the function's buffers (`openToPre_local`,
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

theorem openTo_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : openToRISCV64.pre s) :
    ∃ t s', Exec isa openTo s t s' ∧ abiPreserved s s' ∧ openToRISCV64.post s s' :=
  openTo_wp hs

/-- `tag` at `0x5000`, `dst` at `0x7000` and the working space at `0x6000`,
the stack arguments; no nonce, additional data, text or tag. -/
def toSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x70 else bif Nat.beq a.toNat 0x9011 then 0x50 else
    bif Nat.beq a.toNat 0x9021 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 40⟩]
  wr := [⟨0x7000, 0⟩, ⟨0x6000, 2560⟩]

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and the public data include the leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem openTo_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target openTo
      (Sig.scratchContract RISCV64.abi Spec.Gcm.openToSig "work" .u64 320 (Spec.Gcm.openToPre 64)
        (Proof.AesGcm.openToRoundsPost 64) true 2048 (some (Spec.Gcm.openToLeak 64))) :=
  Verified.of_correct openTo_correct openTo_ct
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToPre, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Proof.AesGcm.openToRoundsPost, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop]
        simp only [openToRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToLeak, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl
          exacts [a0, a1, a2, a3, a4]
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToPre, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toSat }

/-! ## With the working space on the stack -/

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space: `dst`, `dst_len`, `tag` and `tag_len` alone on the stack. -/
def toFrameSat : State :=
  { toSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 32⟩],
               wr := [⟨0x7000, 0⟩] }

theorem toFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract RISCV64.abi 4656).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr,
    List.getD, List.range, List.range.loop]
    [toFrameSat, toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toFrameSat

/-- `open_to`, whose `dst`, `dst_len`, `tag` and `tag_len` arrive on the
stack, as `open`'s `tag` and `tag_len` do. -/
theorem openTo_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2608 4 openTo)
      (Proof.AesGcm.openToRoundsContract RISCV64.abi 4656) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openToPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.openToRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2608) (m := 4) (leak := some (Spec.Gcm.openToLeak RISCV64.abi.ptrBits))
    openTo_verified (by decide) (by decide) (openToPre_local _) (openToPost_local _)
    (openToPostOut_local _) toFrameSat_pre (hleak := openToLeak_local _)

end VG.Proof.AesGcm.RISCV64.OpenTo
