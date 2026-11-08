module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Open
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
  have mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  have hD : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₀.wr := by
    rw [hwr, ← dl]; exact covers_mem (List.mem_cons_self ..)
  have hb : ∀ r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
      ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩,
      ⟨stackArg s₀ 2, (stackArg s₀ 3).toNat⟩, ⟨stackArg s₀ 4, 2560⟩], r.Disjoint (below s₀.sp 2048) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have m : ∀ {x : Region}, x ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
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
  have hW : Covers [⟨stackArg s₀ 4, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 5] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have ain : ∀ i < 5, InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * i)) 8 := fun i hi => by
    have := in_off hA (d := 8 * i) (n := 8) (by omega) (by omega)
    rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this
  have dA : (args s₀ 5).Disjoint (oneR (stackArg s₀ 4)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  have dAi : ∀ i < 5, (⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (oneR (stackArg s₀ 4)) :=
    fun i hi => by
      have hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8 * i) (n := 8) (k := 40) (by omega)
      rw [add_ofNat_assoc, Nat.zero_add] at hs
      exact dA.sub_left hs
  have spa : s₀.sp.toNat % 8 = 0 := by have := hstk.1; omega
  simp only [openEntryWith, ↓reduceIte]
  refine WP.block_append (WP.mono (WP.keep [.t1, .s0, .s1, .s2, .s3, .s4, .s5, .s7, .s9, .s10, .s11]
    (one1At_wp (off := 32) (tagO := 16) (W := stackArg s₀ 4) (T := stackArg s₀ 2) (.inr (.inr rfl)) (.inr rfl) hW
      wa hstk.1 (ain 4 (by decide)) rfl (ain 2 (by decide)) rfl (dAi 2 (by decide))) (by rfl) rfl)
    fun s₁ ⟨h1, kp⟩ => ?_)
  have hk₁ := h1.keeps
  have hv : ∀ i < 5, s₁.mem.readW (s₀.sp + BitVec.ofNat 64 (8 * i)) 64 = stackArg s₀ i := fun i hi => by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAi i hi) (by decide)]
    rfl
  have hv3 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 24) 64 = stackArg s₀ 3 := hv 3 (by decide)
  have hv0 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = stackArg s₀ 0 := hv 0 (by decide)
  have in3 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 24) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 3 (by decide)
  have in0 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 0 (by decide)
  refine Steps.wp_ld (off := 24) (a := s₀.sp + BitVec.ofNat 64 24) (by decide) (by rw [h1.t1])
    (Spill.al8 spa (by decide)) in3 fun s₂ u₂ => ?_
  refine Steps.wp_ld (off := 0) (a := s₀.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [u₂.other _ (by decide), h1.t1]) (Spill.al8 spa (by decide)) (by rw [u₂.rd, u₂.wr]; exact in0)
    fun s₃ u₃ => ?_
  refine Steps.wp_sub fun s₄ u₄ => ?_
  have e0 : s₄.gpr .s0 = stackArg s₀ 4 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h1.s0]
  refine Steps.wp_sd (off := dstO) (a := stackArg s₀ 4 + BitVec.ofNat 64 dstO) (by decide) (by rw [e0])
    (Spill.al8 wa (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, hk₁.wr]; exact in_off hW (show dstO + 8 ≤ 2560 by decide) (by decide))
    fun s₅ m₅ => WP.block_nil ?_
  have t2 : s₄.gpr .t2 = stackArg s₀ 0 - s₀.gpr .a6 := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), kp.gpr (by decide), u₂.mem, hv0]
  have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have hm : s₅.mem = s₁.mem.writeW (stackArg s₀ 4 + BitVec.ofNat 64 dstO) (stackArg s₀ 0 - s₀.gpr .a6) := by
    rw [m₅.mem, t2, mem₄]
  have g : ∀ r, r ≠ .s8 → r ≠ .t2 → s₅.gpr r = s₁.gpr r := fun r h8 h2 => by
    rw [m₅.gpr, u₄.other r h2, u₃.other r h2, u₂.other r h8]
  have dS : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 248 →
      (⟨stackArg s₀ 4 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint ⟨stackArg s₀ 4 + BitVec.ofNat 64 dstO, 8⟩ :=
    fun h₁ h₂ => Lay.w_w (.inl (by unfold dstO; omega)) (by omega) (by decide)
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
      ⟨0, rfl, by omega, by rw [h₂]; exact (BitVec.add_zero _).symm, by rw [h₃, Nat.sub_zero],
        fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r2, r3, gv, rdv, wrv, spv, fv, pv⟩
    have hcn : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine Steps.wp_sb (off := 0) (a := D + BitVec.ofNat 64 i) (by decide) (by rw [r2]; exact BitVec.add_zero _)
      (by rw [wrv]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩) fun t₁ u₁ => ?_
    refine Steps.wp_addi (imm := 1) (by decide) fun t₂ u₂ => Steps.wp_subi (imm := 1) (by decide) fun t₃ u₃ =>
      WP.block_nil ?_
    have z₁ : (v.gpr .t1).setWidth 8 = (0 : BitVec 8) := by rw [gv _ (by decide) (by decide), h₁]; rfl
    have m₃ : t₃.mem = v.mem.writeW (D + BitVec.ofNat 64 i) (0 : BitVec 8) := by
      rw [u₃.mem, u₂.mem, u₁.mem, z₁]
    have f' : Frame [⟨D, n⟩] u.mem t₃.mem := by
      rw [m₃]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix t₃.mem D (i + 1) := by
      rw [m₃]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g' : ∀ r, r ≠ .t2 → r ≠ .t3 → t₃.gpr r = u.gpr r := fun r a b => by
      rw [u₃.other _ b, u₂.other _ a, u₁.gpr, gv r a b]
    have r2' : t₃.gpr .t2 = D + BitVec.ofNat 64 (i + 1) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, r2, Offset.add_add]
    have r3' : t₃.gpr .t3 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, r3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    have rd' : t₃.rd = u.rd := by rw [u₃.rd, u₂.rd, u₁.rd, rdv]
    have wr' : t₃.wr = u.wr := by rw [u₃.wr, u₂.wr, u₁.wr, wrv]
    have sp' : t₃.sp = u.sp := by rw [u₃.sp, u₂.sp, u₁.sp, spv]
    have ev := Steps.eval_nonzero_ofNat t₃ .t3 (k := n - (i + 1)) (by omega) r3'
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g', rd', wr', sp'⟩
    · right
      exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r2', r3', g', rd', wr', sp',
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
  have hres : openToRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧
      OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat then
      some (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)) else none := by
    simp only [openToRes, openResult, decryptWith]
    by_cases hl : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true
    · simp only [hl, ite_true, true_and]
    · simp only [hl, false_and, ite_false, Bool.false_eq_true]
  show WP isa (.seq (.ite (.zero .a0) wipe (.block [])) (.block restore)) s₅ _
  have hW₅ : Covers [⟨stackArg s₀ 4, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [br.rd, br.wr]; exact Covers.right hW
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
      have hdw : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₅.wr := by rw [br.wr]; exact hp.dst
      refine WP.mono (wipe_ok (S := s₀.gpr .a6) br.s0 hp.wa hW₅ br.dat (br.dst rfl) (by rw [br.s11]; simp)
        (s₀.gpr .a7).isLt hp.fD hdw) fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ?_
      have g0 : u.gpr .s0 = stackArg s₀ 4 := by rw [gu _ (by decide) (by decide) (by decide)]; exact br.s0
      have ga : u.gpr .a0 = s₅.gpr .a0 := gu _ (by decide) (by decide) (by decide)
      have sv : SavedAt u.mem (stackArg s₀ 4) s₀ := br.saved.frame fu fun r hr => by
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
