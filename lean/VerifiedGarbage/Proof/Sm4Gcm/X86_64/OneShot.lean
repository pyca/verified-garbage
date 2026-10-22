module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SM4-GCM on x86-64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OneShot.lean`), their streaming state is in `work`, at
`W + 16`. The entry takes `W` from the stack and keeps the public arguments
in it (`oneEntry_ok`); AES-GCM's `oneAad` computes `J₀` and absorbs the
additional data, padded (`oneMid_ok`); `oneCrypt` runs counter mode over the
data from the first counter block (`oneCrypt_ok`); and `oneTag o` absorbs the
ciphertext, padded, and writes the tag to `W + o` (`oneTag_ok`). The calls of
`vg_sm4_ctr32` use the `stkN` bytes below the return address.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save stO aadO alenO dataO lenO tlenO oneAad)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm DataOk DataW SavedAt savedR save_ok covers_of_mem covers_off
  covers_left in_off add_ofNat_assoc blockAt_frame bytesAt_frame ctxH_eq AbsIn absorbPad_ok oneR lensBlock_mod_left)

/-- What the precondition of `seal` (`k = 3`) and `open` (`k = 4`) gives. -/
structure OneCtx (s : State) (k : Nat) (Ctx W SP Np A D : Addr) (nl al n : Nat) : Prop where
  lay : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP
  perm : Perm Ctx (W + BitVec.ofNat 64 16) W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : ∀ i < k, InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 * (i + 1))) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩
  nonce : DataOk (W + BitVec.ofNat 64 16) W SP s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  data : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩

/-- `OneCtx`, from `oneLay` and where the buffers are, with `work` the `w`-th
of `k` arguments on the stack. -/
theorem OneCtx.of {w k : Nat} {s : State} (hp : Proof.Sm4Gcm.oneLay w k s)
    (pc : Covers [⟨s.gpr .rdi, 256⟩] (s.rd ++ s.wr)) (pn : Covers [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩] (s.rd ++ s.wr))
    (pa : Covers [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr))
    (pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * k⟩] (s.rd ++ s.wr))
    (pd : Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] s.wr) (pW : Covers [⟨stackArg s w, 2560⟩] s.wr) :
    OneCtx s k (s.gpr .rdi) (stackArg s w) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat := by
  simp only [Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.args,
    Proof.Sm4Gcm.arg, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨d_cd, d_cw, -, d_nw, -, d_aw, d_dw, d_da, d_wa, r_d, r_w, t_c, t_n, t_a, t_d, t_w, wc, wn, wa, wd, ww,
    sp, wsp⟩ := hp
  have b8 := below8_stk (s.gpr .rsp)
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at d_da d_wa
  have hSt : (⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ : Region).Sub ⟨stackArg s w, 2560⟩ := Lay.wSub (by decide)
  have L : Lay (s.gpr .rdi) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) (s.gpr .rsp) := by
    refine ⟨wc, ?_, ww, d_cw.sub_right hSt, d_cw, ?_, ?_, t_c.sub_left b8, (t_w.sub_left b8).sub_right hSt,
      t_w.sub_left b8⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le ((stackArg s w).toNat + 16 % 2 ^ 64) (2 ^ 64)
      omega_arith
    · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
        (by omega_arith) (by omega_arith)
    · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
        (by omega_arith) (by omega_arith)
  refine ⟨⟨L, sp, t_c, t_w.sub_right hSt, t_w⟩, ⟨pc, covers_off pW (show 16 + 80 ≤ 2560 by decide) (by decide), pW⟩,
    ww, fun i hi => ?_, d_wa.symm,
    ⟨pn, by have := (s.gpr .rdx).isLt; omega_arith, wn, d_nw.sub_right hSt, d_nw, t_n.sub_left b8⟩,
    ⟨pa, by have := (s.gpr .r8).isLt; omega_arith, wa, d_aw.sub_right hSt, d_aw, t_a.sub_left b8⟩,
    ⟨⟨⟨covers_left pd, by have := (stackArg s 0).isLt; omega_arith, wd, d_dw.sub_right hSt, d_dw, t_d.sub_left b8⟩,
      pd, d_cd⟩, t_d⟩,
    r_d, r_w, d_dw, d_da.symm⟩
  have := in_off pm (d := 8 * i) (n := 8) (by omega_arith) (by omega_arith)
  rwa [add_ofNat_assoc, show 8 + 8 * i = 8 * (i + 1) by omega_arith] at this

/-- What `seal`'s precondition gives: `OneCtx`, and `tag`, 16 bytes to write
at `T` (the second argument on the stack). -/
theorem OneCtx.ofSeal {s : State} (hp : Proof.Sm4Gcm.sealPre s) :
    OneCtx s 3 (s.gpr .rdi) (stackArg s 2) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat ∧ Covers [⟨stackArg s 1, 16⟩] s.wr ∧
      (⟨stackArg s 1, 16⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩ ∧
      (⟨stackArg s 1, 16⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, 16⟩ ∧
      (below (s.gpr .rsp) stkN).Disjoint ⟨stackArg s 1, 16⟩ := by
  have hp' := hp
  simp only [Proof.Sm4Gcm.sealPre, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.args, Proof.Sm4Gcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, -, r_t, t_t, -⟩ := hp'
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 2) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, r_t, t_t⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- What `open`'s precondition gives: `OneCtx`, and the received tag, the
`tag_len` (third argument on the stack) bytes to read at `T` (the second). -/
theorem OneCtx.ofOpen {s : State} (hp : Proof.Sm4Gcm.openPre s) :
    OneCtx s 4 (s.gpr .rdi) (stackArg s 3) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat ∧
      Covers [⟨stackArg s 1, (stackArg s 2).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩ ∧
      (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, 2560⟩ ∧
      (below (s.gpr .rsp) stkN).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩ := by
  have hp' := hp
  simp only [Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.args, Proof.Sm4Gcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, t_t, -⟩ := hp'
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 3) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, t_t⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

/-- After `oneEntry`. -/
structure OneEntry (s₀ : State) (Ctx W SP A D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r8
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rbp : s.gpr .rbp = s₀.gpr .rdx
  rsp : s.gpr .rsp = SP
  saved : SavedAt s.mem W s₀
  frame : Frame [oneR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `oneEntry wo`, with `W` at `[rsp + wo]`. -/
theorem oneEntry_ok {s : State} {k : Nat} (hk : 1 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) {wo : Nat} (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP)
    (hA : s.gpr .rcx = A) (hD : s.gpr .r9 = D) (hn : (stackArg s 0).toNat = n)
    (hW' : s.mem.readW (SP + BitVec.ofNat 64 wo) 64 = W) (a₂ : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 wo) 8) :
    WP isa (.block (oneEntry wo)) s (OneEntry s Ctx W SP A D n) := by
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  have a₀ := C.args 0 hk
  simp only [Nat.zero_add, Nat.mul_one] at a₀
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp wo))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, a₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := C.perm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [VG.Impl.AesGcm.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off C.perm.w (show 232 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off C.perm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off C.perm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off C.perm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off C.perm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₀
  have s8 : Region.Sub ⟨SP + BitVec.ofNat 64 8, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := Region.sub_prefix (by omega_arith)
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [hm₀] at f₁
    rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (C.dA.sub_left s8).sub_right (Lay.wSub (by decide))) (by decide), hn']
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 240 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d _ h₂ => by
      have dd : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ :=
        (C.dA.sub_left s8).sub_right (Lay.wSub (by omega_arith))
      exact dd.sep (Region.contains_self _ _) (Region.contains_self _ _)
  have p₁ := sA 232 (by decide) (by decide)
  have p₂ := sA 184 (by decide) (by decide)
  have p₃ := sA 200 (by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := C.ww; omega_arith) (by have := C.ww; omega_arith)
  have q₀ := sep 232 184 (by decide) (by decide) (by decide)
  have q₁ := sep 232 200 (by decide) (by decide) (by decide)
  have q₂ := sep 232 208 (by decide) (by decide) (by decide)
  have q₃ := sep 232 192 (by decide) (by decide) (by decide)
  have q₄ := sep 184 200 (by decide) (by decide) (by decide)
  have q₅ := sep 184 208 (by decide) (by decide) (by decide)
  have q₆ := sep 184 192 (by decide) (by decide) (by decide)
  have q₇ := sep 200 208 (by decide) (by decide) (by decide)
  have q₈ := sep 200 192 (by decide) (by decide) (by decide)
  have q₉ := sep 208 192 (by decide) (by decide) (by decide)
  have e : oneEntry wo = [.mov .rax (.mem (at_ .rsp wo))] ++ save .rax ++
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rax, .store (at_ .r15 tlenO) .rax,
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] := by
    simp [oneEntry, ptr, stO]
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rax, .store (at_ .r15 tlenO) .rax,
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = s.gpr .rsi ∧
      s₂.gpr .rbp = s.gpr .rdx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 232) A).writeW (W + BitVec.ofNat 64 184) (s.gpr .r8)).writeW
        (W + BitVec.ofNat 64 200) D).writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n)).writeW
          (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₀], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hrdi, hCtx]
    · simp [gpr_setReg, gpr_arithFlags, hrsi]
    · simp [gpr_setReg, gpr_arithFlags, hrdx]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, gpr_arithFlags,
        Mem.readW_writeW_sep, hn₁, hrcx, hr8, hr9, hA, hD]
    all_goals rfl
  rw [e]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 64⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 240 → (⟨W + BitVec.ofNat 64 176, 64⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := C.ww; omega_arith)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 232 ∧ v = A) ∨ (d = 184 ∧ v = s.gpr .r8) ∨ (d = 200 ∧ v = D) ∨
      (d = 208 ∧ v = BitVec.ofNat 64 n) ∨ (d = 192 ∧ v = BitVec.ofNat 64 n) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64,
        Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, C.perm.of_eq hrd' hwr'⟩, rd 232 _ (.inl ⟨rfl, rfl⟩),
    rd 184 _ (.inr (.inl ⟨rfl, rfl⟩)), rd 200 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))),
    rd 208 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), rd 192 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))),
    h12, hbp, hsp, ?_, ?_, hrd', hwr'⟩
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by have := C.ww; omega_arith) (by have := C.ww; omega_arith)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- What `seal` and `open` write after their entry: `W` but for the saved
registers and the kept values, the data and the stack. -/
abbrev oneFrame (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP stkN]

/-- What the pieces but `crypt` and the tag write: `W` but for the received
tag, the saved registers and the kept values, and the stack. -/
abbrev wFrame (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, below SP stkN]

theorem wFrame_one {W D SP : Addr} {n o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m') : Frame (oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by omega_arith)⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem wFrame_cons {W SP : Addr} {o : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m' := h.mono fun _ hr => List.mem_cons_of_mem _ hr

/-- AES-GCM's `wFrame`, with the stack below `SP` of its own calls. -/
theorem wFrame_of_aes {W SP : Addr} {m m' : Mem} (h : Frame (AesGcm.X86_64.wFrame W SP) m m') :
    Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below SP stkN, by simp, below8_stk SP⟩

theorem w_wFrame {W SP : Addr} {d k : Nat}
    (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

theorem st_wFrame {W SP : Addr} {d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [add_ofNat_assoc]; exact w_wFrame (.inl ⟨by omega_arith, by omega_arith⟩)

/-- What the pieces write, inside `W` and the stack. -/
theorem wFrame_w {W SP : Addr} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame [⟨W, 2560⟩, below SP stkN] m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem oneR_w {W SP : Addr} : ∃ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], Region.Sub (oneR W) r :=
  ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- A part of `W` in `oneFrame`. -/
theorem w_oneFrame {W D SP : Addr} {n d k : Nat}
    (h : d + k ≤ 128 ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

theorem st_oneFrame {W D SP : Addr} {n d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [add_ofNat_assoc]; exact w_oneFrame (.inl (by omega_arith))

/-- What `crypt` writes, in `oneFrame`. -/
theorem crFrame_one {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (crFrame (W + BitVec.ofNat 64 16) SP D n) m m') :
    Frame (oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  · exact st_oneFrame (by decide)
  · exact ⟨below SP stkN, by simp, fun _ h => h⟩

/-- What `tag o` writes. -/
theorem tagFrame_one {W SP : Addr} {o : Nat} {m m' : Mem}
    (h : Frame (tagFrame (W + BitVec.ofNat 64 16) W SP o) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 16) (k := 32) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 96) (k := 16) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 512) (k := 256) (.inr (.inr ⟨by decide, by decide⟩))
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨below SP stkN, List.mem_cons_of_mem _ (by simp), fun _ h => h⟩

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The kept values are outside `oneFrame`. -/
theorem kept_oneFrame {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h : (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ oneFrame W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.lay.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact L.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm
  · exact (L.kw.sub_right (Lay.wSub (by omega_arith))).symm

theorem saved_oneFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ oneFrame W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.lay.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (L.kw.sub_right (Lay.wSub (by decide))).symm

end

/-- What `seal` and `open` share: `J₀`, the additional data, and their
effects so far, from the entry. -/
structure OneMid (s₀ : State) (Ctx W SP D : Addr) (n : Nat) (H : Block) (iv a : List Byte) (mE : Mem) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r8
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, below SP stkN] s₀.mem s.mem
  fr : Frame (wFrame W SP) mE s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- AES-GCM's `oneAad`, after the entry. -/
theorem oneMid_ok (v : GcmImpl) {k : Nat} {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al) :
    WP isa (oneAad v.callees) s₁
      (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.lay.cw'.sub_left (Lay.ctxSub (by decide))))]
  have hiv : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame E.frame (dW _ _ C.nonce.w) (by have := C.nonce.lt; omega_arith)
  have haa : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega_arith)
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (AesGcm.X86_64.oneAad_ok v L.lay E.env hH₁ (by rw [E.r12, hNp])
    (by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr)
    C.dE E.aad hal')) fun s₂ ⟨ao, hrd₂, hwr₂⟩ => ?_
  rw [hiv, haa] at ao
  have f₂ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons ao.frame)
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (AesGcm.X86_64.kept_oneFrame L.lay C.dE hd) (by decide)
  have fr := wFrame_of_aes ao.frame
  refine ⟨ao.env, ao.hH, by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact E.dat,
    by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact E.len, by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact E.tlen,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact E.alen, ao.j0, ao.abs, ao.cb,
    E.saved.frame f₂ (AesGcm.X86_64.saved_oneFrame L.lay C.dE), ?_, fr, hrd₂.trans E.rd, hwr₂.trans E.wr⟩
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact oneR_w).trans (wFrame_w fr)

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneCrypt`: counter mode over the data, from the first counter block. -/
theorem oneCrypt_ok {icb : Block} {P : Nat} (hP : P % 16 = 0) {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa oneCrypt s fun s' => CrOut Ctx (W + BitVec.ofNat 64 16) W SP icb P D n s.mem s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hP]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have := AesGcm.X86_64.WP.with_rdwr (cryptAl_ok L (icb := icb) (P := P) ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁⟩ hP)
  rw [hm₁] at this
  exact WP.mono this fun s' ⟨h, a, b⟩ => ⟨h, a.trans hrd₁, b.trans hwr₁⟩

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneTag o`: the ciphertext absorbed, padded, and the tag into `W + o`. -/
theorem oneTag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {D : Addr} {n N al : Nat} {H : Block} {x : List Byte}
    (hx16 : x.length % 16 = 0) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (oneTag v.callees o) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx (blockAt s.mem (W + BitVec.ofNat 64 16)))) := by
  have La := L.lay
  have kp : ∀ {m m' : Mem}, Frame (AesGcm.X86_64.oneFrame W D SP n) m m' → ∀ d,
      (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (AesGcm.X86_64.kept_oneFrame La hDW hd) (by decide)
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hx16]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H x D n s₁ :=
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁, hH]⟩
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (yo := 16) (.inr rfl) hai hx16))
    fun s₄ ⟨hf, hrd₄, hwr₄⟩ => ?_)
  rw [hm₁] at hf
  obtain ⟨m₂, fa, ft⟩ := hf.frame
  have he₄ := hf.env
  have g₂ := AesGcm.X86_64.absFrame_one fa
  have f₂ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₂)
  have g₄ := AesGcm.X86_64.tFrame_one ft
  have f₄ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₄)
  have q₄ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have q₅ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧ s₅.gpr .rbx = BitVec.ofNat 64 al ∧
      s₅.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧
      s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, q₄, q₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₄ 184 (.inl ⟨by decide, by decide⟩), kp f₂ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg, kp f₄ 192 (.inl ⟨by decide, by decide⟩), kp f₂ 192 (.inl ⟨by decide, by decide⟩), htl]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have g₅ : Frame (AesGcm.X86_64.wFrame W SP) s.mem s₅.mem := by rw [hm₅]; exact g₂.trans g₄
  have f₅ : Frame (AesGcm.X86_64.oneFrame W D SP n) s.mem s₅.mem :=
    AesGcm.X86_64.wFrame_one (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₅)
  have dC : ∀ r ∈ AesGcm.X86_64.oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact La.cw'.sub_right (Offset.sub_base W (show 0 + 128 ≤ 2560 by decide) |> fun h => by simpa using h)
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact hCD
    · exact La.kc.symm
  have dS0 : ∀ r ∈ AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16,
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using La.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_st (a := 0) (n := 16) (d := 32) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (La.stk_st (a := 0) (n := 16) (by decide)).symm
  have dT0 : ∀ r ∈ AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16,
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using La.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using La.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (La.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [hm₅, blockAt_frame ft dT0, blockAt_frame fa dS0]
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [hm₅, hf.hH]
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (tag_ok v L ho he₅ hH₅ hJ₅)) fun s₆ ⟨ht, hrd₆, hwr₆⟩ =>
    ⟨ht.env, (wFrame_cons (wFrame_of_aes g₅)).trans (tagFrame_one ht.frame), by rw [hrd₆, hrd₅, hrd₄, hrd₁],
      by rw [hwr₆, hwr₅, hwr₄, hwr₁], ?_, ht.j, fun hab => ?_⟩
  · have d48 : ∀ r ∈ tagFrame (W + BitVec.ofNat 64 16) W SP o,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using La.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact La.st_w (by decide) (by omega_arith)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.ks.sub_right (Lay.stSub (by decide))).symm
    have d48a : ∀ r ∈ AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (La.stk_st (by decide)).symm
    have d48t : ∀ r ∈ AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (La.stk_st (by decide)).symm
    rw [blockAt_frame ht.frame d48, hm₅, blockAt_frame ft d48t, blockAt_frame fa d48a]
  have hw := (hf.abs hab).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [ht.out, ciph_frame f₅ dC, hbx₅, hbp₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN,
    lensBlock_mod_left, hm₅, hw]

end

end VG.Proof.Sm4Gcm.X86_64
