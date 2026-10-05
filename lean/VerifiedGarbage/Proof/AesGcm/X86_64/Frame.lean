import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt`. -/
section

/-!
# AES-GCM on x86-64: the entry of `vg_aes_gcm_stream_encrypt` and `_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`), and what the precondition gives
(`CryptCtx`); `streamText` follows (`StreamText.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the entry writes in `W`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- After `cryptEntry`. -/
structure CryptEntry (s₀ : State) (Ctx St W SP D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 ((s₀.gpr .r8).toNat % 16)
  saved : SavedAt s.mem W s₀
  frame : Frame [VG.Proof.AesGcm.X86_64.entryR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cryptEntry_ok {s : State} {Ctx St W SP D : Addr} {n : Nat} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hD : s.gpr .r9 = D) (hSP : s.gpr .rsp = SP) (hW : stackArg s 1 = W) (hn : (stackArg s 0).toNat = n)
    (hperm : Perm Ctx St W s) (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hargs : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hdA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block cryptEntry) s (VG.Proof.AesGcm.X86_64.CryptEntry s Ctx St W SP D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W := by rw [← hW, ← hSP]; rfl
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, hargs.2], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off hperm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off hperm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  have a₁ := hargs.1
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₁
  have hsepA : ∀ (m : Mem) (k : Nat), Frame [⟨W + BitVec.ofNat 64 128, k⟩] s.mem m → k ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := fun m k hf hk => by
    rw [hf.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdA.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))) (by decide), hn']
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := hsepA _ 48 (hm₀ ▸ f₁) (by decide)
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 216 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Region.Disjoint.sep ((hdA.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (n := 8) (d := d) (by omega))) (Region.contains_self _ _) (Region.contains_self _ _)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have a₁₇₆ := sA 176 (by decide) (by decide)
  have a₁₈₄ := sA 184 (by decide) (by decide)
  have a₁₉₂ := sA 192 (by decide) (by decide)
  have a₂₀₀ := sA 200 (by decide) (by decide)
  have q0 := sep 176 184 (by decide) (by decide) (by decide)
  have q1 := sep 176 192 (by decide) (by decide) (by decide)
  have q2 := sep 176 200 (by decide) (by decide) (by decide)
  have q3 := sep 176 208 (by decide) (by decide) (by decide)
  have q4 := sep 184 192 (by decide) (by decide) (by decide)
  have q5 := sep 184 200 (by decide) (by decide) (by decide)
  have q6 := sep 184 208 (by decide) (by decide) (by decide)
  have q7 := sep 192 200 (by decide) (by decide) (by decide)
  have q8 := sep 192 208 (by decide) (by decide) (by decide)
  have q9 := sep 200 208 (by decide) (by decide) (by decide)
  have hand := and15 (s.gpr .r8)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8,
        .store (at_ .r15 dataO) .r9, .mov .rbp (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rbp,
        .mov .r12 (.reg .r9), .mov .rbx (.reg .r8), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧ s₂.gpr .rbp = BitVec.ofNat 64 n ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((s.gpr .r8).toNat % 16) ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, hrdx, hSt]
    · simp [gpr_setReg, hrdi, hCtx]
    · simp [gpr_setReg, hr9, hD]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, Mem.readW_writeW_sep, hn₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hr8, hand]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, Mem.readW_writeW_sep,
        hn₁, hrsi, hrcx, hr8, hr9, hD]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 40⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 176, 40⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 184 ∧ v = s.gpr .rcx) ∨ (d = 192 ∧ v = s.gpr .r8) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, ⟨?_, hR⟩, rd 184 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 192 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))), h12, hbp, hbx, ?_, ?_, hrd', hwr'⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the precondition of `encrypt` and `decrypt` gives. -/
structure CryptCtx (s : State) (Ctx St W SP D : Addr) (n : Nat) : Prop where
  lay : Lay Ctx St W SP
  perm : Perm Ctx St W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  data : DataW Ctx St W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  /-- The stack of the call of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks`. -/
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_s : (below SP 24).Disjoint ⟨St, 80⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

theorem CryptCtx.of {s : State} (hp : Proof.AesGcm.streamCryptPre s) :
    VG.Proof.AesGcm.X86_64.CryptCtx s (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .r9) (stackArg s 0).toNat := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cs, d_cd, d_cw, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, r_s, r_d, r_w, t_c, t_s, t_d, t_w,
    wc, ws, wd, ww, sp24, wsp, hR⟩ := hp
  have b8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by decide) (by decide)
  have k_c := t_c.sub_left b8
  have k_s := t_s.sub_left b8
  have k_d := t_d.sub_left b8
  have k_w := t_w.sub_left b8
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  have L : Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ww, ⟨?_, ?_⟩, d_wa.symm, ⟨⟨?_, by have := (stackArg s 0).isLt; omega, wd, d_sd.symm, d_dw,
    k_d⟩, ?_, d_cd⟩, r_d, r_s, r_w, d_dw, hR, t_c, t_s, t_w, t_d, sp24⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · simpa using in_off pm (show 0 + 8 ≤ 16 by decide) (by decide)
  · have := in_off pm (show 8 + 8 ≤ 16 by decide) (by decide)
    rwa [add_ofNat_assoc] at this
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamText`. -/
section

/-!
# AES-GCM on x86-64: the text of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. `streamText enc` takes the
`n` bytes at `D` in pieces, keeping `SInv` between them: the first `j`
bytes are done (encrypted or decrypted, and their ciphertext absorbed), the
rest are as they were. The pieces: the additional data padded if there is
no text yet (`start_ok`), the head (`sHead_ok`, then `part_ok`), the whole
blocks in one call (`blocks_ok`), and the rest (`part_ok`): `streamText_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `streamText` writes. -/
abbrev stFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 64⟩, ⟨D, n⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 192, 32⟩,
    ⟨W + BitVec.ofNat 64 448, 2112⟩, below SP 24]

/-- The ciphertext of the text `x` from byte `P` on: `x` encrypted, if `enc`,
or `x`. -/
def ctext (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x : List Byte) : List Byte :=
  if enc then xorKs ciph icb P x else x

theorem ctext_append (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x y : List Byte) :
    VG.Proof.AesGcm.X86_64.ctext enc ciph icb P (x ++ y) = VG.Proof.AesGcm.X86_64.ctext enc ciph icb P x ++ VG.Proof.AesGcm.X86_64.ctext enc ciph icb (P + x.length) y := by
  cases enc
  · rfl
  · exact Proof.Gcm.xorKs_append _ _ _ _ _

theorem length_ctext (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x : List Byte) :
    (VG.Proof.AesGcm.X86_64.ctext enc ciph icb P x).length = x.length := by
  cases enc
  · rfl
  · exact Proof.Gcm.length_xorKs _ _ _ _

theorem ctext_nil (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) : VG.Proof.AesGcm.X86_64.ctext enc ciph icb P [] = [] := by
  cases enc <;> rfl

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

/-- Equal bytes, split. -/
theorem bytesAt_split_eq {m m' : Mem} {p : Addr} {a b : Nat} (h : bytesAt m p (a + b) = bytesAt m' p (a + b)) :
    bytesAt m p a = bytesAt m' p a ∧ bytesAt m (p + BitVec.ofNat 64 a) b = bytesAt m' (p + BitVec.ofNat 64 a) b := by
  rw [bytesAt_add, bytesAt_add] at h
  exact List.append_inj h (by rw [length_bytesAt, length_bytesAt])

/-- What stays the same through `streamText`: the layout and what the call
of the whole blocks needs, the rounds and the hash subkey. -/
structure SCtx (Ctx St W SP : Addr) (R : Nat) (H : Block) (D : Addr) (n : Nat) (m₀ : Mem) : Prop where
  lay : Lay Ctx St W SP
  rounds : RoundsAt m₀ W R
  hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_s : (below SP 24).Disjoint ⟨St, 80⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

/-- Between the pieces of `streamText`: the first `j` of the `n` bytes at
`D` done, from `m₀`. Given `Hyp` (the streaming state at the start, with
`x₀` absorbed and `P₀` bytes of text so far), GHASH has absorbed their
ciphertext and the counter is past them. -/
structure SInv (Hyp : Prop) (Ctx St W SP : Addr) (R : Nat) (H icb : Block) (x₀ : List Byte) (P₀ : Nat)
    (enc : Bool) (D : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  le : j ≤ n
  frame : Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m₀ s.mem
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  abs : Hyp → Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
    (x₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
  ctr : Hyp → Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P₀ + j)
  out : Hyp → bytesAt s.mem D j = xorKs (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem ctx_stFrame {D : Addr} {n : Nat} (hC : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) : ∀ r ∈ VG.Proof.AesGcm.X86_64.stFrame St W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact hC
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact t_c.symm

/-- The slots of `W` below `192` are outside `stFrame`. -/
theorem w_stFrame {D : Addr} {n d k : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) (h₁ : 128 ≤ d) (h₂ : d + k ≤ 192) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.stFrame St W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

/-- `J₀` is outside `stFrame`. -/
theorem j0_stFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) : ∀ r ∈ VG.Proof.AesGcm.X86_64.stFrame St W SP D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  have e : (⟨St, 16⟩ : Region) = ⟨St + BitVec.ofNat 64 0, 16⟩ := by rw [BitVec.add_zero]
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

omit L in
/-- The return address is outside `stFrame`. -/
theorem ret_stFrame {D : Addr} {n : Nat} (rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩)
    (rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) (rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.stFrame St W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rS.sub_right (Lay.stSub (by decide))
  · exact rD
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (n := 24) (k := 8) (by decide)

omit L in
/-- `crypt` over part of the data writes within `stFrame`. -/
theorem crFrame_st {D : Addr} {n j k : Nat} (hk : j + k ≤ n) {m m' : Mem}
    (hf : Frame (crFrame St W SP (D + BitVec.ofNat 64 j) k) m m') : Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hk⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem absFrame_st {D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (absFrame St W SP 16) m m') :
    Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem tFrame_st {D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (tFrame St W SP 16) m m') :
    Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem obFrame_st {D : Addr} {n j q : Nat} (hk : j + q * 16 ≤ n) {m m' : Mem}
    (hf : Frame (obFrame St W SP (D + BitVec.ofNat 64 j) q) m m') : Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hk⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

omit L in
theorem slots_st {D : Addr} {n d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) {m m' : Mem}
    (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') : Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit L in
/-- The accumulator and the buffer, through a frame apart from them. -/
theorem abs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r) {H : Block} {x : List Byte}
    (h : Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x) :
    Absorbed m' (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x := by
  have hl := Nat.mod_lt x.length (show 16 > 0 by decide)
  exact h.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))
    (bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by omega))) (by omega))

omit L in
/-- The counter and the keystream block, through a frame apart from them. -/
theorem ctr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r) {ciph : Block → Block} {icb : Block}
    {P : Nat} (h : Ctr m (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb P) :
    Ctr m' (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb P :=
  h.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))
    (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))

omit L in
/-- The rest of the data, after more of it is done. -/
theorem rest_step {D : Addr} {n j k : Nat} (hk : j + k ≤ n) (hn : n < 2 ^ 64) {m₀ m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨D + BitVec.ofNat 64 (j + k), n - (j + k)⟩ : Region).Disjoint r)
    (h : bytesAt m (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) :
    bytesAt m' (D + BitVec.ofNat 64 (j + k)) (n - (j + k)) = bytesAt m₀ (D + BitVec.ofNat 64 (j + k)) (n - (j + k)) := by
  rw [bytesAt_frame hf hd (by omega)]
  rw [show n - j = k + (n - (j + k)) by omega] at h
  have := (VG.Proof.AesGcm.X86_64.bytesAt_split_eq h).2
  rwa [add_ofNat_assoc] at this

omit L in
/-- The first bytes, from the rest. -/
theorem rest_head {D : Addr} {n j k : Nat} (hk : j + k ≤ n) {m₀ m : Mem}
    (h : bytesAt m (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) :
    bytesAt m (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := by
  rw [show n - j = k + (n - j - k) by omega] at h
  exact (VG.Proof.AesGcm.X86_64.bytesAt_split_eq h).1

end

section
variable {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat} {enc : Bool}
  {D : Addr} {n : Nat} {m₀ : Mem}

theorem SInv.rounds {j : Nat} {s : State} (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀)
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : RoundsAt s.mem W R :=
  rounds_frame h.frame (fun r hr => VG.Proof.AesGcm.X86_64.w_stFrame K.lay h.data.ok.w K.t_w (by decide) (by decide) r hr) K.rounds

theorem SInv.hH {j : Nat} {s : State} (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀)
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := by
  rw [blockAt_frame h.frame fun r hr => (VG.Proof.AesGcm.X86_64.ctx_stFrame K.lay h.data.ctx K.t_c r hr).sub_left (Lay.ctxSub (by decide)),
    K.hH]

theorem SInv.ciph {j : Nat} {s : State} (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀)
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R :=
  ciph_frame h.frame (VG.Proof.AesGcm.X86_64.ctx_stFrame K.lay h.data.ctx K.t_c) K.rounds.2

/-- After code changing registers other than those `Env` holds. -/
theorem SInv.regs {j : Nat} {s s' : State} (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s' :=
  ⟨h.env.keep hg hrd hwr, h.data.of_eq hrd hwr, h.le, hm ▸ h.frame, hm ▸ h.rest, fun hy => hm ▸ h.abs hy,
    fun hy => hm ▸ h.ctr hy, fun hy => hm ▸ h.out hy⟩

/-- After code writing only the slots of `W` from `192`. -/
theorem SInv.slots {j : Nat} {s s' : State} (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀)
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] s.mem s'.mem) :
    VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s' := by
  have L := K.lay
  have hD := h.data.ok
  have one : ∀ {r : Region}, r.Disjoint ⟨W, 2560⟩ → ∀ r' ∈ [(⟨W + BitVec.ofNat 64 d, k⟩ : Region)], r.Disjoint r' :=
    fun hr r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr.sub_right (Lay.wSub (by omega))
  have hlt := hD.lt
  have hj := h.le
  refine ⟨h.env.keep hg hrd hwr, h.data.of_eq hrd hwr, h.le, h.frame.trans (VG.Proof.AesGcm.X86_64.slots_st h₁ h₂ hf), ?_,
    fun hy => VG.Proof.AesGcm.X86_64.abs_frame hf (fun r hr => ?_) (h.abs hy), fun hy => VG.Proof.AesGcm.X86_64.ctr_frame hf (fun r hr => ?_) (h.ctr hy),
    fun hy => by rw [bytesAt_frame hf (one (hD.w.sub_left (Region.sub_prefix h.le))) (by omega)]; exact h.out hy⟩
  · rw [bytesAt_frame hf (one (hD.w.sub_left (Offset.sub_base D (by omega)))) (by omega)]; exact h.rest
  · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by omega, by omega⟩)
  · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by omega, by omega⟩)

end

/-! ## The blocks of code between the calls -/

section
variable {Ctx St W SP : Addr}

/-- The data kept, its length and the text so far modulo 16. -/
theorem load_ok {s : State} (he : Env Ctx St W SP s) {Dj : Addr} {k : Nat} {T : BitVec 64}
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = T) :
    ∃ s', runBlock isa streamLoad s = some s' ∧ s'.gpr .r12 = Dj ∧ s'.gpr .rbp = BitVec.ofNat 64 k ∧
      s'.gpr .rbx = BitVec.ofNat 64 (T.toNat % 16) ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamLoad
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have hand := and15 T
  rw [imm_eq (by decide)] at hand
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hdat]
  · simp [gpr_setReg, hlen]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, htl, hand]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

theorem load_env {s s' : State}
    (hg : ∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s'.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)

/-- Whether there are fewer than 256 bytes. -/
theorem small_ok (s : State) {n : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ s', runBlock isa streamSmall s = some s' ∧ s'.cf = some (decide (n < 256)) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamSmall
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_setReg, ite_true, hbp, setWidth_imm, toNat_ofNat_of_lt hn,
      toNat_ofNat_of_lt (show 256 < 2 ^ 64 by decide), show (256 : Nat) % 2 ^ 32 = 256 from rfl]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals rfl

/-- The length of the head. -/
def headLen (P n : Nat) : Nat := if P % 16 = 0 then 0 else min (16 - P % 16) n

theorem headLen_le (P n : Nat) : VG.Proof.AesGcm.X86_64.headLen P n ≤ n := by unfold VG.Proof.AesGcm.X86_64.headLen; split <;> omega

/-- After the head, the text so far is a whole number of blocks, unless
the data is used up. -/
theorem headLen_whole (P n : Nat) : n - VG.Proof.AesGcm.X86_64.headLen P n = 0 ∨ (P + VG.Proof.AesGcm.X86_64.headLen P n) % 16 = 0 := by
  unfold VG.Proof.AesGcm.X86_64.headLen; split <;> omega

/-- `streamHead`: the length of the head, kept and in `rbp`, and the whole
length at `auxO`. -/
theorem sHead_ok {s : State} (he : Env Ctx St W SP s) {P n : Nat} (hn : n < 2 ^ 64)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 (P % 16)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n) :
    WP isa streamHead s fun s' => s'.gpr .rbp = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.headLen P n) ∧
      (∀ r, r ≠ .rbp → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.headLen P n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      Frame [⟨W + BitVec.ofNat 64 208, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := Nat.mod_lt P (show 16 > 0 by decide)
  have w₁ := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have hz := and_self_beq (show P % 16 < 2 ^ 64 by omega)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.store (at_ .r15 auxO) .rbp,
      .alu .test .rbx (.reg .rbx)] s = some s₁ ∧ s₁.zf = some (decide (P % 16 = 0)) ∧ s₁.gpr = s.gpr ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 n) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbx, hz]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg, gpr_arithFlags,
      he.r15, hbp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hbx₁ : s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) := by rw [hg₁, hbx]
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 n := by rw [hg₁, hbp]
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.headLen P n) ∧
      (∀ r, r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    (WP.ite (decide (P % 16 = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)) fun s₂ h₂ => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    apply WP.of_runBlock
    refine ⟨_, by xrun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, VG.Proof.AesGcm.X86_64.headLen, h0, imm_eq]
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_setReg, rd_setReg, wr_setReg]
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    refine WP.mono (minLen_ok s₁ hbx₁ hbp₁ (by omega) hn) fun s₂ ⟨hcx, hg, hm, hrd, hwr⟩ => ⟨?_, hg, hm, hrd, hwr⟩
    rw [hcx]; simp only [VG.Proof.AesGcm.X86_64.headLen, h0, ↓reduceIte]
  obtain ⟨hcx, hg₂, hm₂, hrd₂, hwr₂⟩ := h₂
  have h15 : s₂.gpr .r15 = W := by rw [hg₂ _ (by decide), hg₁, he.r15]
  have w₂' : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 208) 8 := by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact in_left w₂
  have w₂'' : InRegions s₂.wr (W + BitVec.ofNat 64 208) 8 := by rw [hwr₂, hwr₁]; exact w₂
  apply WP.of_runBlock
  have sep : Mem.Sep (W + BitVec.ofNat 64 216) (64 / 8) (W + BitVec.ofNat 64 208) (64 / 8) :=
    Offset.sep _ (.inr (by decide)) (by omega) (by omega)
  refine ⟨_, by xrun [h15, w₂'', hcx], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hcx]
  · intro r a b; simp [gpr_setReg, a, b, hg₂ r b, hg₁]
  · simp [mem_setReg, Mem.readW_writeW_self64]
  · simp only [mem_setReg, hm₂, hm₁]
    rw [Mem.readW_writeW_sep (sep_of_disj (Offset.disjoint _ (.inr (by decide)) (by omega)
      (by omega))) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_setReg, hm₂, hm₁]
    have c : ∀ d, 208 ≤ d → d + 8 ≤ 224 → (⟨W + BitVec.ofNat 64 208, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  all_goals simp [rd_setReg, wr_setReg, hrd₂, hwr₂, hrd₁, hwr₁]

/-- `streamNext`: past the head of `k` bytes, of `n`. -/
theorem next_ok {s : State} (he : Env Ctx St W SP s) {D : Addr} {P k n : Nat} (hk : k ≤ n) (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P)
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.block streamNext) s fun s' => (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 k ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P + k) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - k) ∧
      Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamNext
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₄ := he.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a ≤ 2560 → d ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have eadd : BitVec.ofNat 64 P + BitVec.ofNat 64 k = BitVec.ofNat 64 (P + k) := (BitVec.ofNat_add _ _).symm
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := ofNat_sub hk hn
  have e₁ : (s.mem.writeW (W + BitVec.ofNat 64 200) (D + BitVec.ofNat 64 k)).readW (W + BitVec.ofNat 64 192) 64 =
      BitVec.ofNat 64 P := by rw [Mem.readW_writeW_sep (sep 192 200 (by decide) (by decide) (by decide)) (by decide), htl]
  have e₂ : ((s.mem.writeW (W + BitVec.ofNat 64 200) (D + BitVec.ofNat 64 k)).writeW (W + BitVec.ofNat 64 192)
      (BitVec.ofNat 64 (P + k))).readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [Mem.readW_writeW_sep (sep 216 192 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 216 200 (by decide) (by decide) (by decide)) (by decide), haux]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, q₄, w₁, w₂, w₃, hlen, hdat, eadd, e₁, e₂, esub], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 200 208 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 200 192 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 192 208 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_self64]
  · have c : ∀ d, 192 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 192, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

/-! ## Regions the pieces write -/

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem slot_crFrame {s : State} {Dj : Addr} {k d : Nat} (hd : DataOk St W SP s Dj k) (h₁ : 176 ≤ d)
    (h₂ : d + 8 ≤ 512) : ∀ r ∈ crFrame St W SP Dj k, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.w.sub_right (Lay.wSub (by omega))).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem slot_absFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ absFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem abs_crFrame {s : State} {Dj : Addr} {k : Nat} (hd : DataOk St W SP s Dj k) :
    ∀ r ∈ crFrame St W SP Dj k, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by decide)).symm

theorem ctr_absFrame : ∀ r ∈ absFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by decide)).symm

theorem ctxAll_absFrame : ∀ r ∈ absFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
/-- Part of the data, apart from the part `crypt` writes. -/
theorem dsub_crFrame {s : State} {D : Addr} {n j k e l : Nat} (hd : DataOk St W SP s D n) (hk : j + k ≤ n)
    (hel : e + l ≤ n) (hs : e + l ≤ j ∨ j + k ≤ e) :
    ∀ r ∈ crFrame St W SP (D + BitVec.ofNat 64 j) k, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 e, l⟩ ⟨D, n⟩ := Offset.sub_base D hel
  have hlt := hd.lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint D hs (by omega) (by omega)
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact (hd.w.sub_left hsub).sub_right (Lay.wSub (by decide))
  · exact (hd.stk.sub_right hsub).symm

omit L in
theorem dsub_absFrame {s : State} {D : Addr} {n e l : Nat} (hd : DataOk St W SP s D n) (hel : e + l ≤ n) :
    ∀ r ∈ absFrame St W SP 16, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := fun r hr =>
  (data_absFrame (yo := 16) (.inr rfl) hd r hr).sub_left (Offset.sub_base D hel)

end

theorem dprefix (D : Addr) (j : Nat) : (⟨D, j⟩ : Region) = ⟨D + BitVec.ofNat 64 0, j⟩ := by rw [BitVec.add_zero]

/-! ## A part of the data: `crypt` and `absorb` -/

section
variable (v : GcmImpl) {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `k` more bytes, from byte `j`: encrypted and absorbed, or absorbed and
decrypted. -/
theorem part_ok (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀) (enc : Bool) {j k : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s fun s' =>
      VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ (j + k) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have hdj : DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k := (hD.drop hj).take (by omega)
  have hR := h.rounds K
  have hH := h.hH K
  have hc := h.ciph K
  have hin : bytesAt s.mem (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := VG.Proof.AesGcm.X86_64.rest_head hk h.rest
  have hxl : (x₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = (P₀ + j) % 16 := by
    rw [List.length_append, VG.Proof.AesGcm.X86_64.length_ctext, length_bytesAt]; omega
  have hpre : ∀ r ∈ crFrame St W SP (D + BitVec.ofNat 64 j) k, (⟨D, j⟩ : Region).Disjoint r := by
    rw [VG.Proof.AesGcm.X86_64.dprefix]; exact VG.Proof.AesGcm.X86_64.dsub_crFrame hD.ok hk (by omega) (.inl (by omega))
  have hpreA : ∀ r ∈ absFrame St W SP 16, (⟨D, j⟩ : Region).Disjoint r := by
    rw [VG.Proof.AesGcm.X86_64.dprefix]; exact VG.Proof.AesGcm.X86_64.dsub_absFrame hD.ok (by omega)
  have hrestC := VG.Proof.AesGcm.X86_64.dsub_crFrame hD.ok hk (e := j + k) (l := n - (j + k)) (by omega) (.inr (by omega))
  have hrestA := VG.Proof.AesGcm.X86_64.dsub_absFrame hD.ok (e := j + k) (l := n - (j + k)) (by omega)
  cases enc
  · -- Decrypting: the ciphertext absorbed, then decrypted.
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hai : AbsIn Ctx St W SP 16 H (x₀ ++ VG.Proof.AesGcm.X86_64.ctext false (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s := ⟨h.env, h12, hbp, by rw [hbx, hxl], hdj.ok, hH⟩
    refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₂ ⟨ao, rd₂, wr₂⟩ => ?_)
    have sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.slot_absFrame L h₁ (by omega))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := VG.Proof.AesGcm.X86_64.load_ok ao.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ := ao.env.keep (VG.Proof.AesGcm.X86_64.load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    have hc₂ : ciphOf s₂.mem Ctx R = ciphOf m₀ Ctx R := by rw [ciph_frame ao.frame (VG.Proof.AesGcm.X86_64.ctxAll_absFrame L) hR.2, hc]
    have hR₃ : RoundsAt s₃.mem W R := hm₃ ▸ rounds_frame ao.frame (VG.Proof.AesGcm.X86_64.slot_absFrame L (by decide) (by decide)) hR
    have hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    refine WP.mono (WP.with_rdwr (crypt_ok v L (icb := icb) ⟨he₃, h12₃, hbp₃, hbx₃, hdj₃, hR₃⟩))
      fun s₄ ⟨co, rd₄, wr₄⟩ => ⟨⟨co.env, hD.of_eq (by rw [rd₄, hrd₃, rd₂]) (by rw [wr₄, hwr₃, wr₂]), hk,
        h.frame.trans ((VG.Proof.AesGcm.X86_64.absFrame_st ao.frame).trans (hm₃ ▸ VG.Proof.AesGcm.X86_64.crFrame_st hk co.frame)), ?_, fun hy => ?_, fun hy => ?_,
        fun hy => ?_⟩, fun d h₁ h₂ => ?_⟩
    · rw [bytesAt_frame co.frame hrestC (by omega), hm₃, bytesAt_frame ao.frame hrestA (by omega)]
      exact VG.Proof.AesGcm.X86_64.rest_step hk hlt (Frame.refl (rs := []) _) (fun _ h => by cases h) h.rest
    · have A := VG.Proof.AesGcm.X86_64.abs_frame co.frame (VG.Proof.AesGcm.X86_64.abs_crFrame L hdj₃.ok) (hm₃ ▸ ao.abs (h.abs hy))
      rw [hin] at A
      simp only [VG.Proof.AesGcm.X86_64.ctext, Bool.false_eq_true, ↓reduceIte] at A ⊢
      rw [bytesAt_add, ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hm₃, hc₂] at C
      rw [← Nat.add_assoc]
      exact C (VG.Proof.AesGcm.X86_64.ctr_frame ao.frame (VG.Proof.AesGcm.X86_64.ctr_absFrame L) (h.ctr hy))
    · have C := co.out
      rw [hm₃, hc₂] at C
      have o := C (VG.Proof.AesGcm.X86_64.ctr_frame ao.frame (VG.Proof.AesGcm.X86_64.ctr_absFrame L) (h.ctr hy))
      rw [bytesAt_frame ao.frame (VG.Proof.AesGcm.X86_64.dsub_absFrame hD.ok (by omega)) (by omega), hin] at o
      refine done_append ?_ o
      rw [bytesAt_frame co.frame hpre (by omega), hm₃, bytesAt_frame ao.frame hpreA (by omega)]
      exact h.out hy
    · rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (VG.Proof.AesGcm.X86_64.slot_crFrame L hdj₃.ok h₁ (by omega)) (by decide), hm₃, sl₂ d h₁ h₂]
  · -- Encrypting: the plaintext encrypted, then the ciphertext absorbed.
    simp only [↓reduceIte]
    refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok v L (icb := icb) ⟨h.env, h12, hbp, hbx, hdj, hR⟩))
      fun s₂ ⟨co, rd₂, wr₂⟩ => ?_)
    have sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.slot_crFrame L hdj.ok h₁ (by omega))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := VG.Proof.AesGcm.X86_64.load_ok co.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ := co.env.keep (VG.Proof.AesGcm.X86_64.load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    have hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₃, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdj r hr).sub_left (Lay.ctxSub (by decide))), hH]
    have hai : AbsIn Ctx St W SP 16 H (x₀ ++ VG.Proof.AesGcm.X86_64.ctext true (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s₃ := ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hxl], hdj₃.ok, hH₃⟩
    refine WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai))
      fun s₄ ⟨ao, rd₄, wr₄⟩ => ⟨⟨ao.env, hD.of_eq (by rw [rd₄, hrd₃, rd₂]) (by rw [wr₄, hwr₃, wr₂]), hk,
        h.frame.trans ((VG.Proof.AesGcm.X86_64.crFrame_st hk co.frame).trans (hm₃ ▸ VG.Proof.AesGcm.X86_64.absFrame_st ao.frame)), ?_, fun hy => ?_, fun hy => ?_,
        fun hy => ?_⟩, fun d h₁ h₂ => ?_⟩
    · rw [bytesAt_frame ao.frame hrestA (by omega), hm₃]
      exact VG.Proof.AesGcm.X86_64.rest_step hk hlt co.frame hrestC h.rest
    · have C := co.out
      rw [hc] at C
      have o := C (h.ctr hy)
      rw [hin] at o
      have A := ao.abs (hm₃ ▸ VG.Proof.AesGcm.X86_64.abs_frame co.frame (VG.Proof.AesGcm.X86_64.abs_crFrame L hdj.ok) (h.abs hy))
      rw [hm₃, o] at A
      rw [bytesAt_add, VG.Proof.AesGcm.X86_64.ctext_append, length_bytesAt, ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc] at C
      rw [← Nat.add_assoc]
      exact VG.Proof.AesGcm.X86_64.ctr_frame ao.frame (VG.Proof.AesGcm.X86_64.ctr_absFrame L) (hm₃ ▸ C (h.ctr hy))
    · have C := co.out
      rw [hc] at C
      have o := C (h.ctr hy)
      rw [hin] at o
      refine done_append ?_ ?_
      · rw [bytesAt_frame ao.frame hpreA (by omega), hm₃, bytesAt_frame co.frame hpre (by omega)]
        exact h.out hy
      · rw [bytesAt_frame ao.frame (VG.Proof.AesGcm.X86_64.dsub_absFrame hD.ok (by omega)) (by omega), hm₃]
        exact o
    · rw [ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (VG.Proof.AesGcm.X86_64.slot_absFrame L h₁ (by omega)) (by decide), hm₃, sl₂ d h₁ h₂]

end

/-! ## The whole blocks: one call -/

section
variable {Ctx St W SP : Addr}

/-- The number of whole blocks left. -/
theorem sb1_ok {L : Nat} (hL : L < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) s fun s₁ =>
      s₁.gpr .rax = BitVec.ofNat 64 (L / 16) ∧ s₁.zf = some (decide (L / 16 = 0)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have h4 := shr4 L hL
  have hz := and_self_beq (show L / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hlen, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- After the call: the data kept, its length and the text so far past the
whole blocks. -/
theorem sb3_ok {Dj : Addr} {L T : Nat} (hL : L < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 L)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 T) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
      .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 dataO)),
      .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx, .mov .rcx (.mem (at_ .r15 tlenO)),
      .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx]) s fun s₅ =>
      (∀ r, r ≠ .rax → r ≠ .rcx → s₅.gpr r = s.gpr r) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj + BitVec.ofNat 64 (16 * (L / 16)) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (L % 16) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (T + 16 * (L / 16)) ∧
      Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem s₅.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 L)
  rw [toNat_ofNat_of_lt hL, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 L - BitVec.ofNat 64 (L % 16) = BitVec.ofNat 64 (16 * (L / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hL]; congr 1; omega
  have eadd : BitVec.ofNat 64 T + BitVec.ofNat 64 (16 * (L / 16)) = BitVec.ofNat 64 (T + 16 * (L / 16)) :=
    (BitVec.ofNat_add _ _).symm
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a ≤ 2560 → d ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have e₁ : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (L % 16))).readW (W + BitVec.ofNat 64 200) 64 = Dj := by
    rw [Mem.readW_writeW_sep (sep 200 208 (by decide) (by decide) (by decide)) (by decide), hdat]
  have e₂ : ((s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (L % 16))).writeW (W + BitVec.ofNat 64 200)
      (Dj + BitVec.ofNat 64 (16 * (L / 16)))).readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 T := by
    rw [Mem.readW_writeW_sep (sep 192 200 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 192 208 (by decide) (by decide) (by decide)) (by decide), htl]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, w₁, w₂, w₃, hlen, e15, esub, e₁, e₂, eadd], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 200 192 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 208 192 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 208 200 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_self64]
  · have c : ∀ d, 192 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 192, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The call of `vg_aes_gcm_encrypt_blocks` (`enc`) or `_decrypt_blocks`:
GHASH absorbs the ciphertext, which it writes or reads. -/
theorem callBlocks_ok (enc : Bool) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call (if enc then v.callees.enc else v.callees.dec).name
      (if enc then v.callees.enc else v.callees.dec).code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (St + BitVec.ofNat 64 48))
        (blocksAt s.mem D q) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (St + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
        (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt (if enc then s₄.mem else s.mem) D q) := by
  cases enc
  · exact obFrameD_ok L v h
  · exact obFrameE_ok L v h

/-- The slots of `W` are outside what the call writes. -/
theorem slot_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hq : q * 16 ≤ k)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 240) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

omit L in
/-- Part of the data, apart from the whole blocks the call writes. -/
theorem dsub_obFrame {s : State} {D : Addr} {n j q e l : Nat} (hd : DataOk St W SP s D n)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (hk : j + q * 16 ≤ n) (hel : e + l ≤ n) (hs : e + l ≤ j ∨ j + q * 16 ≤ e) :
    ∀ r ∈ obFrame St W SP (D + BitVec.ofNat 64 j) q, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 e, l⟩ ⟨D, n⟩ := Offset.sub_base D hel
  have hlt := hd.lt
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint D hs (by omega) (by omega)
  · exact (hd.w.sub_left hsub).sub_right (Lay.wSub (by decide))
  · exact (t_d.sub_right hsub).symm

theorem buf_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨St, 80⟩) (hq : q * 16 ≤ k)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨St + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

theorem ks_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨St, 80⟩) (hq : q * 16 ≤ k)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

end

section
variable (v : GcmImpl) {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamBlocks`: the whole blocks of the data left, from byte `j`, in one
call, when the text so far is a whole number of blocks. -/
theorem blocks_ok (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀) (enc : Bool) {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) (hx : x₀.length % 16 = P₀ % 16)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j))
    (hal : (n - j) / 16 ≠ 0 → (P₀ + j) % 16 = 0) :
    WP isa (streamBlocks (if enc then v.callees.enc else v.callees.dec)) s fun s' =>
      VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ (j + 16 * ((n - j) / 16)) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - j) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (j + 16 * ((n - j) / 16))) := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have he := h.env
  generalize hq : (n - j) / 16 = q
  unfold streamBlocks
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.sb1_ok (L := n - j) (by omega) he hlen) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at r₁ z₁
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have h₁ : VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s₁ := h.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (q = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    subst hz
    refine WP.block_nil ⟨by simpa using h₁, by rw [m₁, hdat]; simp, by rw [m₁, hlen]; congr 1; omega,
      by rw [m₁, htl]; simp⟩
  · simp only [decide_eq_false_iff_not] at hz
    have h0 : (P₀ + j) % 16 = 0 := hal (by omega)
    have hqk : j + q * 16 ≤ n := by omega
    have hR₁ := h₁.rounds K
    refine WP.seq (WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ hR₁ (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    have m₂' : s₂.mem = s.mem := m₂.trans m₁
    have hdq : DataW Ctx St W SP s₂ (D + BitVec.ofNat 64 j) (n - j) := (hD.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)
    have obi : ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) q s₂ := ⟨he₂, hdq, by omega, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s⟩
    refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.callBlocks_ok v L enc obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₁, o₂, o₃⟩ => ?_)
    have he₄ : Env Ctx St W SP s₄ := he₂.of_saved cs₄ rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.slot_obFrame L hdq.ok.w (by omega) K.t_w h₁ h₂) (by decide), m₂']
    refine WP.mono (VG.Proof.AesGcm.X86_64.sb3_ok (L := n - j) (by omega) he₄ ((kp 200 (by decide) (by decide)).trans hdat)
      ((kp 208 (by decide) (by decide)).trans hlen) ((kp 192 (by decide) (by decide)).trans htl))
      fun s₅ ⟨g₅, d₅, l₅, t₅, f₅, rd₅, wr₅⟩ => ?_
    rw [hq] at d₅ t₅
    have he₅ : Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)) rd₅ wr₅
    have one : ∀ {r : Region}, r.Disjoint ⟨W, 2560⟩ → ∀ r' ∈ [(⟨W + BitVec.ofNat 64 192, 24⟩ : Region)],
        r.Disjoint r' := fun hr r' h' => by
      simp only [List.mem_singleton] at h'; subst h'; exact hr.sub_right (Lay.wSub (by decide))
    -- What the call did, from `m₀`.
    rw [m₂'] at o₁ o₂ o₃
    have hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R := h.ciph K
    have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := h.hH K
    rw [hc] at o₁
    rw [hH] at o₃
    have hin : bytesAt s.mem (D + BitVec.ofNat 64 j) (16 * q) = bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * q) :=
      VG.Proof.AesGcm.X86_64.rest_head (by omega) h.rest
    have hkd := Offset.sub_base D (d := j) (n := 16 * q) (k := n) (by omega)
    refine ⟨⟨he₅, hD.of_eq (by rw [rd₅, rd₄, rd₂, rd₁]) (by rw [wr₅, wr₄, wr₂, wr₁]), by omega,
      h.frame.trans ((m₂' ▸ VG.Proof.AesGcm.X86_64.obFrame_st hqk fr₄).trans (VG.Proof.AesGcm.X86_64.slots_st (Nat.le_refl _) (by decide) f₅)), ?_, fun hy => ?_,
      fun hy => ?_, fun hy => ?_⟩, by rw [d₅, add_ofNat_assoc], l₅,
      by rw [t₅, Nat.add_assoc]⟩
    · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left (Offset.sub_base D (by omega)))) (by omega)]
      exact VG.Proof.AesGcm.X86_64.rest_step (k := 16 * q) (by omega) hlt fr₄
        (VG.Proof.AesGcm.X86_64.dsub_obFrame hD.ok K.t_d hqk (by omega) (.inr (by omega))) (by rw [m₂']; exact h.rest)
    · have hx0 : (x₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = 0 := by
        rw [List.length_append, VG.Proof.AesGcm.X86_64.length_ctext, length_bytesAt]; omega
      have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      have hZ : bytesAt (if enc then s₄.mem else s.mem) (D + BitVec.ofNat 64 j) (16 * q) =
          VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb (P₀ + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * q)) := by
        cases enc
        · simp only [Bool.false_eq_true, ↓reduceIte, VG.Proof.AesGcm.X86_64.ctext]; exact hin
        · simp only [↓reduceIte, VG.Proof.AesGcm.X86_64.ctext]; rw [cw.1, hin]
      have A₄ := Proof.Gcm.absorb_whole (m' := s₄.mem)
        (d := bytesAt (if enc then s₄.mem else s.mem) (D + BitVec.ofNat 64 j) (16 * q)) (h.abs hy) hx0
        (by rw [length_bytesAt]; omega) (by rw [o₃, Proof.Gcm.blocksAt_eq])
      have A₅ := VG.Proof.AesGcm.X86_64.abs_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)) A₄
      rw [hZ] at A₅
      rw [bytesAt_add, VG.Proof.AesGcm.X86_64.ctext_append, length_bytesAt, ← List.append_assoc]
      exact A₅
    · have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      rw [← Nat.add_assoc]
      exact VG.Proof.AesGcm.X86_64.ctr_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)) cw.2
    · have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      refine done_append ?_ ?_
      · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left (Region.sub_prefix hj))) (by omega),
          bytesAt_frame fr₄ (by rw [VG.Proof.AesGcm.X86_64.dprefix]; exact VG.Proof.AesGcm.X86_64.dsub_obFrame hD.ok K.t_d hqk (by omega) (.inl (by omega)))
            (by omega), m₂']
        exact h.out hy
      · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left hkd)) (by omega), cw.1, hin]

end

/-! ## The start, and all of `streamText` -/

section
variable (v : GcmImpl) {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- The additional data padded, if there is no text yet: then `SInv` holds,
with nothing done. -/
theorem start_ok (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀) (enc : Bool) {s : State} (he : Env Ctx St W SP s)
    (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n) {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s fun s' =>
      VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  have L := K.lay
  have hlt := hd.ok.lt
  have r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (c₀.length = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  have hm₂' : s₂.mem = m₀ := hm₂.trans hm
  have hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H := K.hH
  have dD : ∀ r ∈ tFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hd.ok.st.sub_right (Lay.stSub (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · exact hd.ok.stk.symm
  have cT : ∀ r ∈ tFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.st_st (.inr (by decide)) (by decide) (by decide)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by decide)).symm
  have sT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  -- From a state with the padded additional data absorbed.
  have fin : ∀ s₄ : State, Env Ctx St W SP s₄ → s₄.rd = s.rd → s₄.wr = s.wr → Frame (tFrame St W SP 16) m₀ s₄.mem →
      (Hyp → Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length) ++ c₀)) →
      VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s₄ ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun s₄ he₄ rd₄ wr₄ f₄ ha => ⟨⟨he₄, hd.of_eq rd₄ wr₄, Nat.zero_le _, VG.Proof.AesGcm.X86_64.tFrame_st f₄,
      by simpa using bytesAt_frame f₄ dD (by omega),
      fun hy => by simpa [VG.Proof.AesGcm.X86_64.bytesAt_zero, VG.Proof.AesGcm.X86_64.ctext_nil] using ha hy,
      fun hy => by simpa using VG.Proof.AesGcm.X86_64.ctr_frame f₄ cT (hyC hy), fun _ => rfl⟩,
      fun d h₁ h₂ => by
        rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (sT d h₁ (by omega)) (by decide), hm]⟩
  refine WP.ite (decide (c₀.length = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_)
  · have hc : c₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
    subst hc
    have r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
    obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
        (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
      have hand := and15 (BitVec.ofNat 64 a.length)
      rw [imm_eq (by decide), toNat_mod16] at hand
      refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    unfold firstFlush
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    have hm₃' : s₃.mem = m₀ := hm₃.trans hm₂'
    refine WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (H := H) (x := a) ⟨he₃, by rw [hm₃']; exact hH⟩
      hbx₃)) fun s₄ ⟨fo, rd₄, wr₄⟩ => fin s₄ fo.env (by rw [rd₄, hrd₃, hrd₂]) (by rw [wr₄, hwr₃, hwr₂])
        (hm₃' ▸ fo.frame) fun hy => ?_
    rw [List.append_nil]
    exact fo.abs (by rw [hm₃']; exact hyA hy)
  · have hc : c₀ ≠ [] := fun e => by subst e; simp_all
    refine WP.block_nil (fin s₂ he₂ hrd₂ hwr₂ (by rw [hm₂']; exact Frame.refl _ _) fun hy => ?_)
    rw [hm₂', ← Proof.Gcm.ghashInput_of_ne hc]
    exact hyA hy

end

section
variable (v : GcmImpl) {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamText enc`: the `n` bytes at `D` encrypted (`enc`) or decrypted,
and their ciphertext absorbed, after additional data `a` and text `c₀`. -/
theorem streamText_ok (K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀) (enc : Bool) {s : State} (he : Env Ctx St W SP s)
    (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamText v.callees enc) s fun s' => Env Ctx St W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := by
  suffices WP isa (streamText v.callees enc) s fun s' => Env Ctx St W SP s' ∧ Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) from
    WP.mono (WP.with_rdwr this) fun _ ⟨⟨a, b, c⟩, d, e⟩ => ⟨a, d, e, b, c⟩
  have hlt := hd.ok.lt
  have hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega
  simp only [streamText]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₁, by rw [hm₁, hm]; exact Frame.refl _ _, fun hy => ⟨?_, ?_, rfl⟩⟩
    · rw [VG.Proof.AesGcm.X86_64.bytesAt_zero, VG.Proof.AesGcm.X86_64.ctext_nil, List.append_nil, hm₁, hm]; exact hyA hy
    · rw [hm₁, hm]; exact hyC hy
  have h0 : n ≠ 0 := by simpa using hf
  have sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.start_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁) (c₀ := c₀) hP
    (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC) fun s₂ ⟨I₂, sl₂⟩ => ?_))
  -- The head.
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := VG.Proof.AesGcm.X86_64.load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  have I₃ := I₂.regs (VG.Proof.AesGcm.X86_64.load_env hg₃) hm₃ hrd₃ hwr₃
  have sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  -- The end, from `SInv` over all the data.
  have fin : ∀ s', VG.Proof.AesGcm.X86_64.SInv Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ n s' →
      Env Ctx St W SP s' ∧ Frame (VG.Proof.AesGcm.X86_64.stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := fun s' I => by
    refine ⟨I.env, I.frame, fun hy => ⟨?_, I.ctr hy, I.out hy⟩⟩
    have hne : c₀ ++ VG.Proof.AesGcm.X86_64.ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n) ≠ [] := fun e => h0 (by
      have := congrArg List.length e
      rw [List.length_append, VG.Proof.AesGcm.X86_64.length_ctext, length_bytesAt, List.length_nil] at this
      omega)
    rw [Proof.Gcm.ghashInput_of_ne hne, ← List.append_assoc]
    exact I.abs hy
  -- Fewer than 256 bytes: all of them at once.
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := VG.Proof.AesGcm.X86_64.small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  have I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  have h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  have hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  have hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  have sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => ?_) (fun _ => ?_)
  · refine WP.mono (VG.Proof.AesGcm.X86_64.part_ok v K enc I₃' hx (j := 0) (k := n) (by omega) (by simp [h12₃']) hbp₃'
      (by rw [hbx₃', Nat.add_zero]) (by rw [sl₃' 200 (by decide) (by decide), hdat]; simp)
      (by rw [sl₃' 208 (by decide) (by decide), hlen]) (by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero]))
      fun s' ⟨I, _⟩ => fin s' (by rw [Nat.zero_add] at I; exact I)
  -- The head.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
  generalize hk : VG.Proof.AesGcm.X86_64.headLen c₀.length n = k at hbp₄ hl₄
  have hkn : k ≤ n := hk ▸ VG.Proof.AesGcm.X86_64.headLen_le c₀.length n
  have hkw := VG.Proof.AesGcm.X86_64.headLen_whole c₀.length n
  rw [hk] at hkw
  have g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
  have I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
  have sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K.lay.w_w (.inl (by omega)) (by omega) (by decide)) (by decide), sl₃' d h₁ (by omega)]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.part_ok v K enc I₄ hx (j := 0) (k := k) (by omega) (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
    hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
    (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero])) fun s₅ ⟨I₅, sl₅⟩ => ?_)
  -- Past the head.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
    (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
    (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
    (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
  have I₆ := I₅.slots K (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
  rw [Nat.zero_add] at I₆
  -- The whole blocks.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.blocks_ok v K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega)))
    fun s₇ ⟨I₇, d₇, l₇, t₇⟩ => ?_)
  generalize hj₂ : k + 16 * ((n - k) / 16) = j₂ at I₇ d₇ t₇
  -- The rest.
  obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := VG.Proof.AesGcm.X86_64.load_ok I₇.env d₇ l₇ t₇
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  rw [toNat_mod16] at hbx₈
  have I₈ := I₇.regs (VG.Proof.AesGcm.X86_64.load_env hg₈) hm₈ hrd₈ hwr₈
  refine WP.mono (VG.Proof.AesGcm.X86_64.part_ok v K enc I₈ hx (j := j₂) (k := (n - k) % 16) (by omega) h12₈ hbp₈ hbx₈
    (by rw [hm₈]; exact d₇) (by rw [hm₈]; exact l₇) (by rw [hm₈]; exact t₇)) fun s' ⟨I, _⟩ => ?_
  have hn : j₂ + (n - k) % 16 = n := by omega
  rw [hn] at I
  exact fin s' I

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamRun`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry (`cryptEntry_ok`),
the text (`streamText_ok`) and the exit, for any message the state
represents (`streamText_run`): encrypting appends the ciphertext it writes
(`streamEncrypt_wp`), decrypting the ciphertext it reads (`streamDecrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamText_run (v : GcmImpl) (enc : Bool) {s : State} (hp : Proof.AesGcm.streamCryptPre s)
    {iv a c₀ : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block VG.Impl.AesGcm.X86_64.restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a
          (c₀ ++ VG.Proof.AesGcm.X86_64.ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) ∧
        bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) := by
  have C := CryptCtx.of hp
  have hR := C.rounds
  have hP : c₀.length < 2 ^ 64 := hT ▸ (s.gpr .r8).isLt
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx R = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [VG.Proof.AesGcm.X86_64.entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (by decide))), ← hH, ctxH_eq]
  have hc₁ : ciphOf s₁.mem Ctx R = ciph := by rw [ciph_frame E.frame dCE hR, ← hciph]; rfl
  have K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n s₁.mem := ⟨L, hRo, hH₁, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24⟩
  have eS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [VG.Proof.AesGcm.X86_64.entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have hyA : StreamRepr s.mem St ciph H iv a c₀ → Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀) :=
    fun hy => by
      rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hy
      exact VG.Proof.AesGcm.X86_64.abs_frame E.frame (eS (by decide)) hy.2.1
  have hyC : StreamRepr s.mem St ciph H iv a c₀ → Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx R) icb
      c₀.length := fun hy => by
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hicb] at hy
    rw [hc₁]
    exact VG.Proof.AesGcm.X86_64.ctr_frame E.frame (eS (by decide)) hy.2.2
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.streamText_ok v K enc E.env rfl (C.data.of_eq E.rd E.wr) E.rbp hP (E.alen.trans hA) htl
    E.dat E.len hyA hyC) fun s₂ ⟨he₂, rd₂, wr₂, f₂, hq⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (VG.Proof.AesGcm.X86_64.w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (VG.Proof.AesGcm.X86_64.ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hy => ?_⟩
  rw [hicb]
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide)))
    (by have := C.data.ok.lt; omega)
  obtain ⟨qa, qc, qo⟩ := hq hy
  simp only [hc₁, hd₁] at qa qc qo
  refine ⟨?_, by rw [hm]; exact qo⟩
  have hj := hy
  rw [Proof.Gcm.streamRepr_iff] at hj ⊢
  rw [ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, hicb, List.length_append, VG.Proof.AesGcm.X86_64.length_ctext, length_bytesAt]
  refine ⟨?_, qa, qc⟩
  rw [← hj.1]
  have e : St = St + BitVec.ofNat 64 0 := (BitVec.add_zero St).symm
  rw [blockAt_frame f₂ (VG.Proof.AesGcm.X86_64.j0_stFrame L C.data.ok.st C.t_s), e]
  exact blockAt_frame E.frame (eS (by decide))

/-- `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  have run : ∀ {iv a p : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (VG.Proof.AesGcm.X86_64.streamText_run v true hp (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [VG.Proof.AesGcm.X86_64.ctext, ↓reduceIte, Proof.Gcm.length_gctr] at h₁ h₂
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (p := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

/-- `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  have run : ∀ {iv a c : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (VG.Proof.AesGcm.X86_64.streamText_run v false hp (iv := iv) (c₀ := c) hA hT)
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [VG.Proof.AesGcm.X86_64.ctext, Bool.false_eq_true, ↓reduceIte] at h₁
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (c := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. Both runs take the same
pieces of `streamText` (`streamText_rel`): the branches are on the length
of the data and of the text so far, the same in both; `crypt`, `absorb`,
`flush` and the call of the whole blocks are on data at the same address,
of the same length (`part_rel`, `blocks_rel`, `start_rel`); between them,
each run keeps `SInv` (with no hypotheses: `SI`), from the correctness
proofs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)

/-- Two runs, each with what it satisfies after `c`. -/
theorem rel_both {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True) (hw₁ : ∀ s, F₁ s → WP isa c s G₁)
    (hw₂ : ∀ s, F₂ s → WP isa c s G₂) : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp h (fun _ _ h => h) hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code whose leakage depends only on the registers `rs` and the
environment's. -/
theorem rel_envT {Ctx St W SP : Addr} {F : State → Prop} {c : Prog isa} (rs : List Reg)
    (hF : ∀ s, F s → Env Ctx St W SP s) (hag : ∀ s₁ s₂, F s₁ → F s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (rs ++ ([.r13, .r14, .r15, .rsp] : List Reg))) c hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) c fun _ _ => True :=
  rel_taint (rs ++ [.r13, .r14, .r15, .rsp]) (fun s₁ s₂ h r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hag _ _ h.1 h.2 r hr
    · exact env_agree (hF _ h.1) (hF _ h.2) r hr) hc

/-- One run between the pieces of `streamText`: `SInv`, with no hypotheses. -/
def SI (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  ∃ H icb x₀ m₀, VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀ ∧ x₀.length % 16 = P₀ % 16 ∧
    VG.Proof.AesGcm.X86_64.SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s

section
variable {Ctx St W SP : Addr} {R P₀ : Nat} {enc : Bool} {D : Addr} {n : Nat}

theorem SI.env {j : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s) : Env Ctx St W SP s :=
  let ⟨_, _, _, _, _, _, I⟩ := h; I.env

/-- What a piece does to `SInv`, to `SI`. -/
theorem SI.lift {j j' : Nat} {s : State} {c : Prog isa} {G : State → Prop} (h : VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s)
    (hw : ∀ {H icb x₀ m₀}, VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R H D n m₀ → x₀.length % 16 = P₀ % 16 →
      VG.Proof.AesGcm.X86_64.SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s →
      WP isa c s fun s' => VG.Proof.AesGcm.X86_64.SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j' s' ∧ G s') :
    WP isa c s fun s' => VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j' s' ∧ G s' := by
  obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := h
  exact WP.mono (hw K hx I) fun s' ⟨I', g⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, g⟩

theorem SI.regs {j : Nat} {s s' : State} (h : VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.regs hg hm hrd hwr⟩

theorem SI.slots {j : Nat} {s s' : State} (h : VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] s.mem s'.mem) :
    VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.slots K hg hrd hwr h₁ h₂ hf⟩

end

/-! ## A part of the data -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R P₀ : Nat} {D : Addr} {n : Nat}
include L

/-- Before `part`: what `part_ok` needs. -/
def PartPre (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j k : Nat) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s ∧ j + k ≤ n ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧
    s.gpr .rbp = BitVec.ofNat 64 k ∧ s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- Between `crypt` and `absorb`, in either order. -/
def PartMid (Ctx St W SP : Addr) (R P₀ : Nat) (D : Addr) (j k : Nat) (s : State) : Prop :=
  Env Ctx St W SP s ∧ RoundsAt s.mem W R ∧ DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

omit L in
theorem PartPre.mid {enc : Bool} {j k : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n j k s) :
    VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  exact ⟨⟨I.env, I.rounds K, (I.data.drop I.le).take (by have := I.le; omega), hdat, hlen, htl⟩, h12, hbp, hbx⟩

omit L in
theorem PartMid.crIn {j k : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    CrIn Ctx St W SP R 0 (P₀ + j) (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.1, h.1.2.1⟩

omit L in
theorem PartMid.absIn {j k : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    AbsIn Ctx St W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (List.replicate (P₀ + j) 0)
      (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, by rw [List.length_replicate]; exact h.2.2.2, h.1.2.2.1.ok, rfl⟩

omit L in
/-- The data reloaded. -/
theorem partMid_load {j k : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s) :
    WP isa (.block streamLoad) s fun s' => VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s' ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 j ∧ s'.gpr .rbp = BitVec.ofNat 64 k ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨he, hR, hd, hdat, hlen, htl⟩ := h
  obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := VG.Proof.AesGcm.X86_64.load_ok he hdat hlen htl
  rw [toNat_mod16] at hbx
  exact WP.of_runBlock ⟨s', run, ⟨he.keep (VG.Proof.AesGcm.X86_64.load_env hg) hrd hwr, hm ▸ hR, hd.of_eq hrd hwr, hm ▸ hdat, hm ▸ hlen,
    hm ▸ htl⟩, h12, hbp, hbx⟩

/-- After `crypt`. -/
theorem partMid_crypt {j k : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa (crypt v.callees) s (VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (crypt_ok v L (PartMid.crIn h))) fun s' ⟨co, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.slot_crFrame L hd.ok h₁ (by omega))
      (by decide)
  exact ⟨co.env, co.rounds, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

/-- After `absorb`. -/
theorem partMid_absorb {j k : Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa (absorb v.callees 16) s (VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) (PartMid.absIn h))) fun s' ⟨ao, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.slot_absFrame L h₁ (by omega))
      (by decide)
  exact ⟨ao.env, rounds_frame ao.frame (VG.Proof.AesGcm.X86_64.slot_absFrame L (by decide) (by decide)) h.1.2.1, hd.of_eq hrd hwr,
    by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

/-- `crypt` and `absorb` over the same part of the data in both runs. -/
theorem part_rel (enc : Bool) {j k : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n j k s₁ ∧ VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n j k s₂)
      (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) fun _ _ => True := by
  let M : State → Prop := fun s => VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧
    s.gpr .rbp = BitVec.ofNat 64 k ∧ s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)
  have cr : RelCT isa (fun s₁ s₂ => M s₁ ∧ M s₂) (crypt v.callees) fun _ _ => True :=
    (crypt_rel v L (icb₁ := 0) (icb₂ := 0) rfl).mono (fun _ _ h => ⟨PartMid.crIn h.1, PartMid.crIn h.2⟩)
      fun _ _ h => h
  have ab : RelCT isa (fun s₁ s₂ => M s₁ ∧ M s₂) (absorb v.callees 16) fun _ _ => True :=
    (RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => absorb_rel v L (yo := 16) (.inr rfl) (H₁ := H₁) (H₂ := H₂)
      (x₁ := List.replicate (P₀ + j) 0) (x₂ := List.replicate (P₀ + j) 0) rfl).mono
      (fun _ _ h => ⟨_, _, PartMid.absIn h.1, PartMid.absIn h.2⟩) fun _ _ h => h
  have ld := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := VG.Proof.AesGcm.X86_64.PartMid Ctx St W SP R P₀ D j k) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => VG.Proof.AesGcm.X86_64.partMid_load h) (fun _ h => VG.Proof.AesGcm.X86_64.partMid_load h)
  cases enc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (RelCT.seq (VG.Proof.AesGcm.X86_64.rel_both ab (fun _ h => VG.Proof.AesGcm.X86_64.partMid_absorb v L h) (fun _ h => VG.Proof.AesGcm.X86_64.partMid_absorb v L h))
      (RelCT.seq ld cr)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩) fun _ _ h => h
  · simp only [↓reduceIte]
    exact (RelCT.seq (VG.Proof.AesGcm.X86_64.rel_both cr (fun _ h => VG.Proof.AesGcm.X86_64.partMid_crypt v L h) (fun _ h => VG.Proof.AesGcm.X86_64.partMid_crypt v L h))
      (RelCT.seq ld ab)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩) fun _ _ h => h

end

/-! ## The whole blocks -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R P₀ : Nat} {D : Addr} {n : Nat}
include L

theorem callBlocks_rel (enc : Bool) {D' : Addr} {n' q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn Ctx St W SP R D' n' q s₁ ∧ ObIn Ctx St W SP R D' n' q s₂)
      (.frame (.push [.rax]) (.call (if enc then v.callees.enc else v.callees.dec).name
        (if enc then v.callees.enc else v.callees.dec).code) (.pop .rax 1)) fun _ _ => True := by
  cases enc
  · exact obFrameD_rel v L
  · exact obFrameE_rel v L

/-- Before `streamBlocks`: what `blocks_ok` needs. -/
def BPre (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n j s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- `streamBlocks`, with the same number of whole blocks, at the same
address, in both runs. -/
theorem blocks_rel (enc : Bool) {j : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n j s₁ ∧ VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n j s₂)
      (streamBlocks (if enc then v.callees.enc else v.callees.dec)) fun _ _ => True := by
  -- After the number of whole blocks: what the call's arguments need.
  let G₁ : State → Prop := fun s => s.zf = some (decide ((n - j) / 16 = 0)) ∧ Env Ctx St W SP s ∧
    ((n - j) / 16 ≠ 0 → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)))
  have g₁ : ∀ s, VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n j s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) s G₁ := fun s h => by
    obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hdat, hlen, htl⟩ := h
    have hlt := I.data.ok.lt
    have hj := I.le
    refine WP.mono (VG.Proof.AesGcm.X86_64.sb1_ok (L := n - j) (by omega) I.env hlen) fun s₁ ⟨r₁, z₁, g, m₁, rd₁, wr₁⟩ => ⟨z₁, ?_, fun hz => ?_⟩
    · exact I.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    have he₁ : Env Ctx St W SP s₁ := I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    refine WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ (m₁ ▸ I.rounds K) (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    exact ⟨he₂, (I.data.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s⟩
  have a := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n j) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) g₁ g₁
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)) :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := fun s => G₁ s ∧ s.zf = some false) [] (fun _ h => h.1.2.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩) hw₂ hw₂
  have hw₃ : ∀ s, ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16) s →
      WP isa (.frame (.push [.rax]) (.call (if enc then v.callees.enc else v.callees.dec).name
        (if enc then v.callees.enc else v.callees.dec).code) (.pop .rax 1)) s (Env Ctx St W SP) := fun s h =>
    WP.mono (VG.Proof.AesGcm.X86_64.callBlocks_ok v L enc h) fun _ o => h.env.of_saved o.1 o.2.1 o.2.2.1
  have c := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.callBlocks_rel v L enc) hw₃ hw₃
  have d := VG.Proof.AesGcm.X86_64.rel_envT (F := Env Ctx St W SP) (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax),
      .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx),
      .mov .rcx (.mem (at_ .r15 dataO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx,
      .mov .rcx (.mem (at_ .r15 tlenO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx])
    [] (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩
  unfold streamBlocks
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  exact (RelCT.seq b (RelCT.seq c d)).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩)
    fun _ _ h => h

end

/-! ## The start -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
/-- Whether there is text yet. -/
theorem tl_ok {P : Nat} (hP : P < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s fun s' =>
      s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' ∧ s'.mem = s.mem := by
  have r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₂, run₂, hz₂, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂, hm₂⟩

omit L in
/-- The length of the additional data modulo 16. -/
theorem al_ok {aL : Nat} {s : State} (he : Env Ctx St W SP s)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s' := by
  have r₃ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hand := and15 (BitVec.ofNat 64 aL)
  rw [imm_eq (by decide), toNat_mod16] at hand
  obtain ⟨s₃, run₃, hbx₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₃, run₃, hbx₃, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃⟩

/-- The additional data padded if there is no text yet, in both runs. -/
theorem start_rel {aL P : Nat} (hP : P < 2 ^ 64) {F : State → Prop} (hF : ∀ s, F s → Env Ctx St W SP s ∧
      s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P ∧
      s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) fun _ _ => True := by
  let G : State → Prop := fun s' => s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' ∧
    s'.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  have g : ∀ s, F s → WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s G :=
    fun s h => WP.mono (VG.Proof.AesGcm.X86_64.tl_ok hP (hF s h).1 (hF s h).2.1) fun s' ⟨z, e, m⟩ => ⟨z, e, by rw [m]; exact (hF s h).2.2⟩
  have a := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := F) [] (fun s h => (hF s h).1) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g g
  have b := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := fun s => G s ∧ s.zf = some true) [] (fun _ h => h.1.2.1)
      (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.AesGcm.X86_64.al_ok h.1.2.1 h.1.2.2) (fun s h => VG.Proof.AesGcm.X86_64.al_ok h.1.2.1 h.1.2.2)
  have c := (flush_rel v L (yo := 16) (.inr rfl)).mono (P' := fun (s₁ s₂ : State) =>
      (s₁.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₁) ∧
      (s₂.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₂))
    (fun _ _ h => ⟨h.1.2, h.2.2, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]⟩) fun _ _ h => h
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) ?_ (RelCT.block_nil fun _ _ _ => trivial))
  unfold firstFlush
  exact (RelCT.seq b c).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

/-! ## All of `streamText` -/

/-- Before `streamText`: what the entry leaves, in each run. -/
structure TPre (Ctx St W SP : Addr) (R aL P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  K : VG.Proof.AesGcm.X86_64.SCtx Ctx St W SP R (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) D n s.mem
  hP : P₀ < 2 ^ 64

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R aL P₀ : Nat} {D : Addr} {n : Nat}

/-- What `part_ok` does to `PartPre`. -/
theorem si_part (enc : Bool) {j k : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n j k s) :
    WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s fun s' =>
      VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n (j + k) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  let ⟨hs, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  hs.lift fun K hx I => VG.Proof.AesGcm.X86_64.part_ok v K enc I hx hk h12 hbp hbx hdat hlen htl

include L in
/-- `streamText` in two runs, with the same data and lengths. -/
theorem streamText_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.TPre Ctx St W SP R aL P₀ D n s₁ ∧ VG.Proof.AesGcm.X86_64.TPre Ctx St W SP R aL P₀ D n s₂)
      (streamText v.callees enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : VG.Proof.AesGcm.X86_64.headLen P₀ n = k
  have hkw := VG.Proof.AesGcm.X86_64.headLen_whole P₀ n
  have hkn := VG.Proof.AesGcm.X86_64.headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => VG.Proof.AesGcm.X86_64.TPre Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, VG.Proof.AesGcm.X86_64.TPre Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP⟩, hz⟩
  have a := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := VG.Proof.AesGcm.X86_64.TPre Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (VG.Proof.AesGcm.X86_64.start_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega
  have b := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.start_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₃ : ∀ s, G₂ s → WP isa (.block streamLoad) s G₃ := fun s h => by
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := VG.Proof.AesGcm.X86_64.load_ok h.1.env h.2.1 h.2.2.1 h.2.2.2
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, h.1.regs (VG.Proof.AesGcm.X86_64.load_env hg) hm hrd hwr, h12, hbp, hbx, hm ▸ h.2.1, hm ▸ h.2.2.1,
      hm ▸ h.2.2.2⟩
  have c := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := G₂) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₃ g₃
  -- Fewer than 256 bytes, or more.
  have g₃s : ∀ s, G₃ s → WP isa (.block streamSmall) s fun s' => G₃ s' ∧ s'.cf = some (decide (n < 256)) :=
    fun s h => by
      obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
      have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
      obtain ⟨s', run, hcf, hg, hm, hrd, hwr⟩ := VG.Proof.AesGcm.X86_64.small_ok s hbp hlt
      exact WP.of_runBlock ⟨s', run, ⟨hs.regs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hm hrd hwr,
        by rw [hg .r12 (by decide)]; exact h12, by rw [hg .rbp (by decide)]; exact hbp,
        by rw [hg .rbx (by decide)]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hcf⟩
  have cs := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := G₃) [.rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₃s g₃s
  have pp : ∀ s, G₃ s → VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  have gsm : ∀ s, VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s (Env Ctx St W SP) :=
    fun s h => WP.mono (VG.Proof.AesGcm.X86_64.si_part v enc h) fun _ h' => h'.1.env
  have sm := (VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.part_rel v L enc (j := 0) (k := n)) gsm gsm).mono (P' := fun (s₁ s₂ : State) =>
    ((G₃ s₁ ∧ s₁.cf = some (decide (n < 256))) ∧ (G₃ s₂ ∧ s₂.cf = some (decide (n < 256)))) ∧
      isa.eval .b s₁ = some true) (fun _ _ h => ⟨pp _ h.1.1.1, pp _ h.1.2.1⟩) fun _ _ h => h
  -- The head's length.
  let G₄ : State → Prop := fun s => VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n 0 k s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₄ : ∀ s, G₃ s → WP isa streamHead s G₄ := fun s h => by
    obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    refine WP.mono (VG.Proof.AesGcm.X86_64.sHead_ok hs.env hlt hbx hbp) fun s' ⟨hbp', hg, hl, ha, f, hrd, hwr⟩ => ?_
    rw [hk] at hbp' hl
    have rd : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by decide)
    refine ⟨⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (by decide) (by decide) f,
      by omega, by simp [hg .r12 (by decide) (by decide), h12], hbp',
      by rw [hg .rbx (by decide) (by decide), hbx, Nat.add_zero], by rw [rd 200 (by decide) (by decide), hdat]; simp, hl,
      by rw [rd 192 (by decide) (by decide), htl, Nat.add_zero]⟩, ha⟩
  have d := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₄ g₄
  -- The head.
  let G₅ : State → Prop := fun s => VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n k s ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀ ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₅ : ∀ s, G₄ s → WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s G₅ := fun s h => by
    obtain ⟨hp, ha⟩ := h
    have ⟨_, _, _, _, _, hdat, hlen, htl⟩ := hp
    refine WP.mono (VG.Proof.AesGcm.X86_64.si_part v enc hp) fun s' ⟨hs, sl⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.zero_add] at hs; exact hs
    · rw [sl 208 (by decide) (by decide)]; exact hlen
    · rw [sl 200 (by decide) (by decide), hdat]; simp
    · rw [sl 192 (by decide) (by decide), htl, Nat.add_zero]
    · rw [sl 216 (by decide) (by decide)]; exact ha
  have e := VG.Proof.AesGcm.X86_64.rel_both ((VG.Proof.AesGcm.X86_64.part_rel v L enc (j := 0) (k := k)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) g₅ g₅
  -- Past the head.
  have g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n k) := fun s h => by
    obtain ⟨hs, hl, hdat, htl, ha⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    exact WP.mono (VG.Proof.AesGcm.X86_64.next_ok hs.env hkn hlt hl hdat htl ha) fun s' ⟨hg, d', t', l', f, hrd, hwr⟩ =>
      ⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (Nat.le_refl _)
        (by decide) f, d', l', t'⟩
  have f := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := G₅) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₆ g₆
  -- The whole blocks.
  let G₇ : State → Prop := fun s => VG.Proof.AesGcm.X86_64.SI Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  have g₇ : ∀ s, VG.Proof.AesGcm.X86_64.BPre Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then v.callees.enc
      else v.callees.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (VG.Proof.AesGcm.X86_64.blocks_ok v K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  have g := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.blocks_rel v L enc) g₇ g₇
  -- The rest.
  have g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := VG.Proof.AesGcm.X86_64.load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (VG.Proof.AesGcm.X86_64.load_env hg) hm hrd hwr, by omega, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  have i := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  have g₉ : ∀ s, VG.Proof.AesGcm.X86_64.PartPre Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s (Env Ctx St W SP) :=
    fun s h => WP.mono (VG.Proof.AesGcm.X86_64.si_part v enc h) fun _ h' => h'.1.env
  have j := VG.Proof.AesGcm.X86_64.rel_both (VG.Proof.AesGcm.X86_64.part_rel v L enc) g₉ g₉
  simp only [streamText]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  have big := (RelCT.seq d (RelCT.seq e (RelCT.seq f (RelCT.seq g (RelCT.seq i j))))).mono
    (P' := fun (s₁ s₂ : State) => ((G₃ s₁ ∧ s₁.cf = some (decide (n < 256))) ∧ (G₃ s₂ ∧ s₂.cf = some (decide (n < 256)))) ∧
      isa.eval .b s₁ = some false) (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs
    (RelCT.ite (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm) sm big)))).mono
    (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)

end

/-! ## The functions -/

/-- After the entry, what `streamText` needs. -/
theorem cryptEntry_tpre {s : State} (hp : Proof.AesGcm.streamCryptPre s) :
    WP isa (.block cryptEntry) s (VG.Proof.AesGcm.X86_64.TPre (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat) := by
  have C := CryptCtx.of hp
  refine WP.mono (VG.Proof.AesGcm.X86_64.cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.ww C.args C.dA C.rounds) fun s₁ E => ?_
  exact ⟨E.env, C.data.of_eq E.rd E.wr, E.rbp, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.tlen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    ⟨C.lay, E.rounds, rfl, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24⟩, (s.gpr .r8).isLt⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem stream_rel (v : GcmImpl) (enc : Bool) {s₀ s₀' : State} (hp : Proof.AesGcm.streamCryptPre s₀)
    (hp' : Proof.AesGcm.streamCryptPre s₀') (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block VG.Impl.AesGcm.X86_64.restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := VG.Proof.AesGcm.X86_64.cryptEntry_tpre hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := VG.Proof.AesGcm.X86_64.cryptEntry_tpre hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (VG.Proof.AesGcm.X86_64.stream_pub hq) q₉
    (CryptCtx.of hp).args.2 (CryptCtx.of hp').args.2 ⟨_, by taint_decide⟩ hE₁ hE₂
    ((VG.Proof.AesGcm.X86_64.streamText_rel v L enc (s₀.gpr .r8).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamEncryptX86_64.pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.stream_rel v true hp hp' hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamDecryptX86_64.pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.stream_rel v false hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.SealCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. After the entry, which loads
`work` from the stack first, both runs go through the same pieces with the
same public data (`oneAad_rel`, `oneBlocksE_rel`, `oneCrypt_rel`, `oneTag_rel`),
and copy the tag to the same address, `tag`, which correctness says is still
on the stack (`sealRun_ok`, `tagOut_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- `oneAad`'s precondition, after the entry. -/
theorem OneEntry.aadPre {s₀ s : State} {k : Nat} {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s) (hNp : s₀.gpr .rdx = Np)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) (hR : (s₀.gpr .rsi).toNat = R) :
    OneS Ctx W SP R A al D n none s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl :=
  ⟨⟨E.env, hR ▸ E.rounds, E.aad, by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr, fun _ h => nomatch h⟩, by rw [E.r12, hNp],
    by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq], C.nonce.of_eq E.rd E.wr⟩

theorem one_pub {k : Nat} {s₀ s₀' : State} (hq : Proof.AesGcm.onePub k s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `e; (a; (b; (c; ((d; o); f))))`, related as `e; (((a; (b; (c; d))); o); f)`. -/
theorem rel_reassoc_seal {P Q : State → State → Prop} {e a b c d o f : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq (.seq a (.seq b (.seq c d))) o) f)) Q) :
    RelCT isa P (.seq e (.seq a (.seq b (.seq c (.seq (.seq d o) f))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with
    | seq c₁ e₁ => cases e₁ with | seq e₁ f₁ => cases e₁ with | seq d₁ o₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with
    | seq c₂ e₂ => cases e₂ with | seq e₂ f₂ => cases e₂ with | seq d₂ o₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) o₁) f₁))
    (.seq x₂ (.seq (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) o₂) f₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

theorem seal_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.sealX86_64.pre s₀)
    (hp' : Proof.AesGcm.sealX86_64.pre s₀') (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have C := (OneCtx.ofSeal hp).1
  have C' := (OneCtx.ofSeal hp').1
  have L := C.lay
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq'
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃
  have ha₃ := C.args 3 (by decide); have ha₃' := C'.args 3 (by decide)
  have hw32 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 32) 64 := a₃
  have hT₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 := rfl
  have hT₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 := by rw [q₇, a₂]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₃] at C'
  have hE : ∀ {s : State} (C : OneCtx s 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 →
      InRegions (s.rd ++ s.wr) (s₀.gpr .rsp + BitVec.ofNat 64 32) 8 →
      WP isa (.block (oneEntry 32)) s
        (OneEntry s (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => oneEntry_ok (by decide) C h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl ha₃
  have hE₂ := hE C' q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) (by rw [q₇, a₃]; rfl) (by rw [q₇]; exact ha₃')
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [«seal», oneEntry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine VG.Proof.AesGcm.X86_64.rel_reassoc_seal (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 3 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 3) (SP := s₀.gpr .rsp) (k := 32) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (VG.Proof.AesGcm.X86_64.one_pub hq) hw32 ha₃ ha₃' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  have hDW := C.dE
  have hn := C.data.ok.lt
  have hDW' := C.dE.sub_left (Offset.sub_base (stackArg s₀ 0) (d := 16 * ((stackArg s₀ 1).toNat / 16))
    (n := (stackArg s₀ 1).toNat - 16 * ((stackArg s₀ 1).toNat / 16)) (by omega))
  have a := (oneAad_rel v L hDW (T := none) (R := (s₀.gpr .rsi).toNat)).mono
    (P' := fun (s₁ s₂ : State) => True ∧
      OneEntry s₀ (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat s₁ ∧
      OneEntry s₀' (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat s₂)
    (fun _ _ h => ⟨h.2.1.aadPre C rfl rfl rfl rfl,
      h.2.2.aadPre C' q₃.symm (by rw [q₄]) (by rw [q₆]) (by rw [q₂])⟩) fun _ _ h => h
  have bl := oneBlocksE_rel v L (R := (s₀.gpr .rsi).toNat) (A := s₀.gpr .r8) (al := (s₀.gpr .r9).toNat) (T := none)
    C.t_c C.t_w C.t_d C.sp24
  have t := oneTag_rel v L (.inl rfl) hDW' (N := (stackArg s₀ 1).toNat) (R := (s₀.gpr .rsi).toNat)
    (A := s₀.gpr .r8) (al := (s₀.gpr .r9).toNat)
  -- The address of `tag`, at `[SP + 24]`, after the tag: by correctness.
  have dA := C.arg24 (by decide)
  have hW : ∀ {s₀'' s : State} (C : OneCtx s₀'' 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rdx)
      (s₀.gpr .r8) (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s₀''.gpr .rdx = s₀.gpr .rdx → (s₀''.gpr .rcx).toNat = (s₀.gpr .rcx).toNat →
      (s₀''.gpr .r9).toNat = (s₀.gpr .r9).toNat →
      s₀''.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 →
      OneEntry s₀'' (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat s →
      WP isa (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.enc) (.seq (oneCrypt v.callees)
        (oneTag v.callees 0)))) s (TagAt (s₀.gpr .rdi) (stackArg s₀ 3 + BitVec.ofNat 64 16) (stackArg s₀ 3)
          (s₀.gpr .rsp) .rsp 24 (stackArg s₀ 2)) :=
    fun C h₁ h₂ h₃ hT E => WP.mono (sealRun_ok v C E h₁ h₂ h₃) fun _ ⟨he, hrd, hwr, _, f, _⟩ => ⟨he, by
      rw [he.rsp, f.readW (r := ⟨s₀.gpr .rsp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dA _ (.inl fun _ h => h)
        · exact dA _ (.inr (.inl fun _ h => h))
        · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT], by
      rw [he.rsp, hrd, hwr]; exact C.args 2 (by decide)⟩
  have m := rel_wp (RelCT.seq a (RelCT.seq bl (RelCT.seq (oneCrypt_rel v L hDW') t)))
    (fun _ _ h => h.2) (fun _ h => hW C rfl rfl rfl hT₁ h) (fun _ h => hW C' q₃.symm (by rw [q₄]) (by rw [q₆]) hT₂ h)
  exact RelCT.seq m (tagOut_rel (b := .rsp) (d := 24) (by simp) ⟨_, by taint_decide⟩ (fun _ _ h => h.2))

theorem seal_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.sealX86_64.pre Proof.AesGcm.sealX86_64.pub («seal» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.seal_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_open` is constant time

Untrusted: everything here is checked by Lean. The first branch is on the
tag length (public); then both runs go through `oneAad`, `oneBlocks` and
`oneTag` with the same public data, as in `seal`, and copy and compare the
tags without a branch (the taint analysis). The second branch is on the
comparison, which `open` may leak: correctness says it is whether
`openResult` succeeds (`openPre_ok`), the same in both runs by `pub`; then
both runs decrypt the rest (`oneCrypt`) or encrypt the whole blocks again
(`oneUndo_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- `a; (b; (c; (d; (e; (f; (g; h))))))`, related as `(a; (b; (c; (d; (e; (f; g)))))); h`. -/
theorem rel_reassoc7 {P Q : State → State → Prop} {a b c d e f g h : Prog isa}
    (hr : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) h) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g h))))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with | seq d₁ e₁ =>
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq f₁ e₁ => cases e₁ with | seq g₁ h₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with | seq d₂ e₂ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq f₂ e₂ => cases e₂ with | seq g₂ h₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq x₁ (.seq f₁ g₁)))))) h₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq x₂ (.seq f₂ g₂)))))) h₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- What `open`'s entry leaves, for a tag length `t`. -/
abbrev OpenIn (s₀ : State) (Ctx W SP A D : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t

/-- The address `T` of the received tag, in the argument at `[SP + 24]`. -/
abbrev ArgT (SP T : Addr) (s : State) : Prop := s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T

/-- `ArgT`, and the argument may be read. -/
abbrev ArgR (SP T : Addr) (s : State) : Prop :=
  VG.Proof.AesGcm.X86_64.ArgT SP T s ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneAad` keeps the tag length, and the address of the received tag. -/
theorem aadTl_ok {s₀ s : State} {Np A D T : Addr} {nl al n t : Nat} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hT : VG.Proof.AesGcm.X86_64.ArgT SP T s₀) (h : VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s) :
    WP isa (oneAad v.callees) s fun s' => s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.X86_64.ArgR SP T s' :=
  WP.mono (oneMid_ok v C h.1 hNp hnl hal) fun _ M => by
    refine ⟨?_, ?_, by rw [M.rd, M.wr]; exact C.args 2 (by decide)⟩
    · rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm) (by decide), h.2.2]
    · rw [VG.Proof.AesGcm.X86_64.ArgT, M.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact C.arg24 (by decide) _ (.inl fun _ h => h)
        · exact C.arg24 (by decide) _ (.inr (.inr (below_sub (by decide) (by decide))))) (by decide), hT]

/-- `oneBlocks` keeps the tag length, and what stays in `W`. -/
theorem blocksTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (h : OneS Ctx W SP R A al D n none s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.X86_64.ArgR SP Tp s) :
    WP isa (oneBlocks v.callees.dec) s fun s' =>
      OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s' :=
  WP.mono (oneBlocksD_ok L v ⟨h.1.env, h.1.rounds, h.1.dat, h.1.len, h.1.dD, t_c, t_w, t_d, sp24⟩) fun _ ⟨P, _⟩ =>
    ⟨ObPost.oneS L t_w h.1 P, by
      rw [(obFrame_B P.frame).readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrameB L h.1.dD.ok.w t_w (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [VG.Proof.AesGcm.X86_64.ArgT, (obFrame_B P.frame).readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        oA.oneFrameB (by decide), h.2.2.1], by rw [P.rd, P.wr]; exact h.2.2.2⟩

/-- `oneTag` keeps `OneS` and the tag length. -/
theorem tagTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N t : Nat} {Tp : Addr} {s : State} (hN : N < 2 ^ 64)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (h : OneS Ctx W SP R A al D n (some N) s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.X86_64.ArgR SP Tp s) :
    WP isa (oneTag v.callees uO) s fun s' => OneS Ctx W SP R A al D n (some N) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s' :=
  WP.mono (oneTag_ok v L (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.rounds h.1.dat h.1.len (h.1.tlen N rfl) hN
    h.1.alen h.1.dD.ok hDW h.1.dD.ctx) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := D) (n := n) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hDW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hDW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [VG.Proof.AesGcm.X86_64.ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the address of the received tag into `rsi`. -/
theorem loadTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {T : Option Nat} {Tp : Addr} {s : State}
    (h : OneS Ctx W SP R A al D n T s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
      VG.Proof.AesGcm.X86_64.ArgR SP Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      OneS Ctx W SP R A al D n T s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ := h.2.2.2
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2.1]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

omit L in
/-- The result loaded from `W + 216`. -/
theorem loadAux_ok {s : State} (h : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 auxO))]) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := by
  have r₁ := h.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 auxO))] s = some s₁ ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.r15, r₁], ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hrd hwr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

end

/-- From the entry, for an allowed tag length: ZF says whether
`openResult` fails. -/
theorem openPre_ok (v : GcmImpl) {s s₁ : State} {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat}
    (C : OneCtx s 5 Ctx W SP Np A D nl al n) (h : VG.Proof.AesGcm.X86_64.OpenIn s Ctx W SP A D n t s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al)
    (hR : (s.gpr .rsi).toNat = R) (hok : Spec.Gcm.tagLenOk t = true) (hT : VG.Proof.AesGcm.X86_64.ArgT SP Tp s)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨Tp, t⟩) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))) s₁
      fun s' => (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' ∧
        DataW Ctx (W + BitVec.ofNat 64 16) W SP s' D n) ∧
        s'.zf = some (!(Spec.Gcm.openResult (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t
          (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem Tp t)).isSome) := by
  have L := C.lay
  have E := h.1
  have hS := (E.aadPre C hNp hnl hal hR).1
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have hlt := C.data.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ M => ?_)
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm) (by decide), h.2.2]
  have hd₃ := C.data.of_eq M.rd M.wr
  have hS₃ : OneS Ctx W SP R A al D n none s₃ := hS.frame L M.env (M.rd.trans E.rd.symm) (M.wr.trans E.wr.symm) C.dE
    (wFrame_one (.inl rfl) (wFrame_cons M.fr))
  have oA := C.arg24 (by decide)
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [M.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr (below_sub (by decide) (by decide))))) (by decide), hT]
  refine WP.mono (openFront_ok v L (al := al) ⟨M.env, hR ▸ M.rounds, M.dat, M.len, hd₃, C.t_c, C.t_w, C.t_d, C.sp24⟩
    M.hH hal₃ htl₃ hb.1 hb.2 M.abs M.j0 M.cb hTa₃ (by rw [M.rd, M.wr]; exact C.args 2 (by decide))
    (by rw [M.rd, M.wr]; exact hTr) oT oA) fun s' F => ?_
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => F.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L C.dE C.t_w hd) (by decide)
  refine ⟨⟨⟨F.env, F.rounds, by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact hS₃.aad,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hS₃.alen, F.dat, F.len, hS₃.dA.of_eq F.rd F.wr,
    (hS₃.dD.of_eq F.rd F.wr).drop (by omega), fun N hN => by cases hN; exact F.tlen⟩, hd₃.of_eq F.rd F.wr⟩, ?_⟩
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₃ : ciphOf s₃.mem Ctx R = ctxCiph s.mem Ctx R := ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by omega)
  have hw₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t := bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact oT _ (.inl fun _ h => h)
    · exact oT _ (.inr (.inr (below_sub (by decide) (by decide))))) (by omega)
  have hz := F.zf
  rw [hc₃, hp₃, hw₃] at hz
  rw [hz]
  simp only [Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- From the entry to the comparison, for an allowed tag length. -/
theorem openPre_rel {s₀ s₀' : State} {Np A D Tp : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 5 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : VG.Proof.AesGcm.X86_64.ArgT SP Tp s₀) (hT' : VG.Proof.AesGcm.X86_64.ArgT SP Tp s₀') :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s₁ ∧ VG.Proof.AesGcm.X86_64.OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))))
      fun _ _ => True := by
  have hDW := C.dE
  have hlt := C.data.ok.lt
  have hDW' := C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega))
  have oA := C.arg24 (by decide)
  have a := rel_wp ((oneAad_rel v L (R := R) (Np := Np) (nl := nl) (A := A) (al := al) (T := none) hDW).mono
      (P' := fun (s₁ s₂ : State) => VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s₁ ∧ VG.Proof.AesGcm.X86_64.OpenIn s₀' Ctx W SP A D n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C hNp hnl hal hR, h.2.1.aadPre C' hNp' hnl' hal' hR'⟩) fun _ _ h => h)
    (fun _ _ h => h) (fun _ h => VG.Proof.AesGcm.X86_64.aadTl_ok v L C hNp hnl hal hT h) (fun _ h => VG.Proof.AesGcm.X86_64.aadTl_ok v L C' hNp' hnl' hal' hT' h)
  have bl := rel_wp ((oneBlocksD_rel v L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24).mono
      (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP R A al D n none s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
          VG.Proof.AesGcm.X86_64.ArgR SP Tp s₁) ∧
        (OneS Ctx W SP R A al D n none s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
          VG.Proof.AesGcm.X86_64.ArgR SP Tp s₂))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => VG.Proof.AesGcm.X86_64.blocksTl_ok v L C.t_c C.t_w C.t_d C.sp24 oA h)
    (fun _ h => VG.Proof.AesGcm.X86_64.blocksTl_ok v L C.t_c C.t_w C.t_d C.sp24 oA h)
  have b := rel_wp ((oneTag_rel v L (.inr rfl) hDW' (N := n)).mono (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s₁) ∧
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s₂))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => VG.Proof.AesGcm.X86_64.tagTl_ok v L hlt hDW' oA.ws h) (fun _ h => VG.Proof.AesGcm.X86_64.tagTl_ok v L hlt hDW' oA.ws h)
  have c := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s₁) ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
        s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ VG.Proof.AesGcm.X86_64.ArgR SP Tp s₂)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env ⟨h.2.1.1, h.2.2.1⟩) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => VG.Proof.AesGcm.X86_64.loadTl_ok h) (fun _ h => VG.Proof.AesGcm.X86_64.loadTl_ok h)
  have d := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
        s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩)
    (RelCT.seq (bl.mono (fun _ _ h => h) fun _ _ h => h.2) (RelCT.seq b (RelCT.seq c d)))

/-- `oneUndo` in two runs: the same branch on the public length, and the same
arguments to `vg_aes_ctr32`. -/
theorem oneUndo_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ =>
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n))
      (oneUndo v.callees) fun s₁ s₂ =>
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  let G₁ : State → Prop := fun s => s.zf = some (decide (n / 16 = 0)) ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧
    (n / 16 ≠ 0 → WP isa (.block undoB2) s fun s₂ =>
      CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
  have hw₁ : ∀ s, (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s ∧
      DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) → WP isa (.block undoB1) s G₁ := fun s h =>
    WP.mono (undo1_ok h.2.ok.lt h.1.env (h.1.tlen n rfl) h.1.dat) fun s₁ ⟨hcx, h8, z, g, m, rd, wr⟩ => by
      have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := h.1.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr
      exact ⟨z, he₁, fun _ => WP.mono (undo2_ok L he₁ ⟨by rw [m]; exact h.1.rounds.1, h.1.rounds.2⟩
        (h.2.of_eq rd wr) hcx h8) fun _ ⟨c, e, _⟩ => ⟨c, e⟩⟩
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.1.env h.2.1.env)
    ⟨_, by taint_decide⟩) (fun _ _ h => h) (G₁ := G₁) (G₂ := G₁) hw₁ hw₁
  have t := (rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some true) (c := .block [])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (fun _ h => WP.block_nil h.2.1) (fun _ h => WP.block_nil h.2.1)).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block undoB2) s fun s₂ =>
      CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some false) (c := .block undoB2)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2⟩, ⟨h.1.2.2, by rw [h.1.2.2.1, ← h.1.2.1.1, h.2]⟩⟩) hw₂ hw₂
  have hw₃ : ∀ s, CtrCall s Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s →
      WP isa (.call v.ctr.callee.name v.ctr.callee.code) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := fun s h =>
    WP.mono (ctr_call v.ctr h.1) fun _ g => h.2.of_saved g.saved g.rd g.wr
  have c := (rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧
      (CtrCall s₁ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₁) ∧
      (CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂))
      fun _ _ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.rsp, h.2.2.2.rsp]⟩)
    (fun _ _ h => h.2) hw₃ hw₃).mono (fun _ _ h => h) fun _ _ h => h.2
  rw [oneUndo_eq]
  exact RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.1, h.2.2.1]) t (RelCT.seq b c))

/-- After the comparison: the rest decrypted if the tags match, the whole
blocks encrypted again if not, and the result loaded. -/
theorem openPost_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {b₁ b₂ : Bool} (hb : b₁ = b₂)
    (hDW' : (⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂))
      (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees)) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have t := (VG.Proof.AesGcm.X86_64.oneUndo_rel v L (R := R) (A := A) (al := al) (D := D) (n := n)).mono
    (P' := fun (s₁ s₂ : State) => (True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂)) ∧ s₁.zf = some true)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
  have e := (oneCrypt_rel v L (R := R) (A := A) (al := al) (T := some n) hDW').mono
    (P' := fun (s₁ s₂ : State) => (True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂)) ∧ s₁.zf = some false)
    (Q' := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    (fun _ _ h => ⟨h.1.2.1.1.1, h.1.2.2.1.1⟩) fun _ _ h => ⟨h.1.env, h.2.env⟩
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => VG.Proof.AesGcm.X86_64.loadAux_ok h) (fun _ h => VG.Proof.AesGcm.X86_64.loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, hb]) t e)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

end

/-- After the entry: the tag length checked, then the tag. -/
theorem openBody_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 5 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (ht : t < 2 ^ 64) (hT : VG.Proof.AesGcm.X86_64.ArgT SP Tp s₀) (hT' : VG.Proof.AesGcm.X86_64.ArgT SP Tp s₀')
    (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr)) (hTr' : Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome) :
    RelCT isa (fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s₁ ∧ VG.Proof.AesGcm.X86_64.OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)])
        (.seq (oneAad v.callees)
        (.seq (oneBlocks v.callees.dec)
        (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
        (.seq recv
        (.seq (cmp uO)
        (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees))
          (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  have hK : ∀ {s₀ s : State}, VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s → WP isa tagLenOk s fun s' =>
      VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1], by rw [k.mem]; exact h.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ VG.Proof.AesGcm.X86_64.OpenIn s₀ Ctx W SP A D n t s₁ ∧
      VG.Proof.AesGcm.X86_64.OpenIn s₀' Ctx W SP A D n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length §5.2.1.2 does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hlt := C.data.ok.lt
    refine VG.Proof.AesGcm.X86_64.rel_reassoc7 (RelCT.seq ?_ (VG.Proof.AesGcm.X86_64.openPost_rel v L (R := R) (A := A) (al := al) (congrArg (!·) hres)
      (C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega)))))
    exact rel_wp ((VG.Proof.AesGcm.X86_64.openPre_rel v L C C' hNp hnl hal hR hNp' hnl' hal' hR' hT hT').mono
        (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h) (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
      (fun _ h => VG.Proof.AesGcm.X86_64.openPre_ok v C h hNp hnl hal hR hok hT hTr oT)
      (fun _ h => VG.Proof.AesGcm.X86_64.openPre_ok v C' h hNp' hnl' hal' hR' hok hT' hTr' oT)

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

theorem open_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.openX86_64.pre s₀)
    (hp' : Proof.AesGcm.openX86_64.pre s₀') (hq : Proof.AesGcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  obtain ⟨C', hTr', -, -, -⟩ := OneCtx.ofOpen hp'
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  have hres' : ∀ {s : State}, Proof.AesGcm.rounds s → Proof.AesGcm.openLeak s = [if (Spec.Gcm.openResult
      (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (stackArg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).isSome
      then 1 else 0] := fun h => by
    simp only [Proof.AesGcm.openLeak, Proof.AesGcm.arg, h, not_true_eq_false, ↓reduceIte]
  rw [hres' C.rounds, hres' C'.rounds] at hres
  have hres := VG.Proof.AesGcm.X86_64.leak_bool hres
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide); have a₄ := qa 4 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃ a₄
  have ha₄ := C.args 4 (by decide); have ha₄' := C'.args 4 (by decide)
  have hw40 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 := a₄
  have hT₁ : VG.Proof.AesGcm.X86_64.ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀ := rfl
  have hT₂ : VG.Proof.AesGcm.X86_64.ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀' := by rw [VG.Proof.AesGcm.X86_64.ArgT, q₇, a₂]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₄] at C'
  rw [← a₂, ← a₃] at hTr'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₀, ← a₁, ← a₂, ← a₃] at hres
  generalize ht : (stackArg s₀ 3).toNat = t at hres hTr hTr' d_td d_tw t_t
  have oT : OutWDS (stackArg s₀ 4) (stackArg s₀ 0) (s₀.gpr .rsp) (stackArg s₀ 1).toNat ⟨stackArg s₀ 2, t⟩ :=
    fun r hr => hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have hE : ∀ {s : State} (C : OneCtx s 5 (s₀.gpr .rdi) (stackArg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s₀ 4 → stackArg s 3 = stackArg s₀ 3 →
      WP isa (.block (oneEntry 40 ++ [.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx])) s
        (VG.Proof.AesGcm.X86_64.OpenIn s (s₀.gpr .rdi) (stackArg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => WP.mono (openEntry_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, htl, _⟩ =>
      ⟨E, by rw [hbx, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [htl, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C' q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) (by rw [q₇, a₄]; rfl) a₃.symm
  rw [oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  rw [«open», oneEntry]
  simp only [List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 4 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 4) (SP := s₀.gpr .rsp) (k := 40) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (VG.Proof.AesGcm.X86_64.one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) hw40 ha₄ ha₄' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact VG.Proof.AesGcm.X86_64.openBody_rel v C C' rfl rfl rfl rfl q₃.symm (by rw [← q₄]) (by rw [← q₆]) (by rw [← q₂])
    (by rw [← ht]; exact (stackArg s₀ 3).isLt) hT₁ hT₂ hTr hTr' oT hres

theorem open_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.openX86_64.pre Proof.AesGcm.openX86_64.pub («open» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => VG.Proof.AesGcm.X86_64.open_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Verified`. -/
section

/-!
# AES-GCM on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts
of `Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with 8 bytes of stack, for the return address
of a call: the functions called make no calls, and 24 for those that call
`vg_aes_gcm_encrypt_blocks` or `vg_aes_gcm_decrypt_blocks` with an argument
on the stack).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String :=
  (v.ctr.features ++ v.gh.features ++ (v.stitch.map (·.features)).getD []).dedup

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

section
variable (v : GcmImpl)

theorem init_mx : (init v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_spSafe : (init v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_correct (s : State) (hs : Proof.AesGcm.initX86_64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.init_mx v) he hg, hp⟩

theorem streamInit_mx : (streamInit v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_spSafe : (streamInit v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_correct (s : State) (hs : Proof.AesGcm.streamInitX86_64.pre s) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamInitX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamInit_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamInit_mx v) he hg, hp⟩

theorem streamAad_mx : (streamAad v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_spSafe : (streamAad v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_correct (s : State) (hs : Proof.AesGcm.streamAadX86_64.pre s) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamAadX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamAad_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamAad_mx v) he hg, hp⟩

theorem streamEncrypt_mx : (streamEncrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_correct (s : State) (hs : Proof.AesGcm.streamEncryptX86_64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesGcm.X86_64.streamEncrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamEncrypt_mx v) he hg, hp⟩

theorem streamDecrypt_mx : (streamDecrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_correct (s : State) (hs : Proof.AesGcm.streamDecryptX86_64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesGcm.X86_64.streamDecrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamDecrypt_mx v) he hg, hp⟩

theorem streamFinish_mx : (streamFinish v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_correct (s : State) (hs : Proof.AesGcm.streamFinishX86_64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamFinishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamFinish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamFinish_mx v) he hg, hp⟩

theorem streamVerify_mx : (streamVerify v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_correct (s : State) (hs : Proof.AesGcm.streamVerifyX86_64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamVerifyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamVerify_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.streamVerify_mx v) he hg, hp⟩

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_correct (s : State) (hs : Proof.AesGcm.sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.seal_mx v) he hg, hp⟩

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_correct (s : State) (hs : Proof.AesGcm.openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcm.X86_64.open_mx v) he hg, hp⟩

end

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified (v : GcmImpl) :
    Verified X86_64.target (init v.callees) (Proof.AesGcm.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.init_correct v) (init_ct v) (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, Proof.AesGcm.initX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSat] using VG.Proof.AesGcm.X86_64.initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamInit_verified (v : GcmImpl) :
    Verified X86_64.target (streamInit v.callees) (Proof.AesGcm.streamInitScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamInit_correct v) (streamInit_ct v) (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, Proof.AesGcm.streamInitX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [siSat] using VG.Proof.AesGcm.X86_64.siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x2000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamAad_verified (v : GcmImpl) :
    Verified X86_64.target (streamAad v.callees) (Proof.AesGcm.streamAadScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamAad_correct v) (streamAad_ct v) (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, Proof.AesGcm.streamAadX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [saSat] using VG.Proof.AesGcm.X86_64.saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no data, and `scratch` at 0). -/
def crSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamEncrypt v.callees) (Proof.AesGcm.streamEncryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamEncrypt_correct v) (VG.Proof.AesGcm.X86_64.streamEncrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using VG.Proof.AesGcm.X86_64.crSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamDecrypt v.callees) (Proof.AesGcm.streamDecryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamDecrypt_correct v) (VG.Proof.AesGcm.X86_64.streamDecrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using VG.Proof.AesGcm.X86_64.crSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `work` at 0). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0, 2560⟩]

theorem streamFinish_verified (v : GcmImpl) :
    Verified X86_64.target (streamFinish v.callees) (Proof.AesGcm.streamFinishScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig, Spec.Gcm.streamFinishPre,
      Spec.Gcm.streamFinishPost, Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSat] using VG.Proof.AesGcm.X86_64.finSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def verSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamVerify_verified (v : GcmImpl) :
    Verified X86_64.target (streamVerify v.callees) (Proof.AesGcm.streamVerifyScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig, Spec.Gcm.streamVerifyPre,
      Spec.Gcm.streamVerifyPost, Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSat] using VG.Proof.AesGcm.X86_64.verSat)

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or data, `tag` at
`0x3000` and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Proof.AesGcm.sealScratchContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.seal_correct v) (VG.Proof.AesGcm.X86_64.seal_ct v) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
      Proof.AesGcm.sealX86_64, Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using VG.Proof.AesGcm.X86_64.sealSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data, data or tag, and
`work` at 0). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Proof.AesGcm.openScratchContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.AesGcm.X86_64.open_correct v) (VG.Proof.AesGcm.X86_64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
        sig_simp [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [openSat] using VG.Proof.AesGcm.X86_64.openSat }

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Frame`. -/
section

/-!
# AES-GCM on x86-64, with its working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame of 2568 bytes that
allocates it (`Verified.stackScratch`): the 2560 bytes of working space, and
8 more to keep `rsp` aligned. Their own calls use 8 bytes below it, the
return address, as `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and `vg_ghash` use no
stack (`KeyImpl.noStack`, `Ctr32Impl.noStack`, `GhashImpl.noStack`).

The working space of the others is their last argument, passed on the stack
after the six argument registers and their other stack arguments: their
frames (`Verified.stackArgScratch`) also hold a copy of those, 2584 bytes for
`stream_encrypt` and `stream_decrypt` (one), 2576 for `stream_finish` (none),
2584 for `stream_verify` (one), 2600 for `seal` (three) and 2608 for `open`
(four, and a leak, whether it succeeds, which reads only its buffers:
`openLeak_local`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

variable (v : GcmImpl)

theorem init_xdepth : (init v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamInit_xdepth : (streamInit v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamAad_xdepth : (streamAad v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.AesGcm.X86_64.initSat with
                                           wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using VG.Proof.AesGcm.X86_64.initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.callees))
      (Spec.Gcm.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (VG.Proof.AesGcm.X86_64.init_verified v) (by decide) (by decide)
    (by decide) (VG.Proof.AesGcm.X86_64.init_spSafe v) (VG.Proof.AesGcm.X86_64.init_xdepth v) VG.Proof.AesGcm.X86_64.initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { VG.Proof.AesGcm.X86_64.siSat with
                                               wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using VG.Proof.AesGcm.X86_64.streamInitFrameSat

theorem streamInit_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (VG.Proof.AesGcm.X86_64.streamInit_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamInit_spSafe v) (VG.Proof.AesGcm.X86_64.streamInit_xdepth v) VG.Proof.AesGcm.X86_64.streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { VG.Proof.AesGcm.X86_64.saSat with
                                              wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using VG.Proof.AesGcm.X86_64.streamAadFrameSat

theorem streamAad_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (VG.Proof.AesGcm.X86_64.streamAad_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamAad_spSafe v) (VG.Proof.AesGcm.X86_64.streamAad_xdepth v) VG.Proof.AesGcm.X86_64.streamAadFrameSat_pre

theorem streamEncrypt_xdepth : (streamEncrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem streamDecrypt_xdepth : (streamDecrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: `len`, their one
stack argument, at `0x8008`. -/
def crFrameSat : State :=
  { VG.Proof.AesGcm.X86_64.crSat with
               rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract X86_64.abi 2608).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using VG.Proof.AesGcm.X86_64.crFrameSat

theorem streamEncrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt v.callees))
      (Spec.Gcm.streamEncryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (VG.Proof.AesGcm.X86_64.streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamEncrypt_spSafe v) (VG.Proof.AesGcm.X86_64.streamEncrypt_xdepth v) (streamTextPre_local _) (streamEncryptPost_local _)
    VG.Proof.AesGcm.X86_64.streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract X86_64.abi 2608).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using VG.Proof.AesGcm.X86_64.crFrameSat

theorem streamDecrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt v.callees))
      (Spec.Gcm.streamDecryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (VG.Proof.AesGcm.X86_64.streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamDecrypt_spSafe v) (VG.Proof.AesGcm.X86_64.streamDecrypt_xdepth v) (streamTextPre_local _) (streamDecryptPost_local _)
    VG.Proof.AesGcm.X86_64.streamDecryptFrameSat_pre

theorem streamFinish_xdepth : (streamFinish v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, tagOut, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamVerify_xdepth : (streamVerify v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, tagOut, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { VG.Proof.AesGcm.X86_64.finSat with
                                         rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using VG.Proof.AesGcm.X86_64.finFrameSat

theorem streamFinish_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (streamFinish v.callees))
      (Spec.Gcm.streamFinishContract X86_64.abi 2584) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2576) (VG.Proof.AesGcm.X86_64.streamFinish_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamFinish_spSafe v) (VG.Proof.AesGcm.X86_64.streamFinish_xdepth v) (streamFinishPre_local _)
    (streamFinishPost_local _) VG.Proof.AesGcm.X86_64.finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State :=
  { VG.Proof.AesGcm.X86_64.verSat with
                rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract X86_64.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using VG.Proof.AesGcm.X86_64.verFrameSat

theorem streamVerify_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamVerify v.callees))
      (Spec.Gcm.streamVerifyContract X86_64.abi 2592) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2584) (VG.Proof.AesGcm.X86_64.streamVerify_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.streamVerify_spSafe v) (VG.Proof.AesGcm.X86_64.streamVerify_xdepth v) (streamVerifyPre_local _)
    (streamVerifyPost_local _) VG.Proof.AesGcm.X86_64.verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { VG.Proof.AesGcm.X86_64.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using VG.Proof.AesGcm.X86_64.sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» v.callees))
      (Spec.Gcm.sealContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) (VG.Proof.AesGcm.X86_64.seal_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcm.X86_64.seal_spSafe v) (VG.Proof.AesGcm.X86_64.seal_xdepth v) (sealPre_local _) (sealPost_local _) VG.Proof.AesGcm.X86_64.sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { VG.Proof.AesGcm.X86_64.openSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract X86_64.abi 2632).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using VG.Proof.AesGcm.X86_64.openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callees))
      (Spec.Gcm.openContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (VG.Proof.AesGcm.X86_64.open_verified v)
    (by decide) (by decide) (by decide) (VG.Proof.AesGcm.X86_64.open_spSafe v) (VG.Proof.AesGcm.X86_64.open_xdepth v) (openPre_local _)
    (openPost_local _) VG.Proof.AesGcm.X86_64.openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesGcm.X86_64

end
