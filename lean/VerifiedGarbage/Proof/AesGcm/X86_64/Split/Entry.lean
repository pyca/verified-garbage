module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Contract
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `seal_split` on x86-64: what its precondition gives, and its entry

Untrusted: everything here is checked by Lean. `seal_split`'s precondition
gives `seal`'s context (`OneCtx`, for its six arguments on the stack, with
`dst` and `len` as the data), where `src` is and what it is apart from
(`SplitCtx`); its entry leaves what `seal`'s does (`OneEntry`), with `src`
and `src_len` kept at `tlO` and `tlenO` (`entry_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- What `seal_split`'s precondition gives: `seal`'s context, for the data
`D` (`dst`) of `n` (`len`) bytes, and `sl` (`src_len`) bytes at `S` (`src`),
apart from what is written, and the 56 bytes below the stack pointer apart
from the buffers. -/
structure SplitCtx (s : State) (Ctx W SP Np A D S T : Addr) (nl al n sl : Nat) : Prop
    extends OneCtx s 6 Ctx W SP Np A D nl al n where
  src : Covers [⟨S, sl⟩] (s.rd ++ s.wr)
  sW : (⟨S, sl⟩ : Region).Disjoint ⟨W, 2560⟩
  sD : (⟨S, sl⟩ : Region).Disjoint ⟨D, n⟩
  sWrap : S.toNat + sl ≤ 2 ^ 64
  sl_le : sl ≤ n
  kc : (below SP 56).Disjoint ⟨Ctx, 256⟩
  kw : (below SP 56).Disjoint ⟨W, 2560⟩
  kd : (below SP 56).Disjoint ⟨D, n⟩
  ks : (below SP 56).Disjoint ⟨S, sl⟩
  ka : (below SP 56).Disjoint ⟨A, al⟩
  sp56 : 56 ≤ SP.toNat
  tag : Covers [⟨T, 16⟩] s.wr
  tD : (⟨T, 16⟩ : Region).Disjoint ⟨D, n⟩
  tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  rT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩
  nD : (⟨Np, nl⟩ : Region).Disjoint ⟨D, n⟩
  aD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩

theorem SplitCtx.of {cl : Nat} {s : State} (hp : Proof.AesGcm.splitPre cl s) (hcl : 256 ≤ cl) :
    SplitCtx s (s.gpr .rdi) (stackArg s 5) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 2) (stackArg s 0)
      (stackArg s 4) (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 3).toNat (stackArg s 1).toNat := by
  simp only [Proof.AesGcm.splitPre, Proof.AesGcm.stk56, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cd, d_cw, d_nd, d_nw, d_ad, d_aw, d_sd, d_sw, d_dw, d_da, d_wa, d_td, d_tw, r_d, r_w, r_t,
    t_c, t_n, t_a, t_s, t_d, t_w, wc, wn, wa, ws, wd, wt, ww, sp56, wsp, sl_le, hR⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_da d_wa
  have pc : Covers [⟨s.gpr .rdi, 256⟩] (s.rd ++ s.wr) := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)) a m
      ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  have pn : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have pa : Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  have ps : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * 6⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  have pd : Covers [⟨stackArg s 2, (stackArg s 3).toNat⟩] s.wr := by
    rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  have pt : Covers [⟨stackArg s 4, 16⟩] s.wr := by
    rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have pW : Covers [⟨stackArg s 5, 2560⟩] s.wr := by
    rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have c256 : Region.Sub ⟨s.gpr .rdi, 256⟩ ⟨s.gpr .rdi, cl⟩ := Region.sub_prefix hcl
  replace d_cd := d_cd.sub_left c256
  replace d_cw := d_cw.sub_left c256
  replace t_c := t_c.sub_right c256
  replace wc : (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 := by omega_arith
  have b8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 56) := below_sub (by decide) (by decide)
  have b24 : Region.Sub (below (s.gpr .rsp) 24) (below (s.gpr .rsp) 56) := below_sub (by decide) (by decide)
  have hSt : (⟨stackArg s 5 + BitVec.ofNat 64 16, 80⟩ : Region).Sub ⟨stackArg s 5, 2560⟩ := Lay.wSub (by decide)
  have L : Lay (s.gpr .rdi) (stackArg s 5 + BitVec.ofNat 64 16) (stackArg s 5) (s.gpr .rsp) := by
    refine ⟨wc, ?_, ww, d_cw.sub_right hSt, d_cw, ?_, ?_, t_c.sub_left b8, (t_w.sub_left b8).sub_right hSt,
      t_w.sub_left b8⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le ((stackArg s 5).toNat + 16 % 2 ^ 64) (2 ^ 64)
      omega_arith
    · simpa using Offset.disjoint (stackArg s 5) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
        (by omega_arith) (by omega_arith)
    · exact Offset.disjoint (stackArg s 5) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
        (by omega_arith) (by omega_arith)
  refine ⟨⟨L, ⟨pc, covers_off pW (show 16 + 80 ≤ 2560 by decide) (by decide), pW⟩, ww, fun i hi => ?_,
    d_wa.symm, ⟨pn, by have := (s.gpr .rcx).isLt; omega_arith, wn, (d_nw.sub_right hSt), d_nw, t_n.sub_left b8⟩,
    ⟨pa, by have := (s.gpr .r9).isLt; omega_arith, wa, d_aw.sub_right hSt, d_aw, t_a.sub_left b8⟩,
    ⟨⟨covers_left pd, by have := (stackArg s 3).isLt; omega_arith, wd, d_dw.sub_right hSt, d_dw, t_d.sub_left b8⟩,
      pd, d_cd⟩,
    r_d, r_w, d_dw, d_da.symm, hR, t_c.sub_left b24, t_w.sub_left b24, t_d.sub_left b24, by omega_arith⟩,
    ps, d_sw, d_sd, ws, sl_le, t_c, t_w, t_d, t_s, t_a, sp56, pt, d_td, d_tw, r_t, d_nd, d_ad⟩
  have := in_off pm (d := 8 * i) (n := 8) (by omega_arith) (by omega_arith)
  rwa [add_ofNat_assoc, show 8 + 8 * i = 8 * (i + 1) by omega_arith] at this

/-- After the entry: `seal`'s, with `src` and `src_len` kept. -/
structure SEntry (s₀ : State) (Ctx W SP A D S : Addr) (n sl : Nat) (s : State) : Prop
    extends OneEntry s₀ Ctx W SP A D n s where
  src : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S
  slen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl

/-- `SealSplit.entry`, with `W` at `[rsp + 48]`. -/
theorem entry_ok {s : State} {Ctx W SP Np A D S T : Addr} {nl al n sl : Nat}
    (C : SplitCtx s Ctx W SP Np A D S T nl al n sl) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP)
    (hA : s.gpr .r8 = A) (hS : stackArg s 0 = S) (hsl : (stackArg s 1).toNat = sl) (hD : stackArg s 2 = D)
    (hn : (stackArg s 3).toNat = n) (hW' : s.mem.readW (SP + BitVec.ofNat 64 48) 64 = W) :
    WP isa (.block SealSplit.entry) s (SEntry s Ctx W SP A D S n sl) := by
  have rA : ∀ i, s.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := fun i => by
    rw [← hSP]; simp [stackArg, stackArgAddr]
  have hS' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = S := by rw [← hS, ← rA 0]
  have hsl' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 sl := by
    rw [← hsl, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← rA 1]
  have hD' : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = D := by rw [← hD, ← rA 2]
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← rA 3]
  have a₀ := C.args 0 (by omega_arith)
  have a₁ := C.args 1 (by omega_arith)
  have a₂ := C.args 2 (by omega_arith)
  have a₃ := C.args 3 (by omega_arith)
  have a₅ := C.args 5 (by omega_arith)
  simp only [Nat.zero_add, Nat.mul_one] at a₀ a₁ a₂ a₃ a₅
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 48))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, a₅], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := C.perm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off C.perm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off C.perm.w (show 232 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off C.perm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off C.perm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off C.perm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  have w₆ := in_off C.perm.w (show 224 + 8 ≤ 2560 by decide) (by decide)
  have w₇ := in_off C.perm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅ w₆ w₇
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₀ a₁ a₂ a₃
  have dAW : ∀ i < 6, ∀ (m : Mem) (k' : Nat), Frame [⟨W + BitVec.ofNat 64 128, k'⟩] s.mem m → k' ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = s.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
    fun i hi m k' hf hk' => hf.readW (r := ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := (C.dA.sub_left (show Region.Sub ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 6⟩ by
          rw [show 8 * (i + 1) = 8 + 8 * i by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)))
        exact this.sub_right (Lay.wSub (by omega_arith))) (by decide)
  have hS₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = S := by
    have := dAW 0 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hS'] using this
  have hsl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 sl := by
    have := dAW 1 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hsl'] using this
  have hD₁ : s₁.mem.readW (SP + BitVec.ofNat 64 24) 64 = D := by
    have := dAW 2 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hD'] using this
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 n := by
    have := dAW 3 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hn'] using this
  have sA : ∀ e d, 8 ≤ e → e + 8 ≤ 56 → 176 ≤ d → d + 8 ≤ 240 →
      Mem.Sep (SP + BitVec.ofNat 64 e) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) := by
    intro e d he₁ he₂ h₁ h₂
    refine Region.Disjoint.sep (?_ : (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩)
      (Region.contains_self _ _) (Region.contains_self _ _)
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 6⟩ := by
      rw [show e = 8 + (e - 8) by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    exact (C.dA.sub_left hs).sub_right (Lay.wSub (by omega_arith))
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega_arith) (by omega_arith)
  have p₁ := sA 24 176 (by decide) (by decide) (by decide) (by decide)
  have p₂ := sA 24 232 (by decide) (by decide) (by decide) (by decide)
  have p₃ := sA 24 184 (by decide) (by decide) (by decide) (by decide)
  have p₄ := sA 32 176 (by decide) (by decide) (by decide) (by decide)
  have p₅ := sA 32 232 (by decide) (by decide) (by decide) (by decide)
  have p₆ := sA 32 184 (by decide) (by decide) (by decide) (by decide)
  have p₇ := sA 32 200 (by decide) (by decide) (by decide) (by decide)
  have p₈ := sA 8 176 (by decide) (by decide) (by decide) (by decide)
  have p₉ := sA 8 232 (by decide) (by decide) (by decide) (by decide)
  have p₁₀ := sA 8 184 (by decide) (by decide) (by decide) (by decide)
  have p₁₁ := sA 8 200 (by decide) (by decide) (by decide) (by decide)
  have p₁₂ := sA 8 208 (by decide) (by decide) (by decide) (by decide)
  have p₁₃ := sA 16 176 (by decide) (by decide) (by decide) (by decide)
  have p₁₄ := sA 16 232 (by decide) (by decide) (by decide) (by decide)
  have p₁₅ := sA 16 184 (by decide) (by decide) (by decide) (by decide)
  have p₁₆ := sA 16 200 (by decide) (by decide) (by decide) (by decide)
  have p₁₇ := sA 16 208 (by decide) (by decide) (by decide) (by decide)
  have p₁₈ := sA 16 224 (by decide) (by decide) (by decide) (by decide)
  have q₀ := sep 176 232 (by decide) (by decide) (by decide)
  have q₁ := sep 176 184 (by decide) (by decide) (by decide)
  have q₂ := sep 176 200 (by decide) (by decide) (by decide)
  have q₃ := sep 176 208 (by decide) (by decide) (by decide)
  have q₄ := sep 232 184 (by decide) (by decide) (by decide)
  have q₅ := sep 232 200 (by decide) (by decide) (by decide)
  have q₆ := sep 232 208 (by decide) (by decide) (by decide)
  have q₇ := sep 184 200 (by decide) (by decide) (by decide)
  have q₈ := sep 184 208 (by decide) (by decide) (by decide)
  have q₉ := sep 200 208 (by decide) (by decide) (by decide)
  have q₁₀ := sep 176 224 (by decide) (by decide) (by decide)
  have q₁₁ := sep 232 224 (by decide) (by decide) (by decide)
  have q₁₂ := sep 184 224 (by decide) (by decide) (by decide)
  have q₁₃ := sep 200 224 (by decide) (by decide) (by decide)
  have q₁₄ := sep 208 224 (by decide) (by decide) (by decide)
  have q₁₅ := sep 176 192 (by decide) (by decide) (by decide)
  have q₁₆ := sep 232 192 (by decide) (by decide) (by decide)
  have q₁₇ := sep 184 192 (by decide) (by decide) (by decide)
  have q₁₈ := sep 200 192 (by decide) (by decide) (by decide)
  have q₁₉ := sep 208 192 (by decide) (by decide) (by decide)
  have q₂₀ := sep 224 192 (by decide) (by decide) (by decide)
  have e : SealSplit.entry = [.mov .rax (.mem (at_ .rsp 48))] ++ save .rax ++
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 24)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 32)),
        .store (at_ .r15 lenO) .rax, .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rax,
        .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 tlenO) .rax, .mov .r12 (.reg .rdx),
        .mov .rbp (.reg .rcx)] := by
    simp [SealSplit.entry, ptr, stO]
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 24)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 32)),
        .store (at_ .r15 lenO) .rax, .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rax,
        .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 tlenO) .rax, .mov .r12 (.reg .rdx),
        .mov .rbp (.reg .rcx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = s.gpr .rdx ∧
      s₂.gpr .rbp = s.gpr .rcx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 232) A).writeW
        (W + BitVec.ofNat 64 184) (s.gpr .r9)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n)).writeW (W + BitVec.ofNat 64 224) S).writeW
            (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 sl) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, w₆, w₇, a₀, a₁, a₂, a₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hrdi, hCtx]
    · simp [gpr_setReg, gpr_arithFlags, hrdx]
    · simp [gpr_setReg, gpr_arithFlags, hrcx]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, gpr_arithFlags,
        Mem.readW_writeW_sep, hD₁, hn₁, hS₁, hsl₁, hrsi, hr8, hr9, hA]
    all_goals rfl
  rw [e]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 64⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 240 → (⟨W + BitVec.ofNat 64 176, 64⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by omega_arith)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 232 ∧ v = A) ∨ (d = 184 ∧ v = s.gpr .r9) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) ∨ (d = 224 ∧ v = S) ∨
      (d = 192 ∧ v = BitVec.ofNat 64 sl) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64,
        Mem.readW_writeW_sep]
  refine ⟨⟨⟨h13, h14, h15, hsp, C.perm.of_eq hrd' hwr'⟩, ⟨?_, C.rounds⟩, rd 232 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 184 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))), h12, hbp, hsp, ?_, ?_, hrd', hwr'⟩,
    rd 224 _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))),
    rd 192 _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))))⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
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

end VG.Proof.AesGcm.X86_64.Split
