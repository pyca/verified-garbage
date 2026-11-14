module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PreG
public import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Contract
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `AesGcm.X86_64.Split.Entry`, which only this module used -/

section

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
      t_w.sub_left b8, by decide, by decide⟩
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

end

end


/-!
# AES-GCM `seal_split` on x86-64: from the entry to the tag at `W`

Untrusted: everything here is checked by Lean. After the entry, `J₀` and the
additional data (`oneMid_ok`), `prefix` (`prefix_ok`) and `body` (`body_ok`)
leave the plaintext `src[0..sl] ‖ dst[sl..len]` encrypted at `dst` and the
tag at `W`, of the additional data and the ciphertext with the lengths block
of `len` (`splitRun_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ghash blocks ofBytes toBytes zeros
  padLen gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

theorem padLen_mod {n : Nat} (h : n % 16 = 0) : padLen n = 0 := by simp [padLen, h]

/-- Whole blocks after the padded additional data are text. -/
theorem padded_whole {a A c d : List Byte} (hA : a ++ zeros (padLen a.length) = A) (hAl : A.length % 16 = 0)
    (hc : c.length % 16 = 0) : padded (A ++ c) d = padded a (c ++ d) := by
  have z0 : padLen (A ++ c).length = 0 := padLen_mod (by simp only [List.length_append]; omega_arith)
  have zA : padLen A.length = 0 := padLen_mod hAl
  unfold padded Spec.Gcm.ghashInput
  by_cases hd : d = []
  · subst hd
    by_cases hc0 : c = []
    · subst hc0
      simp only [List.append_nil, ↓reduceIte, hA, zA]
      simp [zeros]
    · simp only [List.append_nil, ↓reduceIte, hc0, hA]
  · have hcd : c ++ d ≠ [] := by simp [hd]
    simp only [hd, hcd, ↓reduceIte, hA, z0]
    simp [zeros, List.append_assoc]

/-- The keystream from the counter block `q` blocks on, from any byte. -/
theorem xorKs_shift' (ciph : Block → Block) (icb : Block) (q k : Nat) (d : List Byte) :
    xorKs ciph icb (16 * q + k) d = xorKs ciph (Nat.repeat inc32 q icb) k d := by
  simp only [xorKs]
  refine List.map_congr_left fun i _ => ?_
  simp only [Proof.Gcm.ksByte]
  rw [show (16 * q + k + i) / 16 = (k + i) / 16 + q by omega_arith, show (16 * q + k + i) % 16 = (k + i) % 16 by omega_arith,
    Proof.Gcm.repeat_add]

/-- A region apart from `W`, the data from byte `k` on and the 56 bytes below
`SP` is apart from what `body` writes. -/
theorem sf_out {W D SP : Addr} {n : Nat} {X : Region} (xw : X.Disjoint ⟨W, 2560⟩) (xd : X.Disjoint ⟨D, n⟩)
    (xs : X.Disjoint (below SP 56)) : ∀ r ∈ splitFrame W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact xw.sub_right (Region.sub_prefix (by decide))
  · exact xw.sub_right (Lay.wSub (by decide))
  · exact xw.sub_right (Lay.wSub (by decide))
  · exact xd
  · exact xs

theorem saved_sf {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {D : Addr} {n : Nat}
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (kw : (below SP 56).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ splitFrame W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (kw.sub_right (Lay.wSub (by decide))).symm

/-- `src` and `src_len`, kept at `tlO` and `tlenO` through `oneAad`. -/
theorem mid_slots {s₀ s₁ s₂ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat} {H : Block}
    {iv a : List Byte} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (M₂ : OneMid s₀ Ctx W SP D n H iv a s₁.mem s₂) :
    s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = S ∧ s₂.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl := by
  have f₂ : Frame (oneFrame W D SP n) s₁.mem s₂.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₂.fr)
  have k₂ : ∀ d, d = 192 ∨ d = 224 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame C.lay C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  exact ⟨by rw [k₂ 224 (.inr rfl)]; exact E.src, by rw [k₂ 192 (.inl rfl)]; exact E.slen⟩

/-- What `prefix` needs, after `J₀` and the additional data. -/
theorem PP.ofMid {M : CtxMode} {s₀ s₂ : State} {mE : Mem} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    {H : Block} {iv a : List Byte} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hR : (s₀.gpr .rsi).toNat = R) (M₂ : OneMid s₀ Ctx W SP D n H iv a mE s₂)
    (hS : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hsl : s₂.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) : PP M Ctx W SP D S R n sl s₂ := by
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  exact ⟨M₂.env, C.lay, hR ▸ M₂.rounds, M₂.dat, M₂.len, hS, hsl, C.data.of_eq M₂.rd M₂.wr,
    by rw [M₂.rd, M₂.wr]; exact C.src, C.sW, C.sD, C.sWrap, C.sl_le, C.kw, C.kd, C.ks, kM, C.sp56,
    X.keep M₂.rd M₂.wr M₂.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩

/-- What `seal_split` leaves at the tag at `W`, after the entry: what
`sealRun_ok` does, for the plaintext of `sl` bytes at `S` and the rest at
`D`. -/
abbrev SplitRunPost (s₀ : State) (Ctx W SP Np A D S : Addr) (nl al n sl : Nat) (s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
    SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 56] s₀.mem s₄.mem ∧
    bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat)
      (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))
      (bytesAt s₀.mem S sl ++ (bytesAt s₀.mem D n).drop sl) ∧
    bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))

/-- What `seal_split`'s code `mid` after the entry must do: leave what
`SplitRunPost` says. -/
def MidOk (M : CtxMode) (mid : Prog isa) : Prop :=
  ∀ {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat},
    SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ →
    (below SP 56).Disjoint ⟨Ctx, M.len⟩ → SEntry s₀ Ctx W SP A D S n sl s₁ →
    s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al →
    WP isa mid s₁ (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl)

/-- After the entry, `seal_split` up to the tag at `W`: additional data
`aadP` that leaves what `oneAad` does (`OneMid`), code `pre` that encrypts
the first whole blocks of the plaintext (`PreOk`), and `body`. -/
theorem splitRun_of_pre {M : CtxMode} {pre : Prog isa} {qf : Nat → Nat → Nat} (hpre : PreOk M pre qf) {body : Prog isa}
    (hbody : BodyOk M body) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq pre body)) s₁ (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) := by
  unfold SplitRunPost
  have L := C.lay
  have hsl := C.sl_le
  have hn := C.data.ok.lt
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono ha fun s₂ M₂ => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M₂ ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M₂ ⊢
  generalize ha : bytesAt s₀.mem A al = a at M₂ ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ M₂.rounds
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  obtain ⟨hS₂, hsl₂⟩ := mid_slots C E M₂
  have P : PP M Ctx W SP D S R n sl s₂ := PP.ofMid C X kM hR M₂ hS₂ hsl₂
  have X₂ := P.ext
  refine WP.seq (WP.mono (hpre P) fun s₃ Q => ?_)
  generalize qf n sl = q at Q
  have fQ := Q.frame
  have rd₃ : s₃.rd = s₀.rd := Q.rd.trans M₂.rd
  have wr₃ : s₃.wr = s₀.wr := Q.wr.trans M₂.wr
  have hq := Q.le
  have wsl : ∀ d, 128 ≤ d → d + 8 ≤ 200 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    fQ.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (pp_wG L C.dE C.kw (.inr (.inl ⟨h₁, h₂⟩))) (by decide)
  have sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * q), n - 16 * q⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega_arith)
  have X₃ : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * q))
      (n - 16 * q) s₃ := (X₂.keep Q.rd Q.wr fQ (pp_outG X.cw X.cd kM.symm)).sub sD'
  have s240 : Region.Sub ⟨Ctx + BitVec.ofNat 64 240, 16⟩ ⟨Ctx, M.len⟩ := Offset.sub_base Ctx (by have := M.ge; omega_arith)
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fQ (pp_outG (X.cw.sub_left s240) (X.cd.sub_left s240) (kM.symm.sub_left s240)), M₂.hH]
  have hcb₃ : blockAt s₃.mem (cbA W) = Nat.repeat inc32 q (inc32 (Spec.Gcm.j0 H iv)) := by
    rw [Q.ctr]; exact congrArg _ M₂.cb
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [wsl 184 (by decide) (by decide), M₂.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hy₃ : blockAt s₃.mem (yA W) = ghashFrom H (blockAt s₂.mem (yA W))
      (blocks (bytesAt s₃.mem D (16 * q))) := by
    rw [Q.y, ← Proof.Gcm.blocksAt_eq, ctxH_eq, M₂.hH]
  have hAl : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hC1l : (bytesAt s₃.mem D (16 * q)).length % 16 = 0 := by rw [length_bytesAt]; omega_arith
  have habs₃ := Proof.Gcm.absorb_whole M₂.abs hAl hC1l hy₃
  have ez : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q) ++
      zeros (padLen (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q)).length) =
      a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q) := by
    have h3 : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q)).length % 16 = 0 := by
      rw [List.length_append]; omega_arith
    rw [padLen_mod h3]; simp [zeros]
  rw [← ez] at habs₃
  have hR₃ : RoundsAt s₃.mem W R := ⟨by rw [wsl 176 (by decide) (by decide)]; exact hRo.1, hRo.2⟩
  refine WP.mono (hbody L (R := R) (al := al) (N := n) Q.env hR₃ Q.dat Q.len ((C.data.of_eq rd₃ wr₃).drop hq) C.kw (C.kd.sub_right sD') kM C.sp56 X₃ hH₃
    hcb₃ hal₃ habs₃ Q.aux (by have := C.data.ok.lt; omega_arith)) fun s₄ ⟨e₄, rd₄, wr₄, f₄, hC₄, hT₄⟩ => ?_
  -- The cipher, kept.
  have kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s₀.mem Ctx R := ciph_frame M₂.frame (dM L.cw' L.kc) hR'
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s₀.mem Ctx R :=
    (ciph_frame fQ (pp_outG L.cw' C.data.ctx kc.symm) hR').trans hc₂
  -- The plaintext, kept by `aadP`.
  have hpt : splitPt s₂.mem D S n sl = splitPt s₀.mem D S n sl := by
    simp only [splitPt]
    rw [bytesAt_frame M₂.frame (dM C.sW (C.ks.sub_left b8)) (by omega_arith),
      bytesAt_frame M₂.frame (dM C.dE C.data.ok.stk) (by omega_arith)]
  have hC1 : bytesAt s₃.mem D (16 * q) =
      xorKs (ciphOf s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) 0 ((splitPt s₀.mem D S n sl).take (16 * q)) := by
    rw [Q.enc, hc₂, hpt, M₂.cb]
  have hC1₄ : bytesAt s₄.mem D (16 * q) = bytesAt s₃.mem D (16 * q) :=
    bytesAt_frame f₄ (sf_out (C.dE.sub_left (Region.sub_prefix hq)) (Offset.base_disjoint D (Nat.le_refl _) (by omega_arith))
      ((C.kd.sub_right (Region.sub_prefix hq)).symm)) (by omega_arith)
  have hD₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D (16 * q) ++
      bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * q)) (n - 16 * q) := by
    have e := bytesAt_add s₄.mem D (16 * q) (n - 16 * q)
    rw [Nat.add_sub_cancel' hq] at e
    rw [e, hC1₄]
  have hJ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [blockAt_frame fQ (pp_wG L C.dE C.kw (d := 16) (k := 16) (.inl (by decide)))]; exact M₂.j0
  refine ⟨e₄, rd₄.trans rd₃, wr₄.trans wr₃, (M₂.saved.frame fQ (pp_wG L C.dE C.kw (d := 128) (k := 48)
    (.inr (.inl ⟨Nat.le_refl _, by decide⟩)))).frame f₄ (saved_sf L (C.dE.sub_left sD') C.kw), ?_, ?_, ?_⟩
  · refine (M₂.frame.sub fun r hr => ?_).trans ((fQ.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨below SP 56, by simp, b8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun a hc => st_w a (cb_sub a hc)⟩
      · exact ⟨_, List.mem_cons_self .., fun a hc => st_w a (y_sub a hc)⟩
      · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., sc_w⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨⟨D, n⟩, by simp, sD'⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
  · rw [hD₄, hC₄, hc₃, hC1, Q.tail, hpt, Proof.Gcm.gctr_eq, ← xorKs_shift' _ _ q 0, Nat.add_zero]
    have e := Proof.Gcm.xorKs_append (ciphOf s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) 0
      ((splitPt s₀.mem D S n sl).take (16 * q)) ((splitPt s₀.mem D S n sl).drop (16 * q))
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by simp only [List.length_append, List.length_drop, length_bytesAt]; omega_arith), Nat.zero_add] at e
    exact e.symm
  · rw [hT₄, hc₃, hJ, padded_whole rfl hAl hC1l, ← hD₄]
    rfl

/-- After the entry, `seal_split` up to the tag at `W`: additional data
`aadP` that leaves what `oneAad` does (`OneMid`), `prefix` and `body`. -/
theorem splitRun_of_midB {M : CtxMode} (T : BlkToFn M) {body : Prog isa}
    (hbody : BodyOk M body) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (SealSplit.prefix T.fn) body)) s₁
      (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) :=
  splitRun_of_pre (prefixOk T) hbody C X kM E hal ha

/-- `splitRun_of_midB` with `SealSplit.body`. -/
theorem splitRun_of_mid (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfin : FinOk M fin) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (SealSplit.prefix T.fn) (SealSplit.body (v.withBlk B) fin))) s₁
      (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) :=
  splitRun_of_midB T (bodyOk_body B hfin) C X kM E hal ha

/-- After the entry, `seal_split` up to the tag at `W`: `oneAad`, `prefix` and
`body`. -/
theorem splitRun_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa} (hfin : FinOk M fin) :
    MidOk M (SealSplit.run (v.withBlk B) T.fn fin) := by
  intro s₀ s₁ Ctx W SP Np A D S T' nl al n sl C X kM E hNp hnl hal
  exact splitRun_of_mid v B T hfin C X kM E hal (oneMid_ok v C.toOneCtx E.toOneEntry hNp hnl hal)

/-- The key context, from `seal_split`'s precondition, and the 56 bytes below
the stack pointer apart from it. -/
theorem CtxExt.ofSplit {M : CtxMode} {s : State} (hp : Proof.AesGcm.splitPre M.len s)
    (hok : M.ok s.mem (s.gpr .rdi)) :
    CtxExt M (s.gpr .rdi) (stackArg s 5 + BitVec.ofNat 64 16) (stackArg s 5) (s.gpr .rsp) (stackArg s 2)
      (stackArg s 3).toNat s ∧ (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rdi, M.len⟩ := by
  simp only [Proof.AesGcm.splitPre, Proof.AesGcm.stk56, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, -, d_cd, d_cw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t_c, -, -, -, -, -, wc, -⟩ := hp
  exact ⟨⟨wc, d_cw.sub_right (Lay.wSub (by decide)), d_cw, d_cd, t_c.sub_left (below_sub (by decide) (by decide)),
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)), hok⟩, t_c⟩

/-- `vg_aes_gcm_seal_split`, for a key context of kind `M`. -/
theorem sealSplitM_wp {M : CtxMode} {mid : Prog isa} (hmid : MidOk M mid) {s : State}
    (hp : (Proof.AesGcm.sealSplitX86_64M M).pre s) :
    WP isa (SealSplit.«seal» mid) s fun s' =>
      gprPreserved s s' ∧ (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  obtain ⟨X, kM⟩ := CtxExt.ofSplit hp.1 hp.2
  have C := SplitCtx.of hp.1 M.ge
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 48) 64 = stackArg s 5 := rfl
  have hT' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := rfl
  have hta := C.args 4 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hS : stackArg s 0 = S at *
  generalize hsl : (stackArg s 1).toNat = sl at *
  generalize hD : stackArg s 2 = D at *
  generalize hn : (stackArg s 3).toNat = n at *
  generalize hT : stackArg s 4 = T' at *
  generalize hW : stackArg s 5 = W at *
  have L := C.lay
  unfold SealSplit.«seal»
  refine WP.seq (WP.mono (entry_ok C hCtx hSP hA hS hsl hD hn hW') fun s₁ E => ?_)
  refine WP.seq (WP.mono (hmid C X kM E hNp hnl hal)
    fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => WP.seq ?_)
  -- The tag copied to `tag`.
  have dA : ∀ r ∈ [(⟨W, 2560⟩ : Region), ⟨D, n⟩, below SP 56], (⟨SP + BitVec.ofNat 64 40, 8⟩ : Region).Disjoint r := by
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 40, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 6⟩ := by
      rw [show (40 : Nat) = 8 + 32 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.dA.sub_left hs
    · exact C.dAD.sub_left hs
    · exact Offset.disjoint_below SP (n := 56) (d := 40) (k := 8) (by decide)
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 40) 64 = T' := by
    rw [he₄.rsp, f₄.readW (r := ⟨SP + BitVec.ofNat 64 40, 8⟩) (Region.contains_self _ _) dA (by decide), hT']
  obtain ⟨s₅, run₅, hb₅, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 40) he₄.r15 hT₄'
    (by rw [he₄.rsp, hrd₄, hwr₄]; exact hta) he₄.perm.w (by rw [hwr₄]; exact C.tag)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have hsv₅ : SavedAt s₅.mem W s := hsv₄.frame f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (C.tW.sub_right (Lay.wSub (by decide))).symm
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₅ (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact C.rW
      · exact C.rD
      · exact Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact C.rT
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun _ => ?_⟩
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.tD.symm) (by have := C.data.ok.lt; omega_arith)
  simp only [Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hS, hsl, hD, hn, hT, Spec.Gcm.encryptWith, hm, hb₅, hT₄, hd₅, hC,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr]
  simp only [List.length_append, List.length_drop, length_bytesAt]
  rw [Nat.add_sub_cancel' C.sl_le]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64.Split
