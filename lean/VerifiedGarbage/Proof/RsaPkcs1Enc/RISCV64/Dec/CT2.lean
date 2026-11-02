module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT1
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Irprf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Irprf
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time of `CL` and `AM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCT3.lean`): a block of IRPRF in two runs
(`prfBody_ct`), its blocks by the taint analysis and its calls by
`macInit_rel`, …, with the counter `i` in `s8` and the number of `AM`'s blocks
in `s9` (`L i`); and the loops of `CL` and `AM`, whose counters agree
(`clLoop_ct`, `amLoop_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

/-- The number of `AM`'s blocks. -/
abbrev nbOf (s : State) : BitVec 64 := BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32)

/-- The counter and the number of `AM`'s blocks. -/
def W8 (i : Nat) (s u : State) : Prop := u.gpr .s8 = BitVec.ofNat 64 i ∧ u.gpr .s9 = nbOf s

/-- In the loops, before block `i`. -/
def L (i : Nat) (s u : State) : Prop := PostAt s u ∧ W8 i s u

theorem W8.only {i : Nat} {s u v : State} (w : W8 i s u) {rs : List Reg} (o : Kept rs u v)
    (h8 : Reg.s8 ∉ rs := by decide) (h9 : Reg.s9 ∉ rs := by decide) : W8 i s v :=
  ⟨(o.gpr _ h8).trans w.1, (o.gpr _ h9).trans w.2⟩

theorem W8.after {i : Nat} {s u v : State} (w : W8 i s u) {ws : List Region} (a : After u ws v) : W8 i s v :=
  ⟨(a.cs _ (by decide)).trans w.1, (a.cs _ (by decide)).trans w.2⟩

section
variable {e : Env}

theorem w8_agree {i : Nat} {a b : State} (ha : W8 i e.s₁ a) (hb : W8 i e.s₂ b) :
    a.gpr .s8 = b.gpr .s8 ∧ a.gpr .s9 = b.gpr .s9 :=
  ⟨by rw [ha.1, hb.1], by rw [ha.2, hb.2, nbOf, nbOf, e.r]⟩

/-- Two runs that satisfy `PostAt` and `W8 i` agree on `s0`–`s6`, `s8` and `s9`. -/
theorem pin_L {P : State → State → Prop} {i : Nat} (hp : ∀ s u, P s u → PostAt s u ∧ W8 i s u) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s8, .s9] := by decide) :
    ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b := fun a b ha hb => by
  obtain ⟨⟨_, _, A⟩, wa⟩ := hp _ _ ha
  obtain ⟨⟨_, _, B⟩, wb⟩ := hp _ _ hb
  have g := post_agree A B
  have g8 := w8_agree wa wb
  refine ⟨g.1, fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2, g8.1, g8.2]

/-- The taint checks of a block of IRPRF's blocks. -/
structure PrfTaint (label : List Nat) (len count : List Instr) (dst : Nat) : Prop where
  msg : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0, .s1, .s8]) (.block (msgBytes label len)) hc).isSome = true
  ini : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0]) (.block (macInitArgs sKDK)) hc).isSome = true
  upd : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0]) (.block (prfUpdArgs (label.length + 4))) hc).isSome = true
  fin : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0, .s8]) (.block (prfFinArgs (label.length + 4) dst)) hc).isSome
    = true
  incr : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s8, .s9]) (.block (incr count)) hc).isSome = true

/-- Block `i` of IRPRF, in two runs: after it, `L (i + 1)` and the blocks left
`C - (i + 1)` in `t1`, for `C` a function of the entry state. -/
theorem prfBody_ct {label : List Nat} {len count : List Instr} {dst : Nat} (T : PrfTaint label len count dst)
    {C : State → BitVec 64} {i : Nat} (hi : i < 256) (hd1 : sCL ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes)
    (hdst : dst < 2048) (hn : label.length + 4 ≤ 16)
    (hmsg : ∀ s R EM u, DPre s → Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w => Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ s u, u.gpr .s9 = nbOf s →
      WP isa (.block (count ++ [.sub .t1 .t1 .s8])) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C s - u.gpr .s8) :
    RelCT isa (Rel e (L i)) (prfBody label len dst count)
      (Rel e fun s u => L (i + 1) s u ∧ u.gpr .t1 = C s - BitVec.ofNat 64 (i + 1)) := by
  have zz := hmac_sizes
  unfold prfBody
  -- The message.
  refine RelCT.seq (rel_post (P' := L i) (rel_of T.msg.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => WP.mono (hmsg s _ _ u h P w.1) fun v ⟨F, K⟩ =>
      ⟨⟨_, _, P.keep h K F fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub h (by decide))⟩,
        w.only K⟩) ?_
  -- HMAC's `init` with `KDK`.
  refine RelCT.seq (rel_post (P' := fun s u => MI sKDK s u ∧ W8 i s u)
    (rel_of T.ini.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => macInitArgs_ok h P (by decide) fun v P' a0 a1 a2 a3 _ K =>
      ⟨⟨⟨_, _, P'⟩, a0, a1, a2, a3⟩, w.only K⟩) ?_
  refine RelCT.seq (rel_post (P' := L i) (macInit_rel (by decide) (by decide) fun _ _ h => h.1)
    fun s u h ⟨⟨⟨_, _, P⟩, a0, a1, a2, a3⟩, w⟩ =>
      macInit_ok h P (i := sSt) (u := sOuter) (k := sKDK) (by decide) (by decide) (by decide) (.inl (by decide))
        (.inr (by decide)) (.inr (by decide)) a0 a1 a2 a3 fun v P' A _ _ => ⟨⟨_, _, P'⟩, w.after A⟩) ?_
  -- `update` with the message.
  refine RelCT.seq (rel_post (P' := fun s u => (UpdAt s u sSt (scA s sMsg) (label.length + 4) ∧
      u.gpr .a1 = BitVec.ofNat 64 64) ∧ W8 i s u)
    (rel_of T.upd.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2) fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_) ?_
  · unfold prfUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
      wp_addi (imm := sMsg) (fun v₃ p₃ f₃ => wp_li (imm := label.length + 4) (by omega) fun v₄ p₄ f₄ =>
        wp_nil ?_) (by decide)) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    have lm : sMsg + (label.length + 4) ≤ scrBytes := by unfold sMsg scrBytes; omega
    exact ⟨⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P.s0], by rw [f₄, BitVec.toNat_ofNat]; omega,
      Covers.right (scCov h P₄.wr lm), scDisj (.inr (by decide)) lm (by decide), lowSc h (by decide) lm⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩, w.only O.keep⟩
  refine RelCT.seq (rel_post (P' := L i) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => scA s sMsg)
    (len := fun _ => label.length + 4) (e.scA_eq _) rfl (fun _ _ h => h.1.1)
    fun _ _ h₁ h₂ => by rw [h₁.1.2, h₂.1.2])
    fun s u h ⟨⟨U, _⟩, w⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun v P' A _ => ⟨⟨_, _, P'⟩, w.after A⟩
  -- HMAC's `finalize` to the block.
  refine RelCT.seq (rel_post (P' := fun s u => MF (dst + 32 * i) (fun _ => BitVec.ofNat 64 (64 + (label.length + 4)))
      s u ∧ W8 i s u)
    (rel_of T.fin.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2) fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_) ?_
  · unfold prfFinArgs
    refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
      wp_li (imm := 64 + (label.length + 4)) (by omega) fun w₃ q₃ g₃ => wp_sll (sh := 5) (fun w₄ q₄ g₄ =>
      wp_add fun w₅ q₅ g₅ => wp_addi (imm := dst) (fun w₆ q₆ g₆ => wp_nil ?_) hdst)) (by decide)) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u w₆ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans q₆))))).mono
    exact ⟨⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [q₆.get .a0, q₅.get .a0, q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P.s0],
      by rw [q₆.get .a1, q₅.get .a1, q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P.s0],
      by rw [q₆.get .a2, q₅.get .a2, q₄.get .a2, g₃],
      by rw [g₆, g₅, g₄, q₃.get .s8, q₂.get .s8, q₁.get .s8, w.1, q₄.get .s0, q₃.get .s0, q₂.get .s0,
        q₁.get .s0, P.s0, shl5]⟩, w.only O.keep⟩
  refine RelCT.seq (rel_post (P' := L i) (macFin_rel hd2 (by unfold sOuter sCL at *; omega) rfl fun _ _ h => h.1)
    fun s u h ⟨⟨⟨_, _, P⟩, a0, a1, _, a3⟩, w⟩ =>
      macFin_ok h P (i := sSt) (u := sOuter) (o := dst + 32 * i) (by decide) (by decide) hd2 (.inl (by decide))
        (.inl (by unfold sSt sCL at *; omega)) (.inl (by unfold sOuter sCL at *; omega)) a0 a1 a3
        fun v P' A _ => ⟨⟨_, _, P'⟩, w.after A⟩) ?_
  -- The counter.
  refine rel_post (rel_of T.incr.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_
  simp only [incr, List.cons_append, List.nil_append]
  refine wp_addi (imm := 1) (fun x₁ r₁ i₁ => WP.mono (hcount s x₁ (by rw [r₁.get .s9, w.2]))
    fun v ⟨Ov, xv⟩ => ?_) (by decide)
  have O : Only [.s8, .t1] u v := (r₁.trans Ov).mono
  have one : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := BitVec.ofNat_add _ _ |>.symm
  exact ⟨⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
    by rw [Ov.get .s8, i₁, w.1, one], by rw [O.get .s9, w.2]⟩, by rw [xv, i₁, w.1, one]⟩

/-- The loop of IRPRF's `N` blocks, in two runs, with `C - (i + 1)` blocks
left after block `i`. -/
theorem prfLoop_ct {label : List Nat} {len count : List Instr} {dst N : Nat} (T : PrfTaint label len count dst)
    {C : State → BitVec 64} (hC : C e.s₁ = C e.s₂) (hCN : ∀ i < N,
      C e.s₁ - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hN0 : 0 < N) (hN : N ≤ 256) (hd1 : sCL ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 2048)
    (hn : label.length + 4 ≤ 16)
    (hmsg : ∀ i < N, ∀ s R EM u, DPre s → Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w => Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ s u, u.gpr .s9 = nbOf s →
      WP isa (.block (count ++ [.sub .t1 .t1 .s8])) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C s - u.gpr .s8) :
    RelCT isa (Rel e (L 0)) (.loop (prfBody label len dst count) (.nonzero .t1))
      (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) := by
  refine (RelCT.loop (Q := Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) (fun m a b => ∃ i, m = N - i ∧ i < N ∧ Rel e (L i) a b)
    (fun m => ?_) N).mono (fun a b h => ⟨0, by omega, hN0, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hm, hiN, hp⟩ e₁ e₂
  obtain ⟨ht, ⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ := prfBody_ct (e := e) T (C := C) (i := i) (by omega) hd1 (by omega) hdst hn
    (hmsg i hiN) hcount s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have v₁ : s₁'.gpr .t1 = BitVec.ofNat 64 (N - (i + 1)) := by rw [c₁, hCN i hiN]
  have v₂ : s₂'.gpr .t1 = BitVec.ofNat 64 (N - (i + 1)) := by rw [c₂, ← hC, hCN i hiN]
  have hz : isa.eval (.nonzero .t1) s₁' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero, ne_zero_iff, v₁]
    exact congrArg some (decide_eq_decide.mpr (counter_ne hiN (by omega)))
  have hz₂ : isa.eval (.nonzero .t1) s₂' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero, ne_zero_iff, v₂]
    exact congrArg some (decide_eq_decide.mpr (counter_ne hiN (by omega)))
  refine ⟨ht, by rw [hz, hz₂], fun hf => ⟨⟨l₁.1, l₁.2.2⟩, ⟨l₂.1, l₂.2.2⟩⟩, fun ht' => ⟨N - (i + 1), by
    rw [hz] at ht'; simp at ht'; omega, i + 1, rfl, by rw [hz] at ht'; simp at ht'; omega, l₁, l₂⟩⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
