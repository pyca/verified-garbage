module
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Common
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame

import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.PrePost
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.List.Induction

/-!
# One-pass XTS-AES on x86-64: eight blocks at a time

`GInv enc KP s₀ b c`: after `c` blocks, with the tweaks of blocks `b … b + 7`
at `scratch + 256`: the registers hold the moved arguments (the tweak pointer
still in `rdx`), only the data and the scratch buffer have changed, and the
first `c` blocks are XTS's (`outBlk`) and the rest unchanged. `KP` is what the rounds need (the key schedule, and for
decryption the round keys through `aesimc` in the scratch buffer below the
tweaks), kept by writes to the data and the tweaks (`Stable`).

`TwR s₀ c`: the tweak registers `ymm4`–`ymm7` hold the tweaks of blocks
`c … c + 7`, and `ymm11` the constant `0x87` in both lanes. `group_wp`: one
run of `group f8` takes `GInv b c ∧ TwR c` to `c + 8`, for rounds `f8`
computing the cipher (or its inverse) on both lanes of `ymm0`–`ymm3`
(`Blk8`); it writes only the data.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff group preXor postXor steps regs4 tws)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast)

/-- The tweak of block `b + j` is at `slot s₀ j`. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (bufOff + 16 * j)

/-- The scratch buffer from the tweaks on. -/
abbrev bufR (s₀ : State) : Region := ⟨S s₀ + BitVec.ofNat 64 bufOff, 1920⟩

/-- What the rounds need is kept by writes to the data and the tweaks. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → s'.gpr .rdi = s.gpr .rdi → s'.gpr .rsi = s.gpr .rsi → s'.gpr .r8 = s.gpr .r8 →
    s'.gpr .r10 = s.gpr .r10 → s'.rd = s.rd → s'.wr = s.wr → Frame [dataR s₀, bufR s₀] s.mem s'.mem → KP s'

/-- `f8` computes the cipher (or its inverse) on both lanes of `ymm0`–`ymm3`. -/
def Blk8 (enc : Bool) (f8 : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f8 regs4) s fun s' =>
    (∀ b ∈ regs4, ∀ l < 2, st (s'.lane b l) = stF enc (R s₀) (wK s₀) (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs4) s s'

/-- Block `k` after XTS. -/
abbrev outBlk (enc : Bool) (s₀ : State) (k : Nat) : List Byte :=
  Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k) (bytesAt s₀.mem (blk s₀ k) 16)

structure GInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  kp : KP s
  le : c ≤ N s₀
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀ - c)
  r11 : s.gpr .r11 = blk s₀ c
  r10 : s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 = if k < c then outBlk enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16
  buf : ∀ j < 8, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j)
  rdx : s.gpr .rdx = Iv s₀

/-- In the loop: the tweaks of blocks `c … c + 7` in `ymm4`–`ymm7`, and
`0x87` in both lanes of `ymm11`. -/
structure TwR (s₀ : State) (c : Nat) (s : State) : Prop where
  tw : ∀ k (h : k < tws.length), ∀ l < 2, b16 (s.lane tws[k] l) = Spec.Xts.next (iv0 s₀) (c + (2 * k + l))
  k87 : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87

theorem next_add (t : List Byte) (a b : Nat) : Spec.Xts.next t (a + b) = Spec.Xts.next (Spec.Xts.next t a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, Spec.Xts.next, Nat.repeat, ← Spec.Xts.next, ih]; rfl

section
variable {s₀ : State}

/-- Block `c + 2k + l` from block `c`. -/
theorem blk_lane (c k l : Nat) : blk s₀ c + BitVec.ofNat 64 (32 * (0 + k) + 16 * l) = blk s₀ (c + (2 * k + l)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith

theorem slot_scr {j : Nat} (hj : j < 16) : Region.Sub ⟨slot s₀ j, 16⟩ (scrR s₀) :=
  UPre.scr_sub (by simp only [bufOff]; omega_arith)

/-- The blocks of a group lie in the data. -/
theorem group_data {c : Nat} (hc : c + 8 ≤ N s₀) : Region.Sub ⟨blk s₀ c, 128⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega_arith)

theorem buf_scr : Region.Sub (bufR s₀) (scrR s₀) := UPre.scr_sub (d := bufOff) (n := 1920) (by decide)

end

theorem tws_regs4 : ∀ t ∈ tws, t ∉ regs4 := by decide

/-- One group of eight blocks. -/
theorem group_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {b c : Nat} (hc : c + 8 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ b c s) (ht : TwR s₀ c s) :
    WP isa (group f8) s fun s' =>
      (GInv enc KP s₀ b (c + 8) s' ∧ TwR s₀ (c + 8) s') ∧ s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hw := hp.data_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have inD : ∀ k < 4, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int)) 32 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (preList_ok regs4 tws 0 s (by decide) rfl tws_regs4
    (fun k hk => inRegions_wr (inD k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ h.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  -- Registers outside the blocks' are as they were.
  have o₂ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₂.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [f₂.lane r (by simp [h8, hr]) l hl, x₁ r hr l hl]
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postList_ok regs4 tws 0 s₂ (by decide) rfl tws_regs4
    (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (by rw [g₂, h.r11, hp.blk_toNat (by omega_arith)]; show _ + 32 * (0 + 4) ≤ _; omega_arith))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 32 * regs4.length = 128 from rfl] at f₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  have o₃ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₃.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [x₃ r hr l hl, o₂ r hr h8 l hl]
  have hK₃ : ∀ l < 2, qword (s₃.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [o₃ _ (by decide) (by decide) l hl]; exact ht.k87 l hl
  -- The tweaks times `α⁸`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok tws (by decide) (by decide) (by decide) s₃ hK₃)
    fun s₄ ⟨e₄, g₄, m₄, rd₄, wr₄, x₄⟩ => ?_
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄
    (by rw [m₄]; exact Frame.refl _ _)
  have hK₄ : ∀ l < 2, qword (s₄.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [x₄ _ (by decide) (by decide) l hl]; exact hK₃ l hl
  -- The memory after the group.
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    rw [m₄]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 8 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [m₄]
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      have hi : i < 8 := by omega_arith
      have hkk : i / 2 < regs4.length := by have : regs4.length = 4 := rfl; omega_arith
      have hkt : i / 2 < tws.length := by have : tws.length = 4 := rfl; omega_arith
      have hl : i % 2 < 2 := Nat.mod_lt _ (by decide)
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (32 * (0 + i / 2) + 16 * (i % 2)) := by
        rw [h.r11, blk_lane]; congr 2; omega_arith
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← ab]
      have hT : s₂.lane tws[i / 2] (i % 2) = s.lane tws[i / 2] (i % 2) :=
        o₂ _ (tws_regs4 _ (List.getElem_mem hkt)) (by
          have : tws[i / 2] ∈ tws := List.getElem_mem hkt
          intro h8; rw [h8] at this; exact absurd this (by decide)) _ hl
      have e1 := e₁ _ hkk _ hl
      rw [← ab] at e1
      have hc' : st (s₂.lane regs4[i / 2] (i % 2)) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.lane tws[i / 2] (i % 2))) :=
        (e₂ _ (List.getElem_mem hkk) _ hl).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      rw [hT]
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ht.tw _ hkt _ hl, h.data _ hk, show c + (2 * (i / 2) + i % 2) = c + i by omega_arith]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + 8 by omega_arith, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 8 by omega_arith]
      · simp only [hlt, ite_false, show ¬ k < c + 8 by omega_arith]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := by
    intro j hj
    rw [m₄, AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right (slot_scr (j := j) (by omega_arith))).symm) (by decide),
      h.buf j hj]
  have htw : ∀ k (hk : k < tws.length), ∀ l < 2,
      b16 (s₄.lane tws[k] l) = Spec.Xts.next (iv0 s₀) (c + 8 + (2 * k + l)) := by
    intro k hk l hl
    have hm : tws[k] ∈ tws := List.getElem_mem hk
    rw [e₄ _ hm l hl, o₃ _ (tws_regs4 _ hm) (by intro h8; rw [h8] at hm; exact absurd hm (by decide)) l hl,
      stepW, ← next_b8, ht.tw k hk l hl, ← next_add]
    congr 1; omega_arith
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, h.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, h.wr]
  -- `add r11, 128`, `sub r9, 8` and `cmp r9, 8`.
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  have hadd : blk s₀ c + 128 = blk s₀ (c + 8) := by
    rw [blk, blk, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 128 = 16 * (c + 8) by omega_arith]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hN := hp.data_wrap
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, ⟨htw, hK₄⟩⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

end VG.Proof.AesXts.X86_64.Vaes
