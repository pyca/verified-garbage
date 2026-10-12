import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.PrePost
import VerifiedGarbage.Proof.AesCbc.X86_64.Body

/-!
# One-pass XTS-AES on x86-64: sixteen blocks at a time

`GInv enc KP s₀ b c`: after `c` blocks, with the tweaks of blocks `b … b + 15`
at `scratch + 256`: the registers hold the moved arguments (the tweak pointer
still in `rdx`), only the data and the scratch buffer have changed, and the
first `c` blocks are XTS's (`outBlk`) and the rest unchanged. `KP` is what the rounds need (the key schedule, and for
decryption the round keys through `aesimc` in the scratch buffer below the
tweaks), kept by writes to the data and the tweaks (`Stable`).

`group_wp`: one run of `group f16` takes `GInv` from `c` to `c + 16`, for
rounds `f16` computing the cipher (or its inverse) on both lanes of
`ymm0`–`ymm7` (`Blk16`).
-/

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff group preXor postXor steps)
open VG.Impl.Aes.X86_64.Vaes (regs8)
open VG.Proof.AesXts (b16 next_b16)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast)

/-- The tweak of block `b + j` is at `slot s₀ j`. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (bufOff + 16 * j)

/-- The scratch buffer from the tweaks on. -/
abbrev bufR (s₀ : State) : Region := ⟨S s₀ + BitVec.ofNat 64 bufOff, 1920⟩

/-- What the rounds need is kept by writes to the data and the tweaks. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → s'.gpr .rdi = s.gpr .rdi → s'.gpr .rsi = s.gpr .rsi → s'.gpr .r8 = s.gpr .r8 →
    s'.gpr .r10 = s.gpr .r10 → s'.rd = s.rd → s'.wr = s.wr → Frame [dataR s₀, bufR s₀] s.mem s'.mem → KP s'

/-- `f16` computes the cipher (or its inverse) on both lanes of `ymm0`–`ymm7`. -/
def Blk16 (enc : Bool) (f16 : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f16 regs8) s fun s' =>
    (∀ b ∈ regs8, ∀ l < 2, st (s'.lane b l) = stF enc (R s₀) (wK s₀) (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs8) s s'

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
  buf : ∀ j < 16, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j)
  rdx : s.gpr .rdx = Iv s₀

theorem next_add (t : List Byte) (a b : Nat) : Spec.Xts.next t (a + b) = Spec.Xts.next (Spec.Xts.next t a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, Spec.Xts.next, Nat.repeat, ← Spec.Xts.next, ih]; rfl

section
variable {s₀ : State}

/-- Block `c + 2k + l` from block `c`. -/
theorem blk_lane (c k l : Nat) : blk s₀ c + BitVec.ofNat 64 (32 * (0 + k) + 16 * l) = blk s₀ (c + (2 * k + l)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

theorem slot_lane (k l : Nat) : S s₀ + BitVec.ofNat 64 (bufOff + 32 * (0 + k) + 16 * l) = slot s₀ (2 * k + l) := by
  congr 2; omega

theorem slot_scr {j : Nat} (hj : j < 16) : Region.Sub ⟨slot s₀ j, 16⟩ (scrR s₀) :=
  UPre.scr_sub (by simp only [bufOff]; omega)

theorem slot_buf {j : Nat} (hj : j < 16) : Region.Sub ⟨slot s₀ j, 16⟩ (bufR s₀) := by
  rw [slot, show S s₀ + BitVec.ofNat 64 (bufOff + 16 * j) = S s₀ + BitVec.ofNat 64 bufOff + BitVec.ofNat 64 (16 * j) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  exact Offset.sub_base _ (by omega)

/-- The blocks of a group lie in the data. -/
theorem group_data {c : Nat} (hc : c + 16 ≤ N s₀) : Region.Sub ⟨blk s₀ c, 256⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega)

theorem tw_buf : Region.Sub ⟨S s₀ + BitVec.ofNat 64 bufOff, 256⟩ (bufR s₀) :=
  Region.sub_prefix (by decide)

theorem tw_scr : Region.Sub ⟨S s₀ + BitVec.ofNat 64 bufOff, 256⟩ (scrR s₀) :=
  UPre.scr_sub (d := bufOff) (n := 256) (by decide)

theorem buf_scr : Region.Sub (bufR s₀) (scrR s₀) := UPre.scr_sub (d := bufOff) (n := 1920) (by decide)

theorem UPre.blk_slot (hp : UPre s₀) {k j : Nat} (hk : k < N s₀) (hj : j < 16) :
    Region.Disjoint ⟨blk s₀ k, 16⟩ ⟨slot s₀ j, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (slot_scr hj)

end

/-- One group of sixteen blocks. -/
theorem group_wp {enc : Bool} {KP : State → Prop} {f16 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f16 KP s₀) {c : Nat} (hc : c + 16 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ c c s) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (group f16) s fun s' =>
      (GInv enc KP s₀ (c + 16) (c + 16) s' ∧ ∀ l < 2, qword (s'.lane .xmm11 l) 0 = 0x87) ∧
        s'.cf = some (decide (N s₀ - (c + 16) < 16)) := by
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have inD : ∀ k < 8, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int)) 32 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have inB : ∀ k < 8, InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * (0 + k) : Nat) : Int)) 32 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r8, ofInt_natCast]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (preList_ok regs8 0 s (by decide) (fun k hk => inRegions_wr (inD k hk))
    (fun k hk => inRegions_wr (inB k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
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
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postList_ok regs8 0 s₂ (by decide) (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inB k hk)) (by rw [g₂, h.r11, hp.blk_toNat (by omega)]; show _ + 32 * (0 + 8) ≤ _; omega)
    (fun k hk l hl => by
      rw [g₂, h.r8, h.r11, slot_lane, Nat.mul_zero, BitVec.add_zero, show 32 * regs8.length = 256 from rfl]
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right (slot_scr (j := 2 * k + l) (by have : regs8.length = 8 := rfl; omega))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 32 * regs8.length = 256 from rfl] at f₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  have hK₃ : ∀ l < 2, qword (s₃.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [x₃ _ (by decide) l hl, f₂.lane _ (by decide) l hl, x₁ _ (by decide) l hl]; exact hK l hl
  -- The tweaks times `α¹⁶`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok s₃ hK₃ (fun k hk => by rw [wr₃, wr₂, g₃']; simpa using inB k hk)
      (by rw [g₃', h.r8]; simp only [bufOff]; omega) 8 (Nat.le_refl _))
    fun s₄ ⟨e₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_
  rw [g₃', h.r8] at e₄ f₄
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄ (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, tw_buf⟩)
  have hK₄ : ∀ l < 2, qword (s₄.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [x₄ _ (by decide) (by decide) l hl]; exact hK₃ l hl
  -- The memory after the group.
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem :=
    h.frame.trans ((f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩).trans
      (f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, tw_scr⟩))
  have blk_tw : ∀ k < N s₀, ∀ r ∈ [(⟨S s₀ + BitVec.ofNat 64 bufOff, 256⟩ : Region)], Region.Disjoint ⟨blk s₀ k, 16⟩ r :=
    fun k hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right tw_scr
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 16 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [AesCbc.X86_64.bytesAt_frame f₄ (blk_tw k hk) (by decide)]
    by_cases hin : c ≤ k ∧ k < c + 16
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < 16 := by omega
      have hkk : i / 2 < regs8.length := by have : regs8.length = 8 := rfl; omega
      have hl : i % 2 < 2 := Nat.mod_lt _ (by decide)
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (32 * (0 + i / 2) + 16 * (i % 2)) := by
        rw [h.r11, blk_lane]; congr 2; omega
      have sl : slot s₀ i = s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (0 + i / 2) + 16 * (i % 2)) := by
        rw [h.r8, slot_lane]; congr 2; omega
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← sl, m₂, ← ab]
      have e1 := e₁ _ hkk _ hl
      rw [← ab, ← sl] at e1
      have hc' : st (s₂.lane regs8[i / 2] (i % 2)) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ i) 128)) := by
        rw [e₂ _ (List.getElem_mem hkk) _ hl, e1]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', ← bytesAt_b16, ← bytesAt_b16, h.buf i hi,
        h.data _ hk]
      simp only [show ¬ c + i < c by omega, ite_false, show c + i < c + 16 by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 16 by omega]
      · simp only [hlt, ite_false, show ¬ k < c + 16 by omega]
  have hbuf : ∀ j < 16, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (c + 16 + j) := by
    intro j hj
    rw [bytesAt_b16, e₄ j hj]
    simp only [show j < 2 * 8 by omega, ite_true]
    rw [f₃.readW (r := ⟨slot s₀ j, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right (slot_scr hj)).symm) (by decide)]
    rw [stepW, ← next_b16, ← bytesAt_b16, h.buf j hj, ← next_add]
    congr 1; omega
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, h.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, h.wr]
  -- `add r11, 256`, `sub r9, 16` and `cmp r9, 16`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 16 = BitVec.ofNat 64 (N s₀ - (c + 16)) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + 256 = blk s₀ (c + 16) := by
    rw [blk, blk, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 256 = 16 * (c + 16) by omega]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hN := hp.data_wrap
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, fun l hl => hK₄ l hl⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 16) < 2 ^ 64 by omega),
    show (16 : BitVec 64).toNat = 16 from rfl]

end VG.Proof.AesXts.X86_64.Vaes
