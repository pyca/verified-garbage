import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Loop
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.TailOps

/-!
# One-pass XTS-AES on x86-64: the blocks left

After the sixteen-block loop, fewer than sixteen blocks are left, with their
tweaks at `scratch + 256` on (`GInv b c` with `b = c`). `TInv b c` adds that
`rax` points at the tweak of block `c`. `tcore_ok`: the blocks `c … c + n − 1`
through the AES-NI round code `f` on `n` block registers (`regs8` or
`xmm0`), their tweaks XORed in before and after; `tail_wp` composes eight and
then one at a time.
-/

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff tPre tPost)
open VG.Impl.Aes.X86_64.AesNi (regs8)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast XFrame)

/-- `f` computes the cipher (or its inverse) on `xmm0`–`xmm7`, or on `xmm0`. -/
def Blk1 (enc : Bool) (f : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ rs, (rs = regs8 ∨ rs = [.xmm0]) → ∀ s, KP s → WP isa (f rs) s fun s' =>
    (∀ b ∈ rs, st (s'.xmm b) = stF enc (R s₀) (wK s₀) (st (s.xmm b))) ∧ XFrame (.xmm8 :: rs) s s'

/-- In the tail: `rax` points at the tweak of block `c`. -/
structure TInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  g : GInv enc KP s₀ b c s
  bc : b ≤ c
  lt : N s₀ < b + 16
  rax : s.gpr .rax = slot s₀ (c - b)

/-- `n` blocks from block `c` lie in the data. -/
theorem group_data_n {s₀ : State} {c n : Nat} (hc : c + n ≤ N s₀) : Region.Sub ⟨blk s₀ c, 16 * n⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega)

theorem regs_cases (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) : rs.Nodup ∧ rs.length ≤ 8 := by
  rcases h with rfl | rfl <;> decide

/-- The blocks `c … c + n − 1` through `f` on `n` block registers `rs`, and
the pointers advanced. -/
theorem tbody_ok {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) (rs : List XReg) (n : Nat)
    (hrs : (rs = regs8 ∧ n = 8) ∨ (rs = [.xmm0] ∧ n = 1))
    {b c : Nat} (hc : c + n ≤ N s₀) {s : State} (h : TInv enc KP s₀ b c s) :
    WP isa (.seq (.block (tPre rs 0)) (.seq (f rs) (.block (tPost rs 0 ++
        ([.alu .add .r11 (.imm (BitVec.ofNat 32 (16 * n))), .alu .add .rax (.imm (BitVec.ofNat 32 (16 * n))),
          .alu .sub .r9 (.imm (BitVec.ofNat 32 n))] : List Instr))))) s fun s' =>
      TInv enc KP s₀ b (c + n) s' ∧ s'.zf = some (decide (N s₀ - (c + n) = 0)) := by
  have hlen : rs.length = n := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hnd : rs.Nodup := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hn8 : n ≤ 8 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hrs' : rs = regs8 ∨ rs = [.xmm0] := by rcases hrs with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hx8 : XReg.xmm8 ∉ rs := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hg := h.g
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have inD : ∀ k < rs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [hg.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have inT : ∀ k < rs.length, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.rax, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (tPreList_ok rs 0 s hnd (fun k hk => inRegions_wr (inD k hk))
    (fun k hk => inRegions_wr (inT k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ hg.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf rs hrs' s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  -- The tweaks XORed in again, and the blocks stored.
  rw [WP.block_append_iff]
  have hr11N : (s.gpr .r11).toNat = (Dp s₀).toNat + 16 * c := by rw [hg.r11]; exact hp.blk_toNat (by omega)
  refine WP.mono (tPostList_ok rs 0 s₂ hnd (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inT k hk)) (by rw [g₂, hr11N]; omega)
    (fun k hk => by
      rw [g₂, h.rax, hg.r11, Nat.mul_zero, BitVec.add_zero, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hp.data_scr.sub_left (group_data_n (s₀ := s₀) (c := c) (n := rs.length) (by omega))).sub_right
        (UPre.scr_sub (by simp only [bufOff]; omega))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, hg.r11, Nat.mul_zero, BitVec.add_zero, m₂, hlen] at f₃
  rw [g₂, m₂] at e₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₃.mem (blk s₀ k) 16 = if k < c + n then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    by_cases hin : c ≤ k ∧ k < c + n
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < rs.length := by omega
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [hg.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      have sl : slot s₀ (c - b + i) = s.gpr .rax + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [h.rax, slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [bytesAt_b16, ab, e₃ _ hi, ← sl, ← ab]
      have e1 := e₁ _ hi
      rw [← ab, ← sl] at e1
      have hc' : st (s₂.xmm rs[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ (c - b + i)) 128)) := by
        rw [e₂ _ (List.getElem_mem hi), e1]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', ← bytesAt_b16, ← bytesAt_b16, hg.buf _ (by omega),
        hg.data _ hk, show b + (c - b + i) = c + i by omega]
      simp only [show ¬ c + i < c by omega, ite_false, show c + i < c + n by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), hg.data k hk]
      by_cases hlt' : k < c
      · simp only [hlt', ite_true, show k < c + n by omega]
      · simp only [hlt', ite_false, show ¬ k < c + n by omega]
  have hbuf : ∀ j < 16, bytesAt s₃.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := fun j hj => by
    rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr hj)).symm) (by decide), hg.buf j hj]
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₃.mem :=
    hg.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hrd : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hg.rd]
  have hwr : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hg.wr]
  -- `add r11, 16 n`, `add rax, 16 n` and `sub r9, n`.
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * n)) = BitVec.ofNat 64 (16 * n) := by
    rcases hrs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have e1 : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
    rcases hrs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hr11 : s₃.gpr .r11 = blk s₀ c := by rw [g₃', hg.r11]
  have hrax : s₃.gpr .rax = slot s₀ (c - b) := by rw [g₃', h.rax]
  have hr9 : s₃.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₃', hg.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - BitVec.ofNat 64 n = BitVec.ofNat 64 (N s₀ - (c + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + BitVec.ofNat 64 (16 * n) = blk s₀ (c + n) := by
    rw [blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * c + 16 * n = 16 * (c + n) by omega]
  have hadd' : slot s₀ (c - b) + BitVec.ofNat 64 (16 * n) = slot s₀ (c + n - b) := by
    rw [slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hr11, hrax, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₃ _ kp₃ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₃', hg.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₃', hg.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h5, h7, g₃', hg.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₃', hg.rdx]⟩, by omega, hlt, by simp; exact hadd'⟩, ?_⟩
  simp only [hsub]
  exact Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (by have := (s₀.gpr .r8).isLt; omega)

open VG.Impl.AesXts.X86_64Vaes (tail tail8 tail1)

/-- The blocks left, eight and then one at a time. -/
theorem tail_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) {c : Nat} (hlt : N s₀ < c + 16) {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (tail f) s (TInv enc KP s₀ c (N s₀)) := by
  have hle := h.le
  have hn := (s₀.gpr .r8).isLt
  -- `mov rax, r8`, `add rax, 256` and `cmp r9, 8`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr8 := h.r8
  have hr9 := h.r9
  have st₁ : WP isa (.block [.mov .rax (.reg .r8), .alu .add .rax (.imm 256), .alu .cmp .r9 (.imm 8)]) s
      fun s₁ => TInv enc KP s₀ c c s₁ ∧ s₁.cf = some (decide (N s₀ - c < 8)) := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      arithFlags, State.setFlags, State.setReg, e256, e8, hr8, hr9, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨hst s _ h.kp (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), h.le,
      by simp [hr8], by simp [hr9], by simp [h.r11], by simp [h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h.keep r h1 h2 h3 h4 h5 h6 h7],
      h.rd, h.wr, h.frame, h.data, h.buf, by simp [h.rdx]⟩, Nat.le_refl _, hlt, ?_⟩, ?_⟩
    · simp only [ite_true, Nat.sub_self, slot, Nat.mul_zero, Nat.add_zero, bufOff]; rfl
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega),
        show (8 : BitVec 64).toNat = 8 from rfl]
  refine WP.seq (WP.mono st₁ fun s₁ ⟨h₁, cf₁⟩ => ?_)
  -- Eight blocks, if as many are left.
  have st₂ : WP isa (.ite .b (.block []) (tail8 f)) s₁ fun s₂ => ∃ c', N s₀ - c' < 8 ∧ TInv enc KP s₀ c c' s₂ := by
    refine WP.ite (decide (N s₀ - c < 8)) (by simp [eval, cf₁]) (fun hb => ?_) (fun hb => ?_)
    · exact WP.block_nil ⟨c, by simpa using hb, h₁⟩
    · have hb' : c + 8 ≤ N s₀ := by simp at hb; omega
      exact WP.mono (tbody_ok hp hst hf regs8 8 (.inl ⟨rfl, rfl⟩) hb' h₁)
        fun s' ⟨h', _⟩ => ⟨c + 8, by omega, h'⟩
  refine WP.seq (WP.mono st₂ fun s₂ ⟨c', hc', h₂⟩ => ?_)
  -- `test r9, r9`.
  have hr9₂ := h₂.g.r9
  have hle₂ := h₂.g.le
  have st₃ : WP isa (.block [.alu .test .r9 (.reg .r9)]) s₂
      fun s₃ => TInv enc KP s₀ c c' s₃ ∧ s₃.zf = some (decide (N s₀ - c' = 0)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hr9₂,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨hst s₂ _ h₂.g.kp rfl rfl rfl rfl rfl rfl (Frame.refl _ _), h₂.g.le, h₂.g.r8, h₂.g.r9, h₂.g.r11,
      h₂.g.r10, h₂.g.keep, h₂.g.rd, h₂.g.wr, h₂.g.frame, h₂.g.data, h₂.g.buf, h₂.g.rdx⟩, h₂.bc, h₂.lt, h₂.rax⟩, ?_⟩
    simp only [arithFlags, State.setFlags, BitVec.and_self]
    rw [Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (k := N s₀ - c') (by omega)]
  refine WP.seq (WP.mono st₃ fun s₃ ⟨h₃, zf₃⟩ => ?_)
  -- One block at a time.
  refine WP.ite (decide (N s₀ - c' = 0)) (by simp [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    exact WP.block_nil (by rw [show N s₀ = c' by omega]; exact h₃)
  · simp at hz
    let I : Nat → State → Prop := fun m t => ∃ d, m = N s₀ - d ∧ d < N s₀ ∧ TInv enc KP s₀ c d t
    have hstep : ∀ m t, I m t → WP isa (tail1 f) t (fun t' =>
        (eval .ne t' = some false ∧ TInv enc KP s₀ c (N s₀) t') ∨
        (eval .ne t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨d, rfl, hd, hI⟩
      refine WP.mono (tbody_ok hp hst hf [.xmm0] 1 (.inr ⟨rfl, rfl⟩) (by omega) hI) fun t' ⟨hI', zf'⟩ => ?_
      by_cases hz' : N s₀ - (d + 1) = 0
      · exact .inl ⟨by simp [eval, zf', hz'], by rw [show N s₀ = d + 1 by omega]; exact hI'⟩
      · exact .inr ⟨by simp [eval, zf', hz'], N s₀ - (d + 1), by omega, d + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀ - c') s₃ ⟨c', rfl, by omega, h₃⟩

end VG.Proof.AesXts.X86_64.Vaes
