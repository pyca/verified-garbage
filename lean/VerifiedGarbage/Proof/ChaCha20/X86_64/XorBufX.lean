module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
public import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ChaCha20 on x86-64: XORing keystream from a buffer, `2 ^ w` bytes at a time

`xorBufXTo w d s` writes the `n` bytes at `S` (in `s`) XORed with the `n`
bytes at `B` (in `rsi`) to the `n` bytes at `D` (in `d`), `n` being in `rdx`
(`xorBufXTo_ok`): `N = 2 ^ w` bytes at a time (16, 32 or 64, through `xmm0`
and `xmm1`, `ymm` or `zmm`) while at least `N` remain (`x_step`, with
`XorBuf`'s invariant), then the rest by `XorBuf.xorBufTo` from
`rdi = D + N ⌊n / N⌋`, `S + N ⌊n / N⌋` and `rsi = B + N ⌊n / N⌋` (`tail_ok`).
Byte `k` of the destination becomes byte `k` of the source XORed with byte
`k` of the buffer, and nothing else in memory changes; among the
general-purpose registers only `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8` and
`s` are written. `xorBufX w d` does it in place (`xorBufX_ok`), its rest by
`XorBuf.xorBuf` from `rdi`, and writes `d` neither.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20.X86_64.XorBufX

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf
open VG.Proof.ChaCha20.X86_64.XorBuf (Inv Sep wMem PostTo inRegions_offset contains_byte xorBufTo_ok)

/-! ## Words of `N` bytes -/

theorem zmm_setZ (t : State) (r : XReg) (l0 l1 l2 l3 : BitVec 128) :
    (t.setZ r l0 l1 l2 l3).zmm r = (l3 ++ l2) ++ (l1 ++ l0) := by
  simp [State.zmm, State.ymm, State.setZ]

theorem halves256 (v u : BitVec 256) :
    (v.extractLsb' 128 128 ^^^ u.extractLsb' 128 128) ++ (v.extractLsb' 0 128 ^^^ u.extractLsb' 0 128) =
      v ^^^ u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega_arith, show 128 + (i - 128) = i by omega_arith]

theorem quarters512 (v u : BitVec 512) :
    ((v.extractLsb' 384 128 ^^^ u.extractLsb' 384 128) ++ (v.extractLsb' 256 128 ^^^ u.extractLsb' 256 128)) ++
      ((v.extractLsb' 128 128 ^^^ u.extractLsb' 128 128) ++ (v.extractLsb' 0 128 ^^^ u.extractLsb' 0 128)) =
      v ^^^ u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb']
  by_cases h₁ : i < 256
  · by_cases h₂ : i < 128
    · simp [h₁, h₂]
    · simp [h₁, h₂, show i - 128 < 128 by omega_arith, show 128 + (i - 128) = i by omega_arith]
  · by_cases h₂ : i - 256 < 128
    · simp [h₁, h₂, show 256 + (i - 256) = i by omega_arith]
    · simp [h₁, h₂, show i - 256 - 128 < 128 by omega_arith, show 384 + (i - 256 - 128) = i by omega_arith]

/-- The data part of `xBodyTo w d s`, from `S + i` and `B + i` to `D + i`, for
`w` = 4, 5 or 6. -/
theorem xDataTo_ok {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) {d sr : Reg} {D S B : Addr} {i : Nat} {s : State}
    (hD : s.gpr d = D) (hS : s.gpr sr = S) (hB : s.gpr .rsi = B) (hrcx : s.gpr .rcx = BitVec.ofNat 64 i)
    (o₁ : InRegions s.wr (D + BitVec.ofNat 64 i) (2 ^ w))
    (i₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) (2 ^ w))
    (i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i) (2 ^ w)) :
    WP isa (.block (xDataTo w d sr)) s fun s' =>
      s'.mem = wMem (2 ^ w) s.mem D S B i ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.ea (idx d) = D + BitVec.ofNat 64 i := by
    simp [State.ea, idx, hD, hrcx]
  have ea₃ : s.ea (idx sr) = S + BitVec.ofNat 64 i := by
    simp [State.ea, idx, hS, hrcx]
  have ea₂ : s.ea (idx .rsi) = B + BitVec.ofNat 64 i := by
    simp [State.ea, idx, hB, hrcx]
  rcases hw with rfl | rfl | rfl <;> simp only [Nat.reducePow] at i₃ i₂ o₁ ⊢ <;> simp only [wMem, Nat.reduceMul]
  · have e₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by simp
    have e₂ : B + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = B + BitVec.ofNat 64 i := by simp
    have e₃ : S + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = S + BitVec.ofNat 64 i := by simp
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, xDataTo, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.ea, State.load128, State.store128, State.setXmm, XOp.exec, reduceXBinOpEval, hD, hS, hB, hrcx, e₁, e₂,
      e₃, i₃, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial⟩
  · apply WP.of_runBlock
    simp only [xDataTo, runBlock_cons, runStep_some, runBlock_nil, exec, ea₁, ea₂, ea₃, State.load256,
      State.store256_eq, i₃, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', ite_true, VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, VOp.exec_ea,
      State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr, State.setV_ea, State.setMem_gpr,
      State.setMem_mem, State.setMem_rd, State.setMem_wr, State.ymm_eq, lane_vbin256, State.lane_setV256,
      reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, reduceVBinOpSse, reduceXBinOpEval, halves256]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · apply WP.of_runBlock
    simp only [xDataTo, runBlock_cons, runStep_some, runBlock_nil, exec, ea₁, ea₂, ea₃, State.load512,
      State.store512_eq, i₃, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', ite_true, ZOp.exec_gpr, ZOp.exec_mem, ZOp.exec_rd, ZOp.exec_wr, ZOp.exec_ea,
      State.setZ_gpr, State.setZ_mem, State.setZ_rd, State.setZ_wr, State.setZ_ea, State.setMem_gpr,
      State.setMem_mem, State.setMem_rd, State.setMem_wr]
    refine ⟨?_, trivial, trivial, trivial⟩
    simp only [ZOp.exec, zmm_setZ, State.zlane_setZ _ _ _ _ _ _ _ (show 0 < 4 by decide),
      State.zlane_setZ _ _ _ _ _ _ _ (show 1 < 4 by decide), State.zlane_setZ _ _ _ _ _ _ _ (show 2 < 4 by decide),
      State.zlane_setZ _ _ _ _ _ _ _ (show 3 < 4 by decide), pick4, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reduceEqDiff, ZBinOp.sse, reduceXBinOpEval, quarters512]

/-! ## The loop -/

section
variable {w : Nat} {d sr : Reg} (hdx : d ≠ .rax ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx)
  (hsx : sr ≠ .rax ∧ sr ≠ .rcx ∧ sr ≠ .rsi ∧ sr ≠ .rdx) {D S B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loop runs: `i` bytes done, of the `n` at `S`. -/
structure Regs (d sr : Reg) (D S B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.gpr d = D
  rs : s.gpr sr = S
  rb : s.gpr .rsi = B
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₀.gpr r

theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem pow_cases {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) : 16 ≤ 2 ^ w ∧ 2 ^ w ≤ 64 := by
  rcases hw with rfl | rfl | rfl <;> decide

theorem seW {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ w)) = BitVec.ofNat 64 (2 ^ w) := by
  rcases hw with rfl | rfl | rfl <;> decide

include hdx hsx in
theorem x_step (hw : w = 4 ∨ w = 5 ∨ w = 6) (hs : Sep D S B n)
    (hwr : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n) (hr : InRegions (s₀.rd ++ s₀.wr) B n)
    {j : Nat} (hj : j < n / 2 ^ w)
    {s : State} (hI : Inv D S B n s₀ (2 ^ w * j) s) (hR : Regs d sr D S B n s₀ (2 ^ w * j) s)
    (hax : s.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w - j)) :
    WP isa (.block (xBodyTo w d sr)) s fun s' =>
      Inv D S B n s₀ (2 ^ w * (j + 1)) s' ∧ Regs d sr D S B n s₀ (2 ^ w * (j + 1)) s' ∧
        s'.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w - (j + 1)) ∧
        s'.zf = some (decide (n / 2 ^ w - (j + 1) = 0)) := by
  have hn := hs.hn
  have hp := pow_cases hw
  have hq' : n / 2 ^ w ≤ n := Nat.div_le_self _ _
  have hi : 2 ^ w * j + 2 ^ w ≤ n := by
    have := Nat.mul_le_of_le_div (2 ^ w) (j + 1) n (by omega_arith)
    rw [Nat.mul_comm] at this; rw [Nat.mul_succ] at this; omega_arith
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 (2 ^ w * j)) (2 ^ w) := by
    rw [hI.wr]; exact inRegions_offset hwr hi
  have i₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (2 ^ w * j)) (2 ^ w) := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hrs hi
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (2 ^ w * j)) (2 ^ w) := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  have eW : 2 ^ w * (j + 1) = 2 ^ w * j + 2 ^ w := Nat.mul_succ _ _
  refine WP.block_append (WP.mono (xDataTo_ok hw hR.rd hR.rs hR.rb hR.rcx o₁ i₃ i₂)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se1, seW hw, g₁,
    hR.rcx, hax, reduceCtorEq, ↓reduceIte]
  refine ⟨by rw [eW]; exact hI.wstep hp.2 hs hi m₁ rd₁ wr₁,
    ⟨by simp [hdx.1, hdx.2.1, hR.rd], by simp [hsx.1, hsx.2.1, hR.rs], by simp [hR.rb], by simp [hR.rdx],
    by simp [eW, BitVec.ofNat_add],
    fun r h₁ h₂ => by simp [h₁, h₂, hR.keep r h₁ h₂]⟩, ?_, ?_⟩
  · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

include hdx hsx in
/-- The prologue and the loop: `N ⌊n / N⌋` bytes done. -/
theorem xloop_ok (hw : w = 4 ∨ w = 5 ∨ w = 6) (hs : Sep D S B n)
    (hD : s₀.gpr d = D) (hS : s₀.gpr sr = S) (hB : s₀.gpr .rsi = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hwr : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n) (hr : InRegions (s₀.rd ++ s₀.wr) B n)
    {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ s, Inv D S B n s₀ (2 ^ w * (n / 2 ^ w)) s → Regs d sr D S B n s₀ (2 ^ w * (n / 2 ^ w)) s →
      WP isa rest s Q) :
    WP isa (.seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax w])
      (.seq (.ite .e (.block []) (.loop (.block (xBodyTo w d sr)) .ne)) rest)) s₀ Q := by
  have hn := hs.hn
  have hp := pow_cases hw
  have hq' : n / 2 ^ w ≤ n := Nat.div_le_self _ _
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax w]) s₀
      fun s => Inv D S B n s₀ 0 s ∧ Regs d sr D S B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w) ∧
        s.zf = some (decide (n / 2 ^ w = 0)) := by
    have hc : 1 ≤ w ∧ w ≤ 63 := by omega_arith
    have h1 : w ≠ 1 := by omega_arith
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx, hc, h1, and_true, ite_true, ite_false]
    have hs : BitVec.ofNat 64 n >>> w = BitVec.ofNat 64 (n / 2 ^ w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
    refine ⟨⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩, ⟨by simp [hdx.1, hdx.2.1, hD], by simp [hsx.1, hsx.2.1, hS], by simp [hB],
      by simp [hrdx], rfl, fun r h₁ h₂ => by simp [h₁, h₂]⟩, by simp [hs], ?_⟩
    simp only [hs]
    rw [← Offset.ofNat_sub_ofNat_beq (x := n / 2 ^ w) (y := 0) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)
      (by decide)]
    simp
  refine WP.seq (WP.mono h₁ fun s₁ ⟨hI, hR, hax, hz⟩ => WP.seq ?_)
  refine WP.mono (Q := fun s' => Inv D S B n s₀ (2 ^ w * (n / 2 ^ w)) s' ∧
    Regs d sr D S B n s₀ (2 ^ w * (n / 2 ^ w)) s') ?_ fun s₂ ⟨hI₂, hR₂⟩ => hrest s₂ hI₂ hR₂
  refine WP.ite (decide ((n / 2 ^ w) = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · have : (n / 2 ^ w) = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [this]; exact hI, by rw [this]; exact hR⟩
  · have hq : 0 < (n / 2 ^ w) := Nat.pos_of_ne_zero (by simpa using h0)
    refine WP.loop (M := isa) (body := .block (xBodyTo w d sr)) (c := .ne)
      (fun (k : Nat) (u : State) => ∃ j, k = (n / 2 ^ w) - j ∧ j < (n / 2 ^ w) ∧ Inv D S B n s₀ (2 ^ w * j) u ∧
        Regs d sr D S B n s₀ (2 ^ w * j) u ∧ u.gpr .rax = BitVec.ofNat 64 ((n / 2 ^ w) - j)) ?_ ((n / 2 ^ w) - 0) _
      ⟨0, rfl, hq, hI, hR, by rw [hax, Nat.sub_zero]⟩
    rintro k u ⟨j, rfl, hj, hIu, hRu, haxu⟩
    refine WP.mono (x_step hdx hsx hw hs hwr hrs hr hj hIu hRu haxu) fun u' ⟨hI', hR', hax', hz'⟩ => ?_
    by_cases he : j + 1 = (n / 2 ^ w)
    · left
      refine ⟨by simp [eval, hz']; omega_arith, by rw [← he]; exact hI', by rw [← he]; exact hR'⟩
    · right
      exact ⟨by simp [eval, hz']; omega_arith, (n / 2 ^ w) - (j + 1), by omega_arith, j + 1, rfl, by omega_arith,
        hI', hR', hax'⟩

end

/-! ## The rest -/

/-- The rest, from `rdi = D + q`, `S + q` (in `sr'`) and `rsi = B + q`, by
`XorBuf.xorBufTo`, with `q` bytes done: then all `n` are done. -/
theorem tail_ok {sr' : Reg} (hsx : sr' ≠ .rax ∧ sr' ≠ .r8 ∧ sr' ≠ .rcx) {D S B : Addr} {n q : Nat}
    {s₀ s₂ s₃ : State} (hs : Sep D S B n) (hq : q ≤ n)
    (hwr : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n) (hr : InRegions (s₀.rd ++ s₀.wr) B n)
    (hI : Inv D S B n s₀ q s₂) (hrdi : s₃.gpr .rdi = D + BitVec.ofNat 64 q)
    (hS : s₃.gpr sr' = S + BitVec.ofNat 64 q) (hB : s₃.gpr .rsi = B + BitVec.ofNat 64 q)
    (hrdx : s₃.gpr .rdx = BitVec.ofNat 64 (n - q)) (hm : s₃.mem = s₂.mem) (hrd : s₃.rd = s₂.rd)
    (hwr₃ : s₃.wr = s₂.wr) :
    WP isa (xorBufTo .rdi sr' .rsi) s₃ fun s =>
      (∀ k < n, s.mem (D + BitVec.ofNat 64 k) = s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)) ∧
      Frame [⟨D, n⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₃.gpr r) := by
  have hn := hs.hn
  have hsub : ∀ {P : Addr}, Region.Sub ⟨P + BitVec.ofNat 64 q, n - q⟩ ⟨P, n⟩ :=
    Offset.sub_base _ (by omega_arith)
  have hs' : Sep (D + BitVec.ofNat 64 q) (S + BitVec.ofNat 64 q) (B + BitVec.ofNat 64 q) (n - q) :=
    ⟨(hs.db.sub_left hsub).sub_right hsub,
      hs.alias.imp (fun h => by rw [h]) fun h => (h.sub_left hsub).sub_right hsub, by omega_arith⟩
  refine WP.mono (xorBufTo_ok (d := .rdi) (b := .rsi) (by decide) hsx (by decide) hrdi hS hB hrdx hs'
    (by rw [hwr₃, hI.wr]; exact inRegions_offset hwr (by omega_arith))
    (by rw [hrd, hwr₃, hI.rd, hI.wr]; exact inRegions_offset hrs (by omega_arith))
    (by rw [hrd, hwr₃, hI.rd, hI.wr]; exact inRegions_offset hr (by omega_arith))) fun s' hp' => ?_
  refine ⟨fun k hk => ?_, ?_, by rw [hp'.rd, hrd, hI.rd], by rw [hp'.wr, hwr₃, hI.wr], hp'.keep⟩
  · by_cases hk' : k < q
    · -- Done by the loop: outside the rest.
      rw [hp'.frame (D + BitVec.ofNat 64 k) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]
        rw [Offset.sub_toNat' D (by omega_arith) (by omega_arith)]
        split <;> omega_arith), hm, hI.data k hk, ite_eq_left hk']
    · have e : ∀ {P : Addr}, P + BitVec.ofNat 64 k =
          P + BitVec.ofNat 64 q + BitVec.ofNat 64 (k - q) := by
        intro P; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega_arith)]
      rw [e, e (P := S), e (P := B), hp'.data (k - q) (by omega_arith), ← e (P := S), ← e (P := B), hm,
        hI.src hs (by omega_arith) hk, hI.buf hs hk]
  · have f₂ := hI.frame
    rw [← hm] at f₂
    exact f₂.trans (hp'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩)

/-! ## The whole -/

/-- What `xorBufXTo w d s` does: byte `k < n` of the destination byte `k` of
the source XORed with byte `k` of the buffer, the rest of memory unchanged,
and the registers but `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8` and `s`. -/
structure XPostTo (sr : Reg) (D S B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ sr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBufXTo_ok {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) {d sr : Reg}
    (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
    (hsx : sr ≠ .rax ∧ sr ≠ .r8 ∧ sr ≠ .rcx ∧ sr ≠ .rsi ∧ sr ≠ .rdx ∧ sr ≠ .rdi)
    {D S B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hS : s₀.gpr sr = S) (hB : s₀.gpr .rsi = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hs : Sep D S B n) (hwr : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n)
    (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBufXTo w d sr) s₀ (XPostTo sr D S B n s₀) := by
  have hn := hs.hn
  refine xloop_ok ⟨hdx.1, hdx.2.2.1, hdx.2.2.2.1, hdx.2.2.2.2.1⟩ ⟨hsx.1, hsx.2.2.1, hsx.2.2.2.1, hsx.2.2.2.2.1⟩
    hw hs hD hS hB hrdx hwr hrs hr fun s₂ hI₂ hR₂ => ?_
  have hq : 2 ^ w * (n / 2 ^ w) ≤ n := Nat.mul_div_le n (2 ^ w)
  have h₃ : WP isa (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add sr (.reg .rcx),
      .alu .add .rsi (.reg .rcx), .alu .sub .rdx (.reg .rcx)]) s₂ fun s =>
        s.gpr .rdi = D + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr sr = S + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rsi = B + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rdx = BitVec.ofNat 64 (n - 2 ^ w * (n / 2 ^ w)) ∧
        (∀ r, r ≠ .rdi → r ≠ sr → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₂.gpr r) ∧ s.mem = s₂.mem ∧
        s.rd = s₂.rd ∧ s.wr = s₂.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
      State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', reduceCtorEq, ↓reduceIte, hR₂.rd, hR₂.rs, hR₂.rb, hR₂.rcx, hR₂.rdx,
      hsx.2.2.2.2.2, hsx.2.2.2.2.2.symm, hsx.2.2.2.1, hsx.2.2.2.1.symm, hsx.2.2.1, hsx.2.2.2.2.1,
      hsx.2.2.2.2.1.symm, hsx.2.2.1.symm, hdx.2.2.1]
    refine ⟨by simp, by simp, by simp,
      ?_, fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄], trivial, trivial, trivial⟩
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨rdi₃, rs₃, rsi₃, rdx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  refine WP.mono (tail_ok ⟨hsx.1, hsx.2.1, hsx.2.2.1⟩ hs hq hwr hrs hr hI₂ rdi₃ rs₃ rsi₃ rdx₃ m₃ rd₃ wr₃)
    fun s' ⟨hdata, hf, hrd', hwr', hk⟩ => ⟨hdata, hf, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, hrd', hwr'⟩
  rw [hk r h₁ h₂ h₃, g₃ r h₆ h₇ h₅ h₄, hR₂.keep r h₁ h₃]

/-- What `xorBufX w d` does: `XPostTo` in place, `d` kept. -/
structure XPost (D B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (D + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBufX_ok {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) {d : Reg}
    (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
    {D B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hB : s₀.gpr .rsi = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hwr : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBufX w d) s₀ (XPost D B n s₀) := by
  have hs : Sep D D B n := XorBuf.Sep.self hd hn
  have hrs : InRegions (s₀.rd ++ s₀.wr) D n := let ⟨r, hr', hc⟩ := hwr; ⟨r, List.mem_append_right _ hr', hc⟩
  have hd' : d ≠ .rax ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx := ⟨hdx.1, hdx.2.2.1, hdx.2.2.2.1, hdx.2.2.2.2.1⟩
  refine xloop_ok hd' hd' hw hs hD hD hB hrdx hwr hrs hr fun s₂ hI₂ hR₂ => ?_
  have hq : 2 ^ w * (n / 2 ^ w) ≤ n := Nat.mul_div_le n (2 ^ w)
  -- The rest from `D + Nq` and `B + Nq`.
  have h₃ : WP isa (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add .rsi (.reg .rcx),
      .alu .sub .rdx (.reg .rcx)]) s₂ fun s => s.gpr .rdi = D + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rsi = B + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rdx = BitVec.ofNat 64 (n - 2 ^ w * (n / 2 ^ w)) ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₂.gpr r) ∧ s.mem = s₂.mem ∧
        s.rd = s₂.rd ∧ s.wr = s₂.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
      State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', reduceCtorEq, ↓reduceIte, hR₂.rd, hR₂.rb, hR₂.rcx, hR₂.rdx]
    refine ⟨by simp [hdx.2.2.1], by simp, ?_, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial,
      trivial⟩
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨rdi₃, rsi₃, rdx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  refine WP.mono (tail_ok (sr' := .rdi) (by decide) hs hq hwr hrs hr hI₂ rdi₃ rdi₃ rsi₃ rdx₃ m₃ rd₃ wr₃)
    fun s' ⟨hdata, hf, hrd', hwr', hk⟩ => ⟨hdata, hf, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, hrd', hwr'⟩
  rw [hk r h₁ h₂ h₃, g₃ r h₆ h₅ h₄, hR₂.keep r h₁ h₃]

end VG.Proof.ChaCha20.X86_64.XorBufX
