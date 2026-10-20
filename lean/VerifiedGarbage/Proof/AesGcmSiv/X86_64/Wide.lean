module
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev

import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV on x86-64: loops four blocks at a time

Untrusted: everything here is checked by Lean. `quadsThenOnes quad one` runs
`quad` (four blocks) while four or more of the `rcx` blocks are left, then
`one` (one block) while any are: `quadsThenOnes_ok` composes the two loops
from invariants `Q` (four at a time, which may say more than `P`) and `P`
(one at a time), indexed by the blocks done, which `cmp` and `test` keep.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (imm)

/-- A property of states that only their flags tell apart. -/
def FlagStable (P : State → Prop) : Prop :=
  ∀ (u : State) (x : BitVec 64) (c o : Bool), P u → P (arithFlags u x c o)

/-- A property of states that only the upper halves of their vector
registers tell apart (which `vzeroupper` clears). -/
def UpperStable (P : State → Prop) : Prop :=
  ∀ u : State, P u → P { u with ymmHi := fun _ => 0, zmmHi := fun _ => 0 }

/-- `cmp rcx, 4` with `k` in `rcx`: CF says whether `k < 4`. -/
theorem cmp8_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .rcx = BitVec.ofNat 64 k) :
    ∃ (x : BitVec 64) (o : Bool), runBlock isa [.alu .cmp .rcx (imm 8)] u =
      some (arithFlags u x (decide (k < 8)) o) := by
  have e4 : BitVec.signExtend 64 (BitVec.ofNat 32 8) = BitVec.ofNat 64 8 := by decide
  refine ⟨BitVec.ofNat 64 k - BitVec.ofNat 64 8,
    subOverflow (BitVec.ofNat 64 k) (BitVec.ofNat 64 8) (BitVec.ofNat 64 k - BitVec.ofNat 64 8), ?_⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, imm, h, Option.bind_some]
  rw [e4]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- `test rcx, rcx` with `k` in `rcx`: ZF says whether `k = 0`. -/
theorem test0_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .rcx = BitVec.ofNat 64 k) :
    runBlock isa [.alu .test .rcx (.reg .rcx)] u =
      some (arithFlags u (BitVec.ofNat 64 k) false false) ∧
      (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  refine ⟨?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some, h,
      BitVec.and_self]
  · by_cases hk0 : k = 0
    · subst hk0; rfl
    · have : BitVec.ofNat 64 k ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
        exact hk0 this
      rw [beq_eq_false_iff_ne.mpr this, decide_eq_false hk0]

/-- The two loops: four blocks at a time while four are left (`Q`, after
`pre`), then one at a time (`P`, from any block before the last). -/
theorem quadsThenOnes_ok {pre quad one : List Instr} {c : Nat} (hc : c < 2 ^ 63) (hc1 : 1 ≤ c)
    (P Q : Nat → State → Prop) (hP : ∀ k, FlagStable (P k)) (hPz : ∀ k, UpperStable (P k))
    (hQP : ∀ k u, Q k u → P k u)
    (hrcx : ∀ k u, P k u → u.gpr .rcx = BitVec.ofNat 64 (c - k))
    (hpre : ∀ u, P 0 u → WP isa (.block pre) u fun u' => Q 0 u' ∧ u'.gpr .rcx = u.gpr .rcx)
    (hquad : ∀ k, k + 4 ≤ c → ∀ u, Q k u → WP isa (.block quad) u fun u' =>
      Q (k + 4) u' ∧ u'.cf = some (decide (c - (k + 4) < 4)))
    (hone : ∀ k, k < c → ∀ u, P k u → WP isa (.loop (.block one) .ne) u (P c))
    {u : State} (h₀ : P 0 u) :
    WP isa (quadsThenOnes pre quad one) u (P c) := by
  unfold quadsThenOnes
  obtain ⟨x, o, run₁⟩ := cmp8_run u (k := c) (by omega) (by rw [hrcx 0 u h₀, Nat.sub_zero])
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  have hP₁ := hP 0 u x (decide (c < 8)) o h₀
  -- Below eight blocks, one at a time from block 0.
  refine WP.ite (decide (c < 8)) rfl (fun _ => hone 0 (by omega) _ hP₁) (fun h8 => ?_)
  have h8' : ¬ c < 8 := by simpa using h8
  refine WP.seq (WP.mono (hpre _ hP₁) fun u₁ ⟨hq₁, _⟩ => ?_)
  -- The quads, from block 0: after them, `k` blocks done with `c - k < 4`.
  have lp : WP isa (.loop (.block quad) .ae) u₁ fun v => ∃ k, k ≤ c ∧ c - k < 4 ∧ Q k v := by
    refine WP.loop (M := isa) (body := .block quad) (c := .ae)
      (fun (m : Nat) (v : State) => ∃ k, m = c - k ∧ k + 4 ≤ c ∧ Q k v) ?_ (c - 0) u₁
      ⟨0, rfl, by omega, hq₁⟩
    rintro m v ⟨k, rfl, hk, hv⟩
    refine WP.mono (hquad k hk v hv) fun v' ⟨hv', hcf'⟩ => ?_
    have ev : isa.eval .ae v' = some !(decide (c - (k + 4) < 4)) := by
      show v'.cf.map (!·) = _; rw [hcf']; rfl
    by_cases hlt : c - (k + 4) < 4
    · left
      exact ⟨by rw [ev, decide_eq_true hlt]; rfl, k + 4, hk, hlt, hv'⟩
    · right
      exact ⟨by rw [ev, decide_eq_false hlt]; rfl, c - (k + 4), by omega, k + 4, rfl, by omega, hv'⟩
  refine WP.seq (WP.mono lp fun v ⟨k, hkc, hk4, hv⟩ => ?_)
  refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
  have hP₂ := hPz k _ (hQP k v hv)
  obtain ⟨run₂, hy⟩ := test0_run _ (k := c - k) (by omega) (hrcx k _ hP₂)
  refine WP.seq (WP.of_runBlock ⟨_, run₂, ?_⟩)
  have hP₃ := hP k _ (BitVec.ofNat 64 (c - k)) false false hP₂
  refine WP.ite (decide (c - k = 0)) (by rw [← hy]; rfl) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have : k = c := by simp at h0; omega
    subst this; exact hP₃
  · exact hone k (by simp at h0; omega) _ hP₃

/-! ## Two blocks at a time on 256-bit registers -/

theorem ea_atd (s : State) (b : Reg) (d : Nat) :
    s.ea (Impl.AesGcm.X86_64.at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 ((d : Nat) : Int) = _
  rw [BitVec.ofInt_natCast]

/-- Lane `l` of a 32-byte load. -/
theorem load256_lane (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    (m.readW a 256).extractLsb' (128 * l) 128 = m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using Proof.Aes.X86_64.Vaes.load256_lo m a
  · simpa using Proof.Aes.X86_64.Vaes.load256_hi m a

/-- Lane `l` of a register's 256 bits. -/
theorem ymm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (128 * l) 128 = s.lane r l := by
  rw [State.ymm_eq]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact Proof.Aes.X86_64.Vaes.extract_lo _ _
  · exact Proof.Aes.X86_64.Vaes.extract_hi _ _

/-- Lane `l` of a 32-byte write, read back. -/
theorem readW_lane256 (m : Mem) (q : Addr) (v : BitVec 256) {l : Nat} (hl : l < 2) :
    (m.writeW q v).readW (q + BitVec.ofNat 64 (16 * l)) 128 = v.extractLsb' (128 * l) 128 := by
  have e := readW_writeW_inside m q v (k := 16 * l) (n := 16) (by omega) (by decide)
  rwa [show 8 * (16 * l) = 128 * l by omega] at e

/-- The two blocks at `rsi + d`, each byte-reversed (`ymm1` holding the mask
in each lane), stored at `rdi + d`. -/
theorem rev2_ok (d : Nat) (s : State) {S P : Addr} (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P)
    (hm : ∀ l < 2, s.lane .xmm1 l = Proof.Gcm.X86_64.revMask)
    (hr : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 32) (hw : InRegions s.wr (P + BitVec.ofNat 64 d) 32) :
    WP isa (.block (rev2 d)) s fun s' =>
      (∃ v : BitVec 256, s'.mem = s.mem.writeW (P + BitVec.ofNat 64 d) v ∧ ∀ l < 2,
        v.extractLsb' (128 * l) 128 = XBinOp.eval .pshufb
          (s.mem.readW (S + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128) Proof.Gcm.X86_64.revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ l < 2, s'.lane .xmm1 l = s.lane .xmm1 l) := by
  let v := s.mem.readW (S + BitVec.ofNat 64 d) 256
  let s₁ := s.setV .l256 .xmm0 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vbin .vpshufb .l256 .xmm0 .xmm0 .xmm1).exec s₁
  rw [rev2, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_atd, hsi, hr, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (Impl.AesGcm.X86_64.at_ .rdi d) .xmm0) s₂ =
      some (s₂.setMem (s.mem.writeW (P + BitVec.ofNat 64 d) (s₂.ymm .xmm0))) := by
    simp only [isa, exec, State.store256_eq, ea_atd, s₂, s₁, VOp.exec_gpr, State.setV_gpr, VOp.exec_wr,
      State.setV_wr, VOp.exec_mem, State.setV_mem, hdi, hw, ite_true]
  refine ⟨_, hst, WP.block_nil ⟨⟨_, rfl, fun l hl => ?_⟩, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁],
    fun l hl => ?_⟩⟩
  · rw [ymm_lane _ _ hl]
    simp only [s₂, lane_vbin256, ite_true, VBinOp.sse, s₁, State.lane_setV256,
      show (XReg.xmm1 = .xmm0) = False by decide, ite_false, hm l hl]
    rw [← load256_lane _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · simp [s₂, s₁, lane_vbin256, State.lane_setV256]

/-- The four blocks at `rsi` (`S`), each byte-reversed (`ymm1` holding the
mask in each lane), stored at `rdi` (`P`), outside them: GHASH reads each as
the block's 128-bit little-endian value. -/
theorem revY_ok (s : State) {S P : Addr} (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P)
    (hm : ∀ l < 2, s.lane .xmm1 l = Proof.Gcm.X86_64.revMask)
    (hr : InRegions (s.rd ++ s.wr) S 32) (hw : InRegions s.wr P 32)
    (hr' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 32) 32) (hw' : InRegions s.wr (P + BitVec.ofNat 64 32) 32)
    (hSP : Region.Disjoint ⟨S, 64⟩ ⟨P, 64⟩) :
    WP isa (.block (rev2 0 ++ rev2 32)) s fun s' =>
      Frame [⟨P, 64⟩] s.mem s'.mem ∧
      (∀ l < 4, Spec.Gcm.blockAt s'.mem (P + BitVec.ofNat 64 (16 * l)) =
        s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ l < 2, s'.lane .xmm1 l = s.lane .xmm1 l) := by
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  rw [WP.block_append_iff]
  refine WP.mono (rev2_ok 0 s (S := S) (P := P) hsi hdi hm (by rw [e0]; exact hr) (by rw [e0]; exact hw))
    fun s₁ ⟨⟨v₁, m₁, h₁⟩, g₁, rd₁, wr₁, k₁⟩ => ?_
  have hm₁ : ∀ l < 2, s₁.lane .xmm1 l = Proof.Gcm.X86_64.revMask := fun l hl => by rw [k₁ l hl, hm l hl]
  refine WP.mono (rev2_ok 32 s₁ (S := S) (P := P) (by rw [g₁, hsi]) (by rw [g₁, hdi]) hm₁ (by rw [rd₁, wr₁]; exact hr')
    (by rw [wr₁]; exact hw')) fun s₂ ⟨⟨v₂, m₂, h₂⟩, g₂, rd₂, wr₂, k₂⟩ => ?_
  rw [e0] at m₁ h₁
  have c0 : (⟨P, 64⟩ : Region).Contains P 32 := by
    have := Offset.contains_base P (d := 0) (n := 32) (k := 64) (by decide) (by omega)
    rwa [e0] at this
  -- The source is outside the first store.
  have srcS : ∀ l < 2, s₁.mem.readW (S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 =
      s.mem.readW (S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [m₁, Offset.add_add]
    exact Mem.readW_writeW_sep (hSP.sep (Offset.contains_base S (by omega) (by omega))
      c0) (by decide)
  refine ⟨?_, fun l hl => ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun l hl => by rw [k₂ l hl, k₁ l hl]⟩
  · rw [m₂, m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      c0).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base P (show 32 + 256 / 8 ≤ 64 by decide) (by omega))
  · rw [Proof.Gcm.X86_64.blockAt_eq]
    by_cases hl2 : l < 2
    · rw [m₂, Mem.readW_writeW_sep (Offset.disjoint P (.inl (by omega)) (by omega) (by omega) |>.sep
          (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), m₁, readW_lane256 _ _ _ hl2,
        h₁ l hl2, Proof.Gcm.X86_64.pshufb_rev_rev]
    · have e : P + BitVec.ofNat 64 (16 * l) = P + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * (l - 2)) := by
        rw [Offset.add_add]; congr 2; omega
      have eS : S + BitVec.ofNat 64 (16 * l) = S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * (l - 2)) := by
        rw [Offset.add_add]; congr 2; omega
      rw [e, m₂, readW_lane256 _ _ _ (by omega), h₂ (l - 2) (by omega), Proof.Gcm.X86_64.pshufb_rev_rev, eS,
        srcS (l - 2) (by omega)]

/-- The two keystream blocks at `rsi + d` XORed into the two data blocks at
`r12 + d`. -/
theorem xor2_ok (d : Nat) (s : State) {S Q : Addr} (hsi : s.gpr .rsi = S) (h12 : s.gpr .r12 = Q)
    (hr : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 32) (hw : InRegions s.wr (Q + BitVec.ofNat 64 d) 32) :
    WP isa (.block (xor2 d)) s fun s' =>
      (∃ v : BitVec 256, s'.mem = s.mem.writeW (Q + BitVec.ofNat 64 d) v ∧ ∀ l < 2,
        v.extractLsb' (128 * l) 128 = s.mem.readW (Q + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128 ^^^
          s.mem.readW (S + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' := Proof.Aes.X86_64.AesNi.inRegions_wr hw
  let vS := s.mem.readW (S + BitVec.ofNat 64 d) 256
  let vQ := s.mem.readW (Q + BitVec.ofNat 64 d) 256
  let s₁ := s.setV .l256 .xmm1 (vS.extractLsb' 0 128) (vS.extractLsb' 128 128)
  let s₂ := s₁.setV .l256 .xmm0 (vQ.extractLsb' 0 128) (vQ.extractLsb' 128 128)
  let s₃ := (VOp.vbin .vpxor .l256 .xmm1 .xmm1 .xmm0).exec s₂
  rw [xor2, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_atd, hsi, hr, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by
    simp only [isa, exec, State.load256, ea_atd, s₁, State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem,
      h12, hw', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (Impl.AesGcm.X86_64.at_ .r12 d) .xmm1) s₃ =
      some (s₃.setMem (s.mem.writeW (Q + BitVec.ofNat 64 d) (s₃.ymm .xmm1))) := by
    simp only [isa, exec, State.store256_eq, ea_atd, s₃, s₂, s₁, VOp.exec_gpr, State.setV_gpr, VOp.exec_wr,
      State.setV_wr, VOp.exec_mem, State.setV_mem, h12, hw, ite_true]
  refine ⟨_, hst, WP.block_nil ⟨⟨_, rfl, fun l hl => ?_⟩, by simp [s₃, s₂, s₁], by simp [s₃, s₂, s₁],
    by simp [s₃, s₂, s₁]⟩⟩
  rw [ymm_lane _ _ hl]
  simp only [s₃, lane_vbin256, ite_true, VBinOp.sse, s₂, s₁, State.lane_setV256,
    show (XReg.xmm1 = .xmm0) = False by decide, ite_false, ite_true]
  rw [Proof.Aes.X86_64.AesNi.eval_pxor, BitVec.xor_comm, ← load256_lane _ _ hl, ← load256_lane _ _ hl]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

/-- The four keystream blocks at `rsi` (`S`) XORed into the four data blocks
at `r12` (`Q`), outside them. -/
theorem ksY_ok (s : State) {S Q : Addr} (hsi : s.gpr .rsi = S) (h12 : s.gpr .r12 = Q)
    (hr : InRegions (s.rd ++ s.wr) S 32) (hw : InRegions s.wr Q 32)
    (hr' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 32) 32) (hw' : InRegions s.wr (Q + BitVec.ofNat 64 32) 32)
    (hSQ : Region.Disjoint ⟨S, 64⟩ ⟨Q, 64⟩) :
    WP isa (.block (xor2 0 ++ xor2 32)) s fun s' =>
      Frame [⟨Q, 64⟩] s.mem s'.mem ∧
      (∀ l < 4, s'.mem.readW (Q + BitVec.ofNat 64 (16 * l)) 128 =
        s.mem.readW (Q + BitVec.ofNat 64 (16 * l)) 128 ^^^ s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  rw [WP.block_append_iff]
  refine WP.mono (xor2_ok 0 s (S := S) (Q := Q) hsi h12 (by rw [e0]; exact hr) (by rw [e0]; exact hw))
    fun s₁ ⟨⟨v₁, m₁, h₁⟩, g₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (xor2_ok 32 s₁ (S := S) (Q := Q) (by rw [g₁, hsi]) (by rw [g₁, h12]) (by rw [rd₁, wr₁]; exact hr')
    (by rw [wr₁]; exact hw')) fun s₂ ⟨⟨v₂, m₂, h₂⟩, g₂, rd₂, wr₂⟩ => ?_
  simp only [e0] at m₁ h₁
  have c0 : (⟨Q, 64⟩ : Region).Contains Q 32 := by
    have := Offset.contains_base Q (d := 0) (n := 32) (k := 64) (by decide) (by omega)
    rwa [e0] at this
  -- The second pair, read after the first store: the keystream is outside
  -- it, and the data after it.
  have srcS : ∀ l < 2, s₁.mem.readW (S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 =
      s.mem.readW (S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [m₁, Offset.add_add]
    exact Mem.readW_writeW_sep (hSQ.sep (Offset.contains_base S (by omega) (by omega)) c0) (by decide)
  have srcQ : ∀ l < 2, s₁.mem.readW (Q + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 =
      s.mem.readW (Q + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [m₁, Offset.add_add]
    exact Mem.readW_writeW_sep ((Offset.disjoint_base Q (d := 32 + 16 * l) (n := 16) (k := 32) (by omega)
      (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
  refine ⟨?_, fun l hl => ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [m₂, m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base Q (show 32 + 256 / 8 ≤ 64 by decide) (by omega))
  · by_cases hl2 : l < 2
    · rw [m₂, Mem.readW_writeW_sep (Offset.disjoint Q (.inl (by omega)) (by omega) (by omega) |>.sep
          (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), m₁, readW_lane256 _ _ _ hl2,
        h₁ l hl2]
    · have e : Q + BitVec.ofNat 64 (16 * l) = Q + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * (l - 2)) := by
        rw [Offset.add_add]; congr 2; omega
      have eS : S + BitVec.ofNat 64 (16 * l) = S + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * (l - 2)) := by
        rw [Offset.add_add]; congr 2; omega
      rw [e, m₂, readW_lane256 _ _ _ (by omega), h₂ (l - 2) (by omega), srcQ (l - 2) (by omega),
        srcS (l - 2) (by omega), eS]

/-! ## The pointers and the count -/

/-- `add a, 64; add b, 64; sub rcx, 4; cmp rcx, 4` with `k ≥ 4` in `rcx`. -/
theorem adv4_run (u : State) {a b : Reg} (ha : a ≠ .rcx) (hb : b ≠ .rcx) (hab : a ≠ b) {k : Nat} (hk4 : 4 ≤ k)
    (hk : k < 2 ^ 63) (hcx : u.gpr .rcx = BitVec.ofNat 64 k) :
    ∃ u', runBlock isa [.alu .add a (imm 64), .alu .add b (imm 64), .alu .sub .rcx (imm 4),
        .alu .cmp .rcx (imm 4)] u = some u' ∧
      u'.gpr a = u.gpr a + BitVec.ofNat 64 64 ∧ u'.gpr b = u.gpr b + BitVec.ofNat 64 64 ∧
      u'.gpr .rcx = BitVec.ofNat 64 (k - 4) ∧ u'.cf = some (decide (k - 4 < 4)) ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ x l, u'.lane x l = u.lane x l) := by
  have e64 : BitVec.signExtend 64 (BitVec.ofNat 32 64) = BitVec.ofNat 64 64 := by decide
  have e4 : BitVec.signExtend 64 (BitVec.ofNat 32 4) = BitVec.ofNat 64 4 := by decide
  have s4 : BitVec.ofNat 64 k - BitVec.ofNat 64 4 = BitVec.ofNat 64 (k - 4) :=
    Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)
  have hba : b ≠ a := fun h => hab h.symm
  have hcb : Reg.rcx ≠ b := fun h => hb h.symm
  have hca : Reg.rcx ≠ a := fun h => ha h.symm
  refine ⟨_, rfl, ?_⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, imm, e64, e4,
    Option.bind_some, gpr_setReg, gpr_arithFlags, ite_true, ha, hb, hab, hba, hca, hcb, ite_false, hcx, s4,
    cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    BitVec.toNat_ofNat]
  refine ⟨trivial, trivial, trivial, ?_, fun r h₁ h₂ h₃ => by simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃,
    ite_false], trivial, trivial, trivial, fun _ _ => rfl⟩
  rw [Nat.mod_eq_of_lt (by omega : k - 4 < 2 ^ 64)]

/-! ## The mask -/

/-- The byte-reversal mask in both lanes of `ymm1`. -/
theorem revMaskY_ok (s : State) :
    WP isa (.block revMaskY) s fun s' =>
      (∀ l < 2, s'.lane .xmm1 l = Proof.Gcm.X86_64.revMask) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [revMaskY, WP.block_append_iff]
  refine WP.mono (Proof.Gcm.X86_64.Pclmul.const_ok .xmm1 _ s (by decide)) fun s₁ ⟨x₁, O⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, rfl, fun l hl => ?_, fun r h₁ => ?_, O.mem, O.rd, O.wr⟩
  · simp only [isa, exec, VOp.exec, show (1 : BitVec 8).getLsbD 0 = true by decide, ite_true, State.lane_setV256]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]; rw [show s₁.lane .xmm1 0 = s₁.xmm .xmm1 from rfl, x₁]; rfl
    · simp only [show (1 : Nat) ≠ 0 by decide, ite_false]; rw [x₁]; rfl
  · simp only [isa, exec, VOp.exec_gpr, State.setV_gpr]
    exact O.gpr r h₁

end VG.Proof.AesGcmSiv.X86_64
