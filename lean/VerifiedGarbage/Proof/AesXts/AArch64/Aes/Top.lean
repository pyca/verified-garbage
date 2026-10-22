module

public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Setup
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# One-pass XTS-AES on AArch64: the whole function

`crypt_wp`: `crypt setup B.f` meets the contract of `vg_aes_xts_encrypt` (or
`vg_aes_xts_decrypt`) as `modeAArch64 (xtsMode enc)` states it, but for the
registers it preserves, when `setup` loads the round keys `B` needs
(`KPre`, `KPost`) and `B` computes the cipher (or its inverse) of the
direction: `enter` and `setup` reach `XInv … 0 0` (`setup_ok`), the loops
reach `XInv … N N` (`loops_ok`), and `finish` writes the tweak after the
last block back (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0 modeAArch64 in_rw)
open VG.Proof.Aes.AArch64.Aese (BlockFn bkp bnr bnb bsch)
open VG.Impl.AesXts.AArch64Aes (enter finish crypt)

theorem enter_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block enter) s₀ fun s =>
      s.gpr .x11 = Iv s₀ ∧ s.gpr .x2 = Dp s₀ ∧ s.gpr .x3 = s₀.gpr .x4 ∧ tweakOf s = tw0 s₀ ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hiv := hp.iv_wrap
  have hW : s₀.rd ++ s₀.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hp.rd, hp.wr]; rfl
  rw [enter, WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (by simpa using Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 8) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h2 h3 h11 h14 h15 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp only [tweakOf, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq,
      BitVec.add_zero]
    exact (readW128 _ _).symm
  · simp [State.write, h2, h3, h11, h14, h15]

/-- `enter` and the key setup. -/
theorem setup_ok (B : BlockFn) (enc : Bool) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (enter ++ setup)) s₀ fun s =>
      XInv B enc s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (N s₀ / 8) := by
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp) fun s₁ ⟨x11, x2, x3, t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have hx0 : bkp s₁ = W s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx1 : bnr s₁ = R s₀ := by
    simp only [bnr, R]; rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have kp : KPre s₁ := ⟨fun ho => by
      rw [rd₁, wr₁, hx0, hp.rd]
      exact in_rw (by simp) (Offset.contains_base _ ho (by omega)), by rw [hx1]; exact hp.rounds⟩
  refine WP.mono (hs s₁ kp) fun s₂ k₂ => ?_
  have g : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → r ≠ .x9 → r ≠ .x6 → r ≠ .x7 →
      r ≠ .x13 → s₂.gpr r = s₀.gpr r := fun r h2 h3 h11 h14 h15 h9 h6 h7 h13 => by
    rw [k₂.gpr r h9 h6 h7 h13, g₁ r h2 h3 h11 h14 h15]
  have hsch : bsch s₁ = wK s₀ := by simp only [bsch, wK, hx0, hx1, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [← hsch, ← hx1]; exact k₂.keys
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x2, blk, Nat.mul_zero, BitVec.add_zero]
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x3, Nat.sub_zero]
    exact Proof.AesCbc.AArch64.x4_ofNat s₀
  · exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x11]
  · rw [tweakOf, k₂.gpr _ (by decide) (by decide) (by decide) (by decide),
      k₂.gpr _ (by decide) (by decide) (by decide) (by decide), ← tweakOf, t₁]; rfl
  · rw [k₂.rd, rd₁]
  · rw [k₂.wr, wr₁]
  · rw [k₂.mem, m₁]; exact Frame.refl _ _
  · rw [k₂.mem, m₁]; simp
  · rw [k₂.x13]; simp only [bnb, x3]

theorem getElem_tweaks (t : List Byte) {n k : Nat} (hk : k < n) :
    (Spec.Xts.tweaks t n)[k]'(by rw [AesXts.length_tweaks]; exact hk) = Spec.Xts.next t k := by
  induction n generalizing t k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Spec.Xts.tweaks, List.getElem_cons_succ]; rw [ih _ (by omega), AesXts.next_succ']

/-- The tweak after the last block written back. -/
theorem finish_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {s : State}
    (h : XInv B enc s₀ (N s₀) (N s₀) s) :
    WP isa (.block finish) s fun s' => (modeAArch64 (AesXts.xtsMode enc)).post s₀ s' ∧
      s'.gpr = s.gpr ∧ s'.v = s.v := by
  have hiv := hp.iv_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [finish, WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 0) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 8) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  have fr : Frame [ivR s₀] s.mem ((s.mem.writeW (Iv s₀) (s.gpr .x14)).writeW (Iv s₀ + BitVec.ofNat 64 8)
      (s.gpr .x15)) := Proof.Cmac.frame_store2 _ _ _
  have hs : Mem.Sep (Iv s₀) (64 / 8) (Iv s₀ + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep (Iv s₀) (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩ <;> simp only [h.x11, BitVec.add_zero]
  · show Spec.Cbc.blocksAt _ (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    have hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      Proof.Cmac.bytesAt_frame16 fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm),
      h.data k hk]
    simp only [hk, ite_true]
  · show bytesAt _ (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
    rw [AesCbc.length_blocksAt, bytesAt_b16, readW128, Mem.readW_writeW_self64,
      Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64, ← tweakOf, h.tw, b16_twW,
      ← iv0_b16]

/-- The whole function, but for the registers it preserves. -/
theorem crypt_wp (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State}
    (h0 : (modeAArch64 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt setup B.f) s₀ ((modeAArch64 (AesXts.xtsMode enc)).post s₀) := by
  have hp := UPre.of h0
  refine WP.seq (WP.mono (setup_ok B enc hs hp) fun s₁ ⟨hI₁, h13⟩ => ?_)
  refine WP.seq (WP.mono (loop8_ok B enc hF hp hI₁ h13) fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  refine WP.seq (WP.mono (loop1_ok B enc hF hp hc hI₂) fun s₃ hI₃ => ?_)
  exact WP.mono (finish_ok B enc hp hI₃) fun _ h => h.1

end VG.Proof.AesXts.AArch64.Aes
