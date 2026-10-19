module
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.AesXts.X86_64Vaes
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.X86_64.Clmul87
import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Common
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.PrePost
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Spec

/-!
# One-pass XTS-AES on x86-64: the tweaks XORed in, one block per register

The blocks left after the eight-block loop go through 128-bit registers:
`tPreList_ok` loads block register `k` from `r11 + 16 k` and XORs in the
tweak at `rax + 16 k`; `tPostList_ok` XORs it in again and stores it.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr ofInt_natCast)
open VG.Impl.AesXts.X86_64Vaes (tPre tPost)

theorem tPre1_ok (b : XReg) (d : Nat) (s : State)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad b (at_ .r11 d), .vbinLoad .vpxor .l128 b b (at_ .rax d)]) s fun s' =>
      s'.xmm b = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 128 ^^^
        s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm,
    State.load128, ea_at, hd, he, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp [State.setV], by simp [State.setV], by simp [State.setV], by simp [State.setV],
    fun r h => by simp [State.setV, h]⟩
  simp [State.setV, State.lane, VBinOp.sse, XBinOp.eval]

theorem tPost1_ok (b : XReg) (d : Nat) (s : State)
    (hd : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.vbinLoad .vpxor .l128 b b (at_ .rax d), .movdquStore (at_ .r11 d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int))
        (s.xmm b ^^^ s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  let u := s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128
  let s₁ := s.setV .l128 b (VBinOp.vpxor.sse.eval (s.lane b 0) u) 0
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load128, ea_at, he, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₁.setMem (s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) (s₁.xmm b)), by
    simp only [isa, exec, State.store128_eq, ea_at, s₁, State.setV_gpr, State.setV_mem, State.setV_wr, hd,
      ite_true], WP.block_nil ?_⟩
  refine ⟨?_, by simp [s₁], by simp [s₁], by simp [s₁], fun r h => by simp [s₁, State.setV, h]⟩
  simp [s₁, State.setV, State.lane, VBinOp.sse, XBinOp.eval, u]

theorem tPreList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (he : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) :
    WP isa (.block (tPre regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^
          s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd he
    rw [tPre, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (tPre1_ok b (16 * j) s hd0 he0) fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, v₁, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, o₁ r hr.1]

theorem tPostList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hd : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (he : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .r11).toNat + 16 * (j + regs.length) ≤ 2 ^ 64)
    (hsep : ∀ k < regs.length,
      Region.Disjoint ⟨s.gpr .rax + BitVec.ofNat 64 (16 * (j + k)), 16⟩
        ⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩) :
    WP isa (.block (tPost regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * (j + k))) 128 =
          s.xmm regs[k] ^^^ s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hd he hw hsep
    rw [tPost, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (tPost1_ok b (16 * j) s hd0 he0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    have hax : s₁.gpr .rax = s.gpr .rax := by rw [g₁]
    rw [ofInt_natCast] at m₁
    have hblk : Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₁.mem := by
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        simp only [Region.Contains, BitVec.sub_self]; simp)
    have hslot : ∀ k < bs.length,
        s₁.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + 1 + k))) 128 =
          s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + 1 + k))) 128 := by
      intro k hk
      refine hblk.readW (r := ⟨_, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      have := hsep (k + 1) (by omega)
      rw [show j + (k + 1) = j + 1 + k by omega] at this
      exact this.sub_right (Region.sub_prefix (by omega))
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
      (fun k hk => by
        rw [rd₁, wr₁, hax, show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega))
      (by rw [h11]; omega)
      (fun k hk => by
        rw [hax, h11]
        have := hsep (k + 1) (by omega)
        rw [show j + (k + 1) = j + 1 + k by omega] at this
        refine this.sub_right ?_
        intro a ha
        simp only [Region.Contains] at ha ⊢
        rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha ⊢
        have := (a - s.gpr .r11).isLt
        omega)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11, hax] at hb
    rw [h11] at hf
    have hdj : ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .r11).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) hdj (by decide), m₁, Mem.readW_writeW_self s.mem _ 16 _ (by decide)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', x₁ _ hne, hslot k hk']
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .r11).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr
      rw [xs r hr.2, x₁ r hr.1]

end VG.Proof.AesXts.X86_64.Vaes
