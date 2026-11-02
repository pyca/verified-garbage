module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack

import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # The framed body restores the caller's saved registers -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

theorem framed_body_ok (M : Mont) {s : State} {B : Addr} {n w c bm b : Nat} {mi : BitVec 64}
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hc : MrCtx (entered s) B (8 * n) w mi c bm) (h : MrDims B (8 * n) w)
    (he : ECtx (entered s).mem B w c) (hodd : c % 2 = 1) (h3 : 3 ≤ c)
    (hX : wv (entered s).mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c)
    (hd : Region.Disjoint ⟨B, 8 * n⟩ ⟨s.gpr .rsp - 112#64, 112⟩)
    (hv : ∀ p ∈ restoreSlots, (entered s).mem.readW
      ((entered s).gpr .rsp + BitVec.ofNat 64 p.2) 64 = word (entered s).mem B (8 * p.1)) :
    WP isa (.frame (.push saved)
      (.frame (.push [.rbp]) (VG.Impl.MillerRabin.X86_64.body M.mm) (.pop .rbp 1))
      (.pop .r11 13)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Proof.MillerRabin.Round.round c b).toNat ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w s.mem t.mem ∧
      Frame [⟨s.gpr .rsp - 112#64, 112⟩, ⟨B, 8 * n⟩] s.mem t.mem := by
  apply round_frames hs
  have hd' : Region.Disjoint ⟨B, 8 * n⟩ ⟨(entered s).gpr .rsp, 112⟩ := by
    rw [entered_rsp]
    exact hd
  refine WP.mono (body_keeps_ok M hc h he hodd h3 hX rfl hd'
    (fun _ hlo hhi => entered_load s hlo hhi) hv) ?_
  rintro t ⟨hr, hbx, h12, h13, h14, h15, hk, hf, hp⟩
  have hsp : t.gpr .rsp = (entered s).gpr .rsp := hk.gpr (by decide)
  refine ⟨hsp, hk.2.2, ?_, ?_, ?_, ?_⟩
  · rw [exited_gpr _ (by decide) (by decide) (by decide)]
    exact hr
  · exact exited_registers hs (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hd.symm) hf hsp hbx h12 h13 h14 h15
  · rw [exited_mem]
    intro i hi hh ha ht
    refine (hp i hi hh ha ht).trans ?_
    apply (entered_frame s hs).bytes (R := ⟨B, 8 * n⟩) ?_ ?_ hi
    · intro r hr'
      simp only [List.mem_singleton] at hr'
      subst hr'
      exact hd
    · change 8 * n ≤ 2 ^ 64
      have := hc.good.scr.nowrap
      omega_arith
  · rw [exited_mem]
    exact ((entered_frame s hs).mono (by simp)).trans (hf.mono (by simp))

end VG.Proof.MillerRabin.X86_64
