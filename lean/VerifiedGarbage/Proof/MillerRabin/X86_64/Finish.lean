module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Restore
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Restore preserved registers and return the round's secret Boolean -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64

private theorem mask_one (p : Bool) : mask p &&& 1 = BitVec.ofNat 64 p.toNat := by
  cases p <;> decide

theorem restoreAndReturn_ok {s : State} {B S : Addr} {Z w : Nat} {mi : BitVec 64} {p : Bool}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hsp : s.gpr .rsp = S)
    (hp : VG.Proof.Bignum.word s.mem B (8 * kFlag) = mask p)
    (hl : ∀ d ∈ [72, 80, 88, 96, 104], InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8) :
    WP isa (.block restoreAndReturn) s fun t =>
      t.mem = s.mem ∧ t.gpr .rax = BitVec.ofNat 64 p.toNat ∧
      t.gpr .rbx = s.mem.readW (S + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (S + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (S + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (S + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (S + 72#64) 64 ∧ Keep [.rbx, .r12, .r13, .r14, .r15, .rax] s t := by
  have hf : InRegions (s.rd ++ s.wr) (off B (8 * kFlag)) 8 :=
    h.scr.ld (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  refine WP.mono (WP.keep (c := .block restoreAndReturn) [.rbx, .r12, .r13, .r14, .r15, .rax]
    (Q := fun t => t.mem = s.mem ∧ t.gpr .rax = BitVec.ofNat 64 p.toNat ∧
      t.gpr .rbx = s.mem.readW (S + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (S + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (S + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (S + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (S + 72#64) 64) ?_ rfl)
    fun t ⟨⟨hm, hr, hbx, h12, h13, h14, h15⟩, hk⟩ => ⟨hm, hr, hbx, h12, h13, h14, h15, hk⟩
  xrun [restoreAndReturn, State.ea, hsp, hdr, h.rdi, hdrOff, hf, hp, mask_one,
    show BitVec.ofInt 64 72 = 72#64 from rfl, show BitVec.ofInt 64 80 = 80#64 from rfl,
    show BitVec.ofInt 64 88 = 88#64 from rfl, show BitVec.ofInt 64 96 = 96#64 from rfl,
    show BitVec.ofInt 64 104 = 104#64 from rfl,
    hl 72 (by simp), hl 80 (by simp), hl 88 (by simp), hl 96 (by simp), hl 104 (by simp)]

theorem finish_ok {s : State} {B S : Addr} {Z w : Nat} {mi : BitVec 64} {p : Bool}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hsp : s.gpr .rsp = S)
    (hp : VG.Proof.Bignum.word s.mem B (8 * kFlag) = mask p)
    (hd : Region.Disjoint ⟨B, Z⟩ ⟨S, 112⟩)
    (hl : ∀ d, 8 ≤ d → d + 8 ≤ 112 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8) :
    WP isa (.block finish) s fun t =>
      t.mem = restoredMem s.mem B S ∧ t.gpr .rax = BitVec.ofNat 64 p.toNat ∧
      t.gpr .rbx = s.mem.readW (S + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (S + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (S + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (S + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (S + 72#64) 64 ∧ Keep [.r11, .rbx, .r12, .r13, .r14, .r15, .rax] s t := by
  have h256 : 256 ≤ Z := by have := VG.Proof.Bignum.hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  unfold VG.Impl.MillerRabin.X86_64.finish
  rw [WP.block_append_iff]
  refine WP.mono (restoreBookkeeping_ok h.scr h256 h.rdi hsp hd hl) fun u ⟨hm, hk⟩ => ?_
  have hg : Good u B Z w mi := by
    refine ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, ?_, ?_, ?_⟩
    · rw [hm, restored_header _ _ _ (Or.inl (by decide))]; exact h.hdr.hw
    · rw [hm, restored_header _ _ _ (Or.inl (by decide))]; exact h.hdr.hminv
    · intro j hj
      rw [hm, restored_header _ _ _ (Or.inl (by unfold sArr; omega_arith))]
      exact h.hdr.harr j hj
  have hp' : VG.Proof.Bignum.word u.mem B (8 * kFlag) = mask p := by
    rw [hm, restored_header _ _ _ (Or.inr rfl)]
    exact hp
  refine WP.mono (restoreAndReturn_ok hg hZ ((hk.gpr (by decide)).trans hsp) hp' (fun d hd' => by
    rw [hk.2.1, hk.2.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl
    all_goals exact hl _ (by decide) (by decide))) fun t ⟨hm', hr, hbx, h12, h13, h14, h15, k⟩ => ?_
  refine ⟨hm'.trans hm, hr, ?_, ?_, ?_, ?_, ?_, (hk.trans k).mono (by decide)⟩
  all_goals
    first
      | (rw [hbx, hm]; exact restored_stack s.mem h256 hd (by decide))
      | (rw [h12, hm]; exact restored_stack s.mem h256 hd (by decide))
      | (rw [h13, hm]; exact restored_stack s.mem h256 hd (by decide))
      | (rw [h14, hm]; exact restored_stack s.mem h256 hd (by decide))
      | (rw [h15, hm]; exact restored_stack s.mem h256 hd (by decide))

end VG.Proof.MillerRabin.X86_64
