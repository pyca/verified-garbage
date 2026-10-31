module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyCopy
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyTemp
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyStore
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the key-schedule word invariant is independent of key copying and the public ABI.
/-! # POWER8 AES key-schedule word loop -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.KeyWords (W Good good_store W_ge)
open VG.Impl.Aes.KeyWords (rc)

def keyGprs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

structure WordInv (base : State) (P S : Addr) (nk i : Nat) (s : State) : Prop where
  bound : nk ≤ i ∧ i ≤ 4*(nk+7)
  keep : Keep keyGprs base s
  ptr10 : s.gpr .r10 = S + BitVec.ofNat 64 (4*(i-nk))
  ptr11 : s.gpr .r11 = S + BitVec.ofNat 64 (4*(i-1))
  index : s.gpr .r12 = BitVec.ofNat 64 (4*(i%nk))
  keylen : s.gpr .r7 = BitVec.ofNat 64 (4*nk)
  left : s.gpr .r4 = BitVec.ofNat 64 (4*(nk+7)-i)
  constant : s.gpr .r6 = (rc ((i-1)/nk+1)).setWidth 64
  good : Good s.mem S (W base.mem P nk) i
  frame : Frame [⟨S, 240⟩] base.mem s.mem

theorem word_step {base s : State} {P S : Addr} {nk i : Nat} (hc : KeyConfig base P S (4*nk))
    (h : WordInv base P S nk i s) (hi : i < 4*(nk+7)) :
    WP isa Impl.Aes.PPC64LE.Crypto.wordBody s (WordInv base P S nk (i+1)) := by
  have h3 : nk = 4 ∨ nk = 6 ∨ nk = 8 := by have := hc.length; omega
  have hn : 0 < nk ∧ nk ≤ 8 := by omega
  have hni := h.bound.1
  have hread : InRegions (s.rd ++ s.wr) (s.gpr .r11) 4 := by
    rw [h.ptr11, h.keep.2.1, h.keep.2.2]
    exact ⟨⟨S, 240⟩, List.mem_append_right _ hc.schedule,
      Offset.contains_base _ (d := 4*(i-1)) (n := 4) (k := 240) (by omega) (by omega)⟩
  rw [Impl.Aes.PPC64LE.Crypto.wordBody]
  refine WP.seq (WP.mono (loadWord_ok .r9 .r11 s (by decide) hread) fun u ⟨hv, he⟩ => ?_)
  have hprev : (u.gpr .r9).setWidth 32 = W base.mem P nk (i-1) := by
    rw [hv, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq, h.ptr11]
    exact h.good _ (by omega)
  refine WP.seq (WP.mono (tempWord_ok u h3 hni hi
    ((he.keep.gpr (by decide)).trans h.index) ((he.keep.gpr (by decide)).trans h.keylen)
    ((he.keep.gpr (by decide)).trans h.constant)) fun v ⟨htemp, hrc, hf⟩ => ?_)
  have hbefore := he.trans hf
  rw [hprev] at htemp
  have hrd : InRegions (v.rd ++ v.wr) (v.gpr .r10) 4 := by
    rw [hbefore.keep.2.1, hbefore.keep.2.2, hbefore.keep.gpr (by decide), h.ptr10, h.keep.2.1, h.keep.2.2]
    exact ⟨⟨S, 240⟩, List.mem_append_right _ hc.schedule,
      Offset.contains_base _ (d := 4*(i-nk)) (n := 4) (k := 240) (by omega) (by omega)⟩
  have haddr : v.gpr .r11 + 4#64 = S + BitVec.ofNat 64 (4*i) := by
    rw [hbefore.keep.gpr (by decide), h.ptr11]
    change S + BitVec.ofNat 64 (4*(i-1)) + BitVec.ofNat 64 4 = _
    rw [Offset.add_add]
    exact congrArg (fun j => S + BitVec.ofNat 64 j) (by omega)
  have hwr : InRegions v.wr (v.gpr .r11 + 4#64) 4 := by
    rw [haddr, hbefore.keep.2.2, h.keep.2.2]
    exact ⟨⟨S, 240⟩, hc.schedule,
      Offset.contains_base _ (d := 4*i) (n := 4) (k := 240) (by omega) (by omega)⟩
  refine WP.seq (WP.mono (wordStore_ok v hrd hwr) fun t ht => ?_)
  have hvalue : (v.gpr .r9).setWidth 32 ^^^ v.mem.readW (v.gpr .r10) 32 = W base.mem P nk i := by
    rw [htemp, hbefore.mem, hbefore.keep.gpr (by decide), h.ptr10, h.good _ (by omega), BitVec.xor_comm]
    exact (W_ge hn.1 hni).symm
  have hm : t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4*i)) (W base.mem P nk i) := by
    rw [ht.mem, haddr, hvalue, hbefore.mem]
  have hidx : t.gpr .r12 = BitVec.ofNat 64 (4*(i%nk+1)) := by
    rw [ht.index, hbefore.keep.gpr (by decide), h.index]
    change BitVec.ofNat 64 (4*(i%nk)) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have htest : t.gpr .r0 = BitVec.ofNat 64 (4*(i%nk+1)) - BitVec.ofNat 64 (4*nk) := by
    rw [ht.test, hbefore.keep.gpr (by decide), hbefore.keep.gpr (by decide), h.index, h.keylen]
    change BitVec.ofNat 64 (4*(i%nk)) + BitVec.ofNat 64 4 - BitVec.ofNat 64 (4*nk) = _
    rw [← BitVec.ofNat_add]
    exact congrArg (fun j => BitVec.ofNat 64 j - BitVec.ofNat 64 (4*nk)) (by omega)
  have hleft : t.gpr .r4 = BitVec.ofNat 64 (4*(nk+7)-i) :=
    (ht.keep.gpr (by decide)).trans ((hbefore.keep.gpr (by decide)).trans h.left)
  refine WP.mono (wordEnd_ok t h3 hi htest hidx hleft) fun z ⟨h12, h4, hz⟩ => ?_
  have hframes : Frame [⟨S, 240⟩] base.mem t.mem := by
    rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 4*i) (n := 4) (k := 240) (by omega) (by omega))
  refine ⟨⟨by omega, by omega⟩, (((h.keep.trans hbefore.keep).trans ht.keep).trans hz.keep).mono
    (by simp [keyGprs]), ?_, ?_, h12, ?_, h4, ?_, ?_, ?_⟩
  · rw [hz.keep.gpr (by decide), ht.ptr10, hbefore.keep.gpr (by decide), h.ptr10]
    change S + BitVec.ofNat 64 (4*(i-nk)) + BitVec.ofNat 64 4 = _
    rw [Offset.add_add]
    exact congrArg (fun j => S + BitVec.ofNat 64 j) (by omega)
  · rw [hz.keep.gpr (by decide), ht.ptr11, haddr]
    exact congrArg (fun j => S + BitVec.ofNat 64 j) (by omega)
  · rw [hz.keep.gpr (by decide), ht.keep.gpr (by decide), hbefore.keep.gpr (by decide), h.keylen]
  · rw [hz.keep.gpr (by decide), ht.keep.gpr (by decide), hrc, Nat.add_sub_cancel]
  · rw [hz.mem, hm]
    exact good_store h.good rfl (by omega)
  · rw [hz.mem]; exact hframes

theorem word_loop_ok {base s : State} {P S : Addr} {nk i : Nat} (hc : KeyConfig base P S (4*nk))
    (h : WordInv base P S nk i s) (hi : i < 4*(nk+7)) :
    WP isa (.loop Impl.Aes.PPC64LE.Crypto.wordBody (.nonzero .d .r4)) s (WordInv base P S nk (4*(nk+7))) := by
  have hnk : nk ≤ 8 := by have := hc.length; omega
  have step : ∀ j t, j+1 ≤ 4*(nk+7) → WordInv base P S nk j t →
      WP isa Impl.Aes.PPC64LE.Crypto.wordBody t (WordInv base P S nk (j+1)) :=
    fun _ _ hj ht => word_step hc ht (by omega)
  have test : ∀ j t, j ≤ 4*(nk+7) → WordInv base P S nk j t →
      (4*(nk+7)-j < 1 → eval (.nonzero .d .r4) t = some false) ∧
      (1 ≤ 4*(nk+7)-j → eval (.nonzero .d .r4) t = some true) := by
    intro j t hj ht
    have he := eval_nonzero_ofNat' t .r4 (by omega) ht.left
    change eval (.nonzero .d .r4) t = some (decide (4*(nk+7)-j ≠ 0)) at he
    constructor
    · intro hl
      rw [he, show 4*(nk+7)-j = 0 by omega]
      rfl
    · intro hl
      rw [he]
      simp only [ne_eq, show ¬4*(nk+7)-j = 0 by omega, not_false_eq_true, decide_true]
  refine WP.mono (WP.chunk_loop (by decide) (by omega) h step test) ?_
  rintro t ⟨j, hj, he, ht⟩
  have hje : j = 4*(nk+7) := by omega
  exact hje ▸ ht

end VG.Proof.Aes.PPC64LE.Crypto
