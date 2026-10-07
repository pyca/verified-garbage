import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.X86_64.RpCode

/-!
# The RSA functions' postconditions do not read the return address

What `ok_of_inline` and `Verified.of_inline` need of the contracts of the
x86-64 RSA functions that call `vg_rsa_mont_mul`: their postconditions read
memory only in their writable buffers, which a precondition with `Clear`
keeps off the 8 bytes below `rsp`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Proof.Rsa.X86_64

/-- The bytes of a writable buffer miss the hole. -/
theorem Clear.miss_wr {H : Region} {s : State} (hc : Clear H s) {p : Addr} {n : Nat}
    (hr : (⟨p, n⟩ : Region) ∈ s.wr) (hn : p.toNat + n ≤ 2 ^ 64) {k : Nat} (hk : k ≤ n) :
    ∀ i < k, ¬ H.Contains (p + BitVec.ofNat 64 i) 1 :=
  fun _ hi => Clear.wr_miss hc hr (by omega) (by omega)

theorem patch_mem (b : State) (H : Region) (hv : Mem) (u : Nat → BitVec 64) :
    (b.patch H hv u).mem = overlay H hv b.mem := rfl

theorem pc_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : pcContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : pcContract.post s b) :
    pcContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, hn, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_refl _)
  simp only [pcContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, wordsAt_overlay fun i hi => hm i (by omega)]
  exact hp

theorem pdChk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : pdChkContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : pdChkContract.post s b) :
    pdChkContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hn, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_refl _)
  simp only [pdChkContract, State.patch_gpr] at hp ⊢
  intro nB hl he
  rw [patch_mem, written_overlay hm]
  exact hp nB hl he

theorem crt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : crtContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : crtContract.post s b) :
    crtContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hn : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_of_eq hl.symm)
  simp only [crtContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, written_overlay hm]
  exact hp

theorem rp_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : rpContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : rpContract.post s b) :
    rpContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hn₁ : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn₂ : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := hs
  have hm₁ := Clear.miss_wr hc (by rw [hwr]; simp) hn₁ (Nat.le_of_eq h1.symm)
  have hm₂ := Clear.miss_wr hc (by rw [hwr]; simp) hn₂ (Nat.le_of_eq h2.symm)
  simp only [rpContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, writtenAll_overlay fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact hm₁
    · exact hm₂]
  exact hp

end VG.Proof.Bignum.X86_64
