import VerifiedGarbage.Proof.Mont.X86.P256Red

/-! # Certified selection of the sparse P-256 reduction row -/
namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem p256RedChoice_ok (n m : Nat) : (p256RedChoice n m).ok n m = true := by
  unfold p256RedChoice
  split
  next h => rcases h with ⟨rfl, rfl⟩; decide +kernel
  next _ => rfl

theorem p256RedEnabled_ok {M : Mod} {m : Nat} (h : M.ok m = true)
    (he : p256RedEnabled M = true) :
    M.n = 4 ∧ m = p256Prime ∧ minv32 M = 1 := by
  simp only [p256RedEnabled, Bool.and_eq_true, beq_iff_eq] at he
  have hr := M.ok_red h
  rw [he.1.2] at hr
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hr
  have hv := hr.1.2
  have hl := hr.1.1.2
  change (2 ^ 192 - 2 ^ 160 + 2 ^ 128 + 2 ^ 32) = (m + 1) / 2 ^ 64 at hv
  exact ⟨he.1.1, by unfold p256Prime; omega, he.2⟩

theorem redRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} {acc i w N m : Nat} (hN : words M = N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hb : M.mo + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size)
    (hsep : M.mo + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ M.mo)
    (hm : val32 s.mem base M.mo N = m) (hred : M.ok m = true)
    (hq : (s.gpr .ecx).toNat = w32 s.mem base w * (minv32 M).toNat % 2 ^ 32)
    (hlt : val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base M.mo N < 2 ^ (32 * (N + 2))) :
    WP isa (.block (redRow M acc)) s fun u =>
      Outside base w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base w (N + 2) = val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base M.mo N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  unfold redRow
  split
  next he =>
    obtain ⟨hn, hm', hi⟩ := p256RedEnabled_ok hred he
    have hn' : N = 8 := by rw [← hN, words, hn]
    rw [hn'] at hb hwN hsep hm hlt ⊢
    have hq' : (s.gpr .ecx).toNat = w32 s.mem base w := by
      rw [hi] at hq
      change _ = _ * 1 % 2 ^ 32 at hq
      rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base w) 32).isLt] at hq
      exact hq
    rw [hm, hm'] at hlt ⊢
    simp only [Nat.reduceAdd, Nat.reduceMul] at hlt
    unfold p256Prime at hlt
    exact WP.mono (p256Red_ok hs hp hw hwN hq' hlt) fun u ⟨O, V, K⟩ => ⟨O, V, K.mono (by decide)⟩
  next _ =>
    rw [hN]
    exact mulRow_ok hs hp hw hb hwN hsep hlt

end VG.Proof.Mont.X86
