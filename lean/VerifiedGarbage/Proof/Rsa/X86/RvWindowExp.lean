module

public import VerifiedGarbage.Proof.Rsa.X86.RvWindowLoop
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSet
public import VerifiedGarbage.Proof.Rsa.X86.RvArguments
public import VerifiedGarbage.Proof.Rsa.RecoverExp

/-! # A recovery candidate's power by fixed 4-bit windows

The exponent `r < 2 ^ c` (`c = 8 (e_len + d_len)` bits) is first shifted up
by the `L - c` bits its `L`-bit words leave above it, so that its windows
are its words' top bits; then the windows' loop of `c / 4` iterations.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem windowLoop_ok {g : Geo} {s0 s : State} {T AW V : Nat → Nat} {m b E C : Nat}
    (h : WI g s0 T AW V m b E C 0 s)
    (table : ∀ j < 16, T j = b ^ j * 2 ^ (64 * g.n) % m)
    (value : T mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (count : 0 < C) (hC : C < 2 ^ 32) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.windowBody .ne) s (WI g s0 T AW V m b E C C) := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = C ∧ 0 < j ∧ WI g s0 T AW V m b E C k u)
    ?_ C s ⟨0, by omega, count, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (windowBody_ok hu table value bound inverse odd positive (by omega) hC)
    fun t ⟨ht, zt⟩ => ?_
  by_cases last : k + 1 = C
  · left
    refine ⟨?_, last ▸ ht⟩
    change t.zf.map (!·) = some false
    simp [zt, last]
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show C - (k + 1) ≠ 0 from by omega]

/-- The exponent's alignment after `j` of its four-bit shifts. -/
def AI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (r C j : Nat) (s : State) : Prop :=
  KS g s0 A liveExp (upd AW wRc (r * 16 ^ j % 2 ^ (32 * g.W))) [wRc, wR] (upd V sCnt (C - j)) slotsExp s

theorem alignBody_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {r C j : Nat}
    (h : AI g s0 A AW V r C j s) (hj : j < C) (hC : C < 2 ^ 32) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.alignBody s fun t => AI g s0 A AW V r C (j + 1) t ∧
      t.zf = some (decide (C - (j + 1) = 0)) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.alignBody AI at *
  refine WP.seq (WP.mono (h.shiftUp_W (by simp) (by decide)) fun u ⟨hu, _⟩ => ?_)
  rw [upd_self, upd_twice] at hu
  have hu' := hu.mono (liveW' := [wRc, wR]) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨by simp [hj], rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (hu'.cntNext_ok (by simp) (by rw [upd_self]; omega) (by rw [upd_self]; omega))
    fun t ⟨ht, zt⟩ => ⟨?_, ?_⟩
  · rw [upd_self, upd_twice] at ht
    refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨by simp [hd], ?_⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [upd_self, upd_self, Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_mod]
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    · by_cases e : d = sCnt
      · subst e; rw [upd_self, upd_self]; omega
      · rw [upd_ne _ _ e, upd_ne _ _ e]
  · rw [zt, upd_self, Nat.sub_sub]

theorem alignLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {r C : Nat}
    (h : AI g s0 A AW V r C 0 s) (count : 0 < C) (hC : C < 2 ^ 32) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.alignBody .ne) s (AI g s0 A AW V r C C) := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = C ∧ 0 < j ∧ AI g s0 A AW V r C k u)
    ?_ C s ⟨0, by omega, count, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (alignBody_ok hu (by omega) hC) fun t ⟨ht, zt⟩ => ?_
  by_cases last : k + 1 = C
  · left
    refine ⟨?_, last ▸ ht⟩
    change t.zf.map (!·) = some false
    simp [zt, last]
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show C - (k + 1) ≠ 0 from by omega]

theorem alignCount_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {eLen dLen : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (wide : 8 * (dLen + eLen) < 32 * g.W) (fits : 8 * g.W < 2 ^ 32) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.alignCount) s fun t =>
      KS g s0 A live AW liveW (upd V sCnt (8 * g.W - 2 * (dLen + eLen))) (sCnt :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.alignCount
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h.arg ae (by decide)).readSrc fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_addS (hu.arg ad (by decide)).readSrc fun v D _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  have hw := (hu.of_rest D.keeps (by decide) D.mem).of_rest W.keeps (by decide) W.mem
  have ea : w.gpr .eax = BitVec.ofNat 32 (2 * (dLen + eLen)) := by
    rw [W.gpr, D.gpr, U.gpr]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hw.rtW) hw.rtW.lenLe
    fun x K m e => ?_
  rw [kw_wid] at e
  have hx := hw.of_rest K (by decide) m
  refine wp_addS rfl fun y Y _ => wp_subS rfl fun z Z _ => ?_
  have hz := (hx.of_rest Y.keeps (by decide) Y.mem).of_rest Z.keeps (by decide) Z.mem
  have exa : y.gpr .eax = BitVec.ofNat 32 (2 * (dLen + eLen)) := by
    rw [Y.other _ (by decide), K.1 _ (by decide), ea]
  have ey : (y.gpr .edx).toNat = 8 * g.W := by
    rw [Y.gpr, BitVec.toNat_add, e]; simp only [Geo.W] at fits ⊢; omega
  have value : z.gpr .edx = BitVec.ofNat 32 (8 * g.W - 2 * (dLen + eLen)) := by
    apply BitVec.eq_of_toNat_eq
    rw [Z.gpr, BitVec.toNat_sub, ey, exa, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.mono (hz.storeSlot (d := sCnt) (by decide) .edx) fun t ⟨ht, _, _⟩ => ?_
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  exact ht

theorem windowCount_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {eLen dLen : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (bound : 8 * (dLen + eLen) < 2 ^ 32) :
    WP isa (.block windowCount) s fun t =>
      KS g s0 A live AW liveW (upd V sCnt (2 * (dLen + eLen))) (sCnt :: ls) t := by
  unfold windowCount
  refine wp_movS (h.arg ae (by decide)).readSrc fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_addS (hu.arg ad (by decide)).readSrc fun v D _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  have hw := (hu.of_rest D.keeps (by decide) D.mem).of_rest W.keeps (by decide) W.mem
  have value : w.gpr .eax = BitVec.ofNat 32 (2 * (dLen + eLen)) := by
    rw [W.gpr, D.gpr, U.gpr]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  refine WP.mono (hw.storeSlot (d := sCnt) (by decide) .eax) fun t ⟨ht, _, _⟩ => ?_
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  exact ht

/-- `r` shifted up by `L - c` bits, `L` its words' bits. -/
theorem aligned_value {r c L : Nat} (hr : r < 2 ^ c) (hc : c ≤ L) (h4 : 4 ∣ L - c) :
    r * 16 ^ ((L - c) / 4) % 2 ^ L = r * 2 ^ (L - c) := by
  have e : (16 : Nat) ^ ((L - c) / 4) = 2 ^ (L - c) := by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]
    congr 1
    omega
  rw [e]
  apply Nat.mod_eq_of_lt
  have := Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos (L - c))
  rwa [← Nat.pow_add, show c + (L - c) = L by omega] at this

/-- The aligned exponent's windows, all `c / 4` of them, are `r`. -/
theorem windows_value {r c L : Nat} (hc : c ≤ L) (h4 : 4 ∣ c) :
    r * 2 ^ (L - c) * 16 ^ (c / 4) / 2 ^ L = r := by
  rw [show (16 : Nat) ^ (c / 4) = 2 ^ c by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega,
    Nat.mul_assoc, ← Nat.pow_add, show L - c + c = L by omega]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

theorem windows_rest {r c L : Nat} (hc : c ≤ L) (h4 : 4 ∣ c) :
    r * 2 ^ (L - c) * 16 ^ (c / 4) % 2 ^ L = 0 := by
  rw [show (16 : Nat) ^ (c / 4) = 2 ^ c by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega,
    Nat.mul_assoc, ← Nat.pow_add, show L - c + c = L by omega]
  exact Nat.mul_mod_left _ _

end VG.Proof.Rsa.X86.Recover
