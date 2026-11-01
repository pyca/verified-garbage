module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA

/-!
# ML-KEM on x86-64: the NTT on registers, of `u16`s

`nttR16 pb` is `nttR pb` reading the polynomial at `rdi` as `u16`s
(`PolyIsW 16`): pass A of `u16`s (`passA16`) leaves pass B the state pass A
of `u32`s does (`stA16_toBA`), so `checkAcc pb d` says it leaves `NTT` of the
polynomial in the accumulator at `d` too (`nttRAcc16_ok`), and `check pb d`
that it leaves it as `u32`s at `d` (`nttR16_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR sR Keep Acc16)

/-- The words of a polynomial of `u16`s. -/
def inW16 (m : Mem) (p : Addr) : WPoly := Vector.ofFn fun i => wordAt m p i.val

theorem inW16_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 256) : (inW16 m p)[i]! = wordAt m p i := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi)]; simp [inW16]

theorem coeffAtW16_word (m : Mem) (p : Addr) (i : Nat) : coeffAtW 16 m p i = wordAt m p i := rfl

theorem inTerms16_get {j : Nat} (hj : j < 256) : Y.get (inTerms16.getD (j / 16) []) (j % 16) = .lv 0 j := by
  rw [inTerms16, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some, Y.get, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.mod_lt _ (by decide)), Option.map_some, Option.getD_some,
    show 16 * (j / 16) + j % 16 = j by omega]

theorem initA16_reg (r : XReg) :
    initA16.reg r = if r = .xmm15 then List.replicate 16 (.c qN) else List.replicate 16 .junk := by
  cases r <;> rfl

theorem initA16_rel {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {s₁ : State}
    (hL : ∀ p < 256, L 0 p = wordAt s₁.mem (s₁.gpr .rdi) p)
    (hq : ∀ e < 16, wd s₁ .xmm15 e = 3329) : Rel rsA16 L O initA16 s₁ s₁ := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, by cases s₁; rfl,
    ⟨by simp only [initA16, rsA16, List.length_cons, List.length_nil], by simp [initA16]⟩, fun _ _ => rfl⟩
  · rw [initA16_reg]
    split
    · rename_i hr; subst hr
      rw [get_replicate _ he, hq e he]; exact Hd.of_eq rfl
    · rw [get_replicate _ he]; exact Hd.junk _
  · simp only [rsA16, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rw [show initA16.mem.getD 0 [] = junks 16 by simp only [initA16, List.getD_cons_zero], junks_get]; rfl
    · have hj' : j < 256 := hj
      have hb : rbase rsA16 s₁ 1 = s₁.gpr .rdi := by simp [rbase, rsA16]
      rw [show initA16.mem.getD 1 [] = inTerms16 by simp only [initA16, List.getD_cons_succ, List.getD_cons_zero],
        inTerms16_get hj', hb]
      refine Hd.of_eq ?_
      simp only [E.eval]
      rw [hL _ hj']

/-- The regions of `S` and of the input's 512 bytes: readable, `S` writable, apart. -/
theorem ctx16 {s : State} (hS : pR (s.gpr .rsi) ∈ s.wr) (hX : sR (s.gpr .rdi) ∈ s.rd ++ s.wr)
    (hD : (sR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (h8 : s.gpr .r8 = s.syms tblName) :
    Ctx rsA16 s := by
  have cS : (pR (s.gpr .rsi)).Contains (s.gpr .rsi + BitVec.ofNat 64 oS) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; simp [oS]
  have cX : (sR (s.gpr .rdi)).Contains (s.gpr .rdi + BitVec.ofNat 64 0) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have sep : Mem.Sep (s.gpr .rsi + BitVec.ofNat 64 oS) 512 (s.gpr .rdi + BitVec.ofNat 64 0) 512 := by
    intro x h1 h2
    rw [Offset.lt_iff x _ (by decide)] at h1
    rw [Offset.lt_iff x _ (by decide)] at h2
    exact hD x (by show (x - s.gpr .rdi).toNat + 1 ≤ 512; omega)
      (by show (x - s.gpr .rsi).toNat + 1 ≤ 1024; simp only [oS] at h1; omega)
  refine ⟨fun k hk => ?_, fun k hk hw => ?_, fun k k' hk hk' hne => ?_, fun k hk => ?_, h8⟩
  · simp only [rsA16, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hS, cS⟩
    · exact ⟨_, hX, cX⟩
  · simp only [rsA16, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, hS, cS⟩
    · cases hw
  · simp only [rsA16, List.length_cons, List.length_nil] at hk hk'
    rcases (by omega : k = 0 ∧ k' = 1 ∨ k = 1 ∧ k' = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sep
    · exact fun x h1 h2 => sep x h2 h1
  · simp only [rsA16, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [rlen, rsA16, oS]

/-- `nttR16 pb` leaves `NTT` of the polynomial of `u16`s at `rdi` in the
accumulator at `d`, if `checkAcc pb d`. -/
theorem nttRAcc16_ok {pb : List Instr} {d : Reg} (hc : checkAcc pb d = true) (hd : d = .rdi ∨ d = .r10)
    {s : State} (hS : pR (s.gpr .rsi) ∈ s.wr) (hI : sR (s.gpr .rdi) ∈ s.rd ++ s.wr) (hO : sR (s.gpr d) ∈ s.wr)
    (hDI : (sR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hDO : (sR (s.gpr d)).Disjoint (pR (s.gpr .rsi)))
    (hred : ReducedW 16 s.mem (s.gpr .rdi)) :
    WP isa (nttR16 pb) s fun s' => Acc16 s'.mem (s.gpr d) (ntt (polyAtW 16 s.mem (s.gpr .rdi))) ∧
      Frame [sR (s.gpr d), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold checkAcc at hc
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  obtain ⟨σ₁₆, σ', h16, hA', heq⟩ := stA16_toBA
  have eA : σ' = σA := Option.some.inj (hA'.symm.trans hA)
  subst eA
  unfold nttR16
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  have gd : s1.gpr d = s.gpr d := g _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide)
  let W := inW16 s.mem (s.gpr .rdi)
  let F := polyAtW 16 s.mem (s.gpr .rdi)
  have hW : ∀ p < 256, (W[p]!).toNat = (F[p]!).val := fun p hp => by
    rw [inW16_get _ _ hp, ← coeffAtW16_word, VG.Proof.MlKem.polyIsW_toNat (f := F) ⟨hred, rfl⟩ (by rw [n_eq]; exact hp)]
  have hM : Model fwdRules (Lf W) (Of W) := model W fun p hp => by
    rw [hW p hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (hW p hp)
  have hrel0 : Rel rsA16 (Lf W) (Of W) initA16 s1 s1 := by
    refine initA16_rel (fun p hp => ?_) hq
    show (LW W 0)[p]! = _
    rw [gdi, hm1]; exact inW16_get _ _ hp
  have cA : Ctx rsA16 s1 := ctx16 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact hI)
    (by rw [gdi, gsi]; exact hDI) h8
  have cB : Ctx (rsBA d) s1 := ctxA (by rw [gsi, k1.2.2]; exact hS) (by rw [gd, k1.2.2]; exact hO)
    (by rw [gd, gsi]; exact hDO) h8
  refine WP.mono (run_ok hM cA passA16 hrel0 h16) fun s2 hr2 => ?_
  have hr2' := reframeA (d := d) hr2
  rw [heq] at hr2'
  refine WP.mono (run_ok hM cB pb hr2' hB) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsBA d) s1 1 = s.gpr d := by simp [rbase, rsBA, gd]
    intro w hw
    have h0 := hr3.mem 1 w (by simp [rsBA]) (by simp [rlen, rsBA]; omega)
    rw [outAccOk_get hc hw, hb] at h0
    have e0 := h0.eq rfl
    show (wordAt s3.mem (s.gpr d) w).toNat = _
    rw [e0]
    exact Of_ntt W F hrep (accIdx_lt hw)
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsBA, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega
    · refine hx (sR (s.gpr d)) (by simp) ?_
      simp only [rbase, rlen, rsBA, List.getD_cons_succ, List.getD_cons_zero, gd] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr d).toNat + 1 ≤ 512
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

theorem toB_eq_of_toBA {a b : St} (h : toBA a = toBA b) : toB a = toB b := by
  simp only [toBA, toB, St.mk.injEq, List.cons.injEq] at h ⊢
  exact ⟨h.1, h.2.1, trivial⟩

/-- `nttR16 pb` leaves `NTT` of the polynomial of `u16`s at `rdi` as `u32`s at
`d`, if `check pb d`. -/
theorem nttR16_ok {pb : List Instr} {d : Reg} (hc : check pb d = true) (hd : d = .rdi ∨ d = .r10) {s : State}
    (hS : pR (s.gpr .rsi) ∈ s.wr) (hI : sR (s.gpr .rdi) ∈ s.rd ++ s.wr) (hO : pR (s.gpr d) ∈ s.wr)
    (hDI : (sR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hDO : (pR (s.gpr d)).Disjoint (pR (s.gpr .rsi)))
    (hred : ReducedW 16 s.mem (s.gpr .rdi)) :
    WP isa (nttR16 pb) s fun s' => PolyIs s'.mem (s.gpr d) (ntt (polyAtW 16 s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr d), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold check at hc
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  obtain ⟨σ₁₆, σ', h16, hA', heq⟩ := stA16_toBA
  have eA : σ' = σA := Option.some.inj (hA'.symm.trans hA)
  subst eA
  unfold nttR16
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  have gd : s1.gpr d = s.gpr d := g _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide)
  let W := inW16 s.mem (s.gpr .rdi)
  let F := polyAtW 16 s.mem (s.gpr .rdi)
  have hW : ∀ p < 256, (W[p]!).toNat = (F[p]!).val := fun p hp => by
    rw [inW16_get _ _ hp, ← coeffAtW16_word, VG.Proof.MlKem.polyIsW_toNat (f := F) ⟨hred, rfl⟩ (by rw [n_eq]; exact hp)]
  have hM : Model fwdRules (Lf W) (Of W) := model W fun p hp => by
    rw [hW p hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (hW p hp)
  have hrel0 : Rel rsA16 (Lf W) (Of W) initA16 s1 s1 := by
    refine initA16_rel (fun p hp => ?_) hq
    show (LW W 0)[p]! = _
    rw [gdi, hm1]; exact inW16_get _ _ hp
  have cA : Ctx rsA16 s1 := ctx16 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact hI)
    (by rw [gdi, gsi]; exact hDI) h8
  have cB : Ctx (rsB d) s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS)
    (by rw [gd, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO)
    (fun _ => by rw [gd, k1.2.2]; exact hO) (by rw [gd, gsi]; exact hDO) h8
  refine WP.mono (run_ok hM cA passA16 hrel0 h16) fun s2 hr2 => ?_
  have hr2' := reframe (d := d) hr2
  rw [toB_eq_of_toBA heq] at hr2'
  refine WP.mono (run_ok hM cB pb hr2' hB) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsB d) s1 1 = s.gpr d := by simp [rbase, rsB, gd]
    refine VG.Proof.MlKem.polyIs_of_toNat fun p hp => ?_
    rw [n_eq] at hp
    have h0 := hr3.mem 1 (2 * p) (by simp [rsB]) (by simp [rlen, rsB]; omega)
    have h1 := hr3.mem 1 (2 * p + 1) (by simp [rsB]) (by simp [rlen, rsB]; omega)
    rw [outOk_get hc (by omega), hb] at h0 h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show 2 * p / 2 = p by omega] at h0
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at h1
    have e0 := h0.eq rfl
    have e1 := h1.eq rfl
    show (coeffAt s3.mem (s.gpr d) p).toNat = _
    rw [coeff_words, toNat_app16, e0, e1]
    simp only [E.eval]
    rw [Of_ntt W F hrep hp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
    rfl
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsB, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega
    · refine hx (pR (s.gpr d)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_succ, List.getD_cons_zero, gd] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr d).toNat + 1 ≤ 1024
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

end VG.Proof.MlKem.X86_64.NttR
