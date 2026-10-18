module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on x86-64: the NTT on registers

`nttR pb` (`pb` pass B storing to `d`, as `check` says) leaves `NTT` of the
polynomial at `rdi` at `d` (`nttR_ok`): after `pro`, the terms of `initA`
hold, with the polynomial's words after `st` layers `Lf W st` for its words
`W` and their reductions `Of W`; pass A keeps them (`run_ok`) in the regions
`rsA`, pass B in the regions `rsB d`, and `check` says the output's terms are
`Of W`, which `Of_ntt` takes to `NTT`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR Keep yconst_ok)

/-! ## Coefficients as words -/

theorem coeff_words (m : Mem) (p : Addr) (i : Nat) :
    coeffAt m p i = wordAt m p (2 * i + 1) ++ wordAt m p (2 * i) := by
  have h0 := readW_extract m (p + BitVec.ofNat 64 (4 * i)) (w := 32) (k := 0) (n := 2) (by omega)
  have h1 := readW_extract m (p + BitVec.ofNat 64 (4 * i)) (w := 32) (k := 2) (n := 2) (by omega)
  have a0 : p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 0 = wAddr p (2 * i) := by
    simp only [wAddr, BitVec.add_zero]; congr 2; omega
  have a1 : p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 2 = wAddr p (2 * i + 1) := by
    rw [wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [a0] at h0; rw [a1] at h1
  have h0' : (m.readW (p + BitVec.ofNat 64 (4 * i)) 32).extractLsb' 0 16 = m.readW (wAddr p (2 * i)) 16 := h0
  have h1' : (m.readW (p + BitVec.ofNat 64 (4 * i)) 32).extractLsb' 16 16 = m.readW (wAddr p (2 * i + 1)) 16 := h1
  unfold wordAt coeffAt
  rw [← h0', ← h1']
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · simp only [show j < 16 by omega, decide_true, Bool.true_and]; exact congrArg _ (by omega)
  · simp only [show j - 16 < 16 by omega, decide_true, Bool.true_and]; exact congrArg _ (by omega)

/-- The words of the input's coefficients. -/
def inW (m : Mem) (p : Addr) : WPoly := Vector.ofFn fun i => wordAt m p (2 * i.val)

theorem inW_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 256) : (inW m p)[i]! = wordAt m p (2 * i) := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi)]; simp [inW]

theorem toNat_app16 (a b : BitVec 16) : (a ++ b).toNat = a.toNat * 65536 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem reduced_words {m : Mem} {p : Addr} (h : Reduced m p) {i : Nat} (hi : i < 256) :
    wordAt m p (2 * i + 1) = 0 ∧ (wordAt m p (2 * i)).toNat = (coeffAt m p i).toNat := by
  have hc : (coeffAt m p i).toNat < 3329 := h i (by rw [n_eq]; exact hi)
  rw [coeff_words, toNat_app16] at hc ⊢
  exact ⟨BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 16).toNat = 0 from rfl]; omega), by omega⟩

/-! ## The prologue -/

theorem word_q {i : Nat} (hi : i < 8) : word (ofDwords 0x0D010D01 0x0D010D01 0x0D010D01 0x0D010D01) i = 3329 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pro_ok (s : State) :
    WP isa (.block pro) s fun s1 => s1.gpr .r8 = s1.syms tblName ∧ (∀ e < 16, wd s1 .xmm15 e = 3329) ∧
      s1.mem = s.mem ∧ Keep [.rax, .r8] s s1 := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 0x0D010D01 s) fun s2 ⟨hl, k2, hm, _, _⟩ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨rfl, fun e he => ?_, hm, ?_⟩⟩
  · simp only [wd, VG.Proof.MlKem.X86_64.lane_setReg]
    rw [hl _ (by omega), word_q (Nat.mod_lt _ (by decide))]
  · refine ⟨fun r hr => ?_, k2.2.1, k2.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2]
    exact k2.1 r (by simpa using hr.1)

/-! ## The regions -/

/-- A region of `S` and `X`: readable, `S` writable (and `X` if `w`), apart. -/
theorem ctx2 {s : State} {X : Reg} {w : Bool} (hS : pR (s.gpr .rsi) ∈ s.wr)
    (hX : pR (s.gpr X) ∈ s.rd ++ s.wr) (hXw : w = true → pR (s.gpr X) ∈ s.wr)
    (hD : (pR (s.gpr X)).Disjoint (pR (s.gpr .rsi))) (h8 : s.gpr .r8 = s.syms tblName) :
    Ctx [(.rsi, oS, 256, true), (X, 0, 512, w)] s := by
  have cS : (pR (s.gpr .rsi)).Contains (s.gpr .rsi + BitVec.ofNat 64 oS) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; simp [oS]
  have cX : (pR (s.gpr X)).Contains (s.gpr X + BitVec.ofNat 64 0) 1024 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have sep : Mem.Sep (s.gpr .rsi + BitVec.ofNat 64 oS) 512 (s.gpr X + BitVec.ofNat 64 0) 1024 := by
    intro x h1 h2
    rw [Offset.lt_iff x _ (by decide)] at h1
    rw [Offset.lt_iff x _ (by decide)] at h2
    exact hD x (by show (x - s.gpr X).toNat + 1 ≤ 1024; omega)
      (by show (x - s.gpr .rsi).toNat + 1 ≤ 1024; simp only [oS] at h1; omega)
  refine ⟨fun k hk => ?_, fun k hk hw => ?_, fun k k' hk hk' hne => ?_, fun k hk => ?_, h8⟩
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hS, cS⟩
    · exact ⟨_, hX, cX⟩
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, hS, cS⟩
    · exact ⟨_, hXw hw, cX⟩
  · simp only [List.length_cons, List.length_nil] at hk hk'
    rcases (by omega : k = 0 ∧ k' = 1 ∨ k = 1 ∧ k' = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sep
    · exact fun x h1 h2 => sep x h2 h1
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [rlen, oS]

/-! ## The terms where each pass starts -/

theorem initA_reg (r : XReg) :
    initA.reg r = if r = .xmm15 then List.replicate 16 (.c qN) else List.replicate 16 .junk := by
  cases r <;> rfl

theorem get_replicate (x : E) {e : Nat} (he : e < 16) : Y.get (List.replicate 16 x) e = x := by
  rw [Y.get, List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left_of_eq_true _ _ (eq_true he)]; rfl

theorem junks_get (n c e : Nat) : Y.get ((junks n).getD c []) e = .junk := by
  rw [junks, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split
  · rw [Option.getD_some, Y.get, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  · rfl

theorem inTerms_get {j : Nat} (hj : j < 512) :
    Y.get (inTerms.getD (j / 16) []) (j % 16) = if j % 2 = 0 then .lv 0 (j / 2) else .c 0 := by
  rw [inTerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some, Y.get, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.mod_lt _ (by decide)), Option.map_some, Option.getD_some,
    show 16 * (j / 16) + j % 16 = j by omega]

theorem initA_rel {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {s₁ : State}
    (hL : ∀ p < 256, L 0 p = wordAt s₁.mem (s₁.gpr .rdi) (2 * p))
    (hz : ∀ p < 256, wordAt s₁.mem (s₁.gpr .rdi) (2 * p + 1) = 0)
    (hq : ∀ e < 16, wd s₁ .xmm15 e = 3329) : Rel rsA L O initA s₁ s₁ := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, by cases s₁; rfl, ⟨by simp only [initA, rsA, List.length_cons, List.length_nil], by simp [initA]⟩, fun _ _ => rfl⟩
  · rw [initA_reg]
    split
    · rename_i hr; subst hr
      rw [get_replicate _ he, hq e he]; exact Hd.of_eq rfl
    · rw [get_replicate _ he]; exact Hd.junk _
  · simp only [rsA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rw [show initA.mem.getD 0 [] = junks 16 by simp only [initA, List.getD_cons_zero], junks_get]; rfl
    · have hj' : j < 512 := hj
      have hb : rbase rsA s₁ 1 = s₁.gpr .rdi := by simp [rbase, rsA]
      have ht : Y.get ((initA.mem.getD 1 []).getD (j / 16) []) (j % 16) =
          if j % 2 = 0 then .lv 0 (j / 2) else .c 0 := by
        rw [show initA.mem.getD 1 [] = inTerms by simp only [initA, List.getD_cons_succ, List.getD_cons_zero],
          inTerms_get hj']
      rw [ht, hb]
      split
      · rename_i h2
        refine Hd.of_eq ?_
        simp only [E.eval]
        rw [hL _ (by omega), show 2 * (j / 2) = j by omega]
      · refine Hd.of_eq ?_
        rw [show j = 2 * (j / 2) + 1 by omega, hz _ (by omega)]; rfl

/-- Pass B starts from the registers and `S` pass A leaves. -/
theorem reframe {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {X d : Reg} {n : Nat} {σ : St} {s₀ s : State}
    (h : Rel [(.rsi, oS, 256, true), (X, 0, n, false)] L O σ s₀ s) :
    Rel [(.rsi, oS, 256, true), (d, 0, 512, true)] L O (toB σ) s₀ s := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, h.eq, ⟨rfl, by simp [toB, St.set, h.len.2]⟩,
    fun x hx => h.fr x ?_⟩
  · show Hd L O (((σ.set .xmm3 (List.replicate 16 .junk)).reg r).get e) _
    rw [St.reg_set _ _ _ _ h.len.2]
    split
    · rw [get_replicate _ he]; exact Hd.junk _
    · exact h.reg r e he
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact h.mem 0 j (by simp) hj
    · left
      rw [show (toB σ).mem.getD 1 [] = junks 32 by simp only [toB, List.getD_cons_succ, List.getD_cons_zero],
        junks_get]; rfl
  · intro k hk hw
    simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact hx 0 (by simp) rfl
    · cases hw

/-! ## The NTT -/

theorem outOk_get {σ : St} (h : outOk σ = true) {i : Nat} (hi : i < 512) :
    Y.get ((σ.mem.getD 1 []).getD (i / 16) []) (i % 16) = if i % 2 = 0 then .out (i / 2) else .c 0 :=
  E.beq_eq (List.all_eq_true.1 h i (List.mem_range.2 hi))

/-- `nttR pb` leaves `NTT` of the polynomial at `rdi` at `d`, if `check pb d`. -/
theorem nttR_ok {pb : List Instr} {d : Reg} (hc : check pb d = true) (hd : d = .rdi ∨ d = .r10) {s : State}
    (hS : pR (s.gpr .rsi) ∈ s.wr) (hI : pR (s.gpr .rdi) ∈ s.rd ++ s.wr) (hO : pR (s.gpr d) ∈ s.wr)
    (hDI : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hDO : (pR (s.gpr d)).Disjoint (pR (s.gpr .rsi)))
    (hred : Reduced s.mem (s.gpr .rdi)) :
    WP isa (nttR pb) s fun s' => PolyIs s'.mem (s.gpr d) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr d), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold check at hc
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  unfold nttR
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  have gd : s1.gpr d = s.gpr d := g _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide)
  let W := inW s.mem (s.gpr .rdi)
  let F := polyAt s.mem (s.gpr .rdi)
  have hW : ∀ p < 256, (W[p]!).toNat = (F[p]!).val := fun p hp => by
    rw [inW_get _ _ hp, (reduced_words hred hp).2, VG.Proof.MlKem.polyAt_val hred (by rw [n_eq]; exact hp)]
  have hM : Model fwdRules (Lf W) (Of W) := model W fun p hp => by
    rw [hW p hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (hW p hp)
  have hrel0 : Rel rsA (Lf W) (Of W) initA s1 s1 := by
    refine initA_rel (fun p hp => ?_) (fun p hp => ?_) hq
    · show (LW W 0)[p]! = _
      rw [gdi, hm1]; exact inW_get _ _ hp
    · rw [gdi, hm1]; exact (reduced_words hred hp).1
  have cA : Ctx rsA s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact hI)
    (fun h => by cases h) (by rw [gdi, gsi]; exact hDI) h8
  have cB : Ctx (rsB d) s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gd, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO)
    (fun _ => by rw [gd, k1.2.2]; exact hO) (by rw [gd, gsi]; exact hDO) h8
  refine WP.mono (run_ok hM cA passA hrel0 hA) fun s2 hr2 => ?_
  refine WP.mono (run_ok hM cB pb (reframe hr2) hB) fun s3 hr3 => ?_
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
