module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsLeaves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: a lane at a height

`forsUpLane k` at height `z` (`upLane_ok`): lane `k`'s message its node and
the authentication path's node `z`, in the order bit `z` of its leaf says;
its address's height `z + 1` and index `⌊L / 2^(z+1)⌋`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr bytesAt_frame readW_frame)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-- The first two fields of 16 bytes. -/
theorem split16 {m : Mem} {S : Addr} {d : Nat} {A B C D : List Byte} (hA : A.length = 4) (hB : B.length = 4)
    (h : bytesAt m (at' S d) 16 = A ++ (B ++ (C ++ D))) :
    bytesAt m (at' S d) 4 = A ∧ bytesAt m (at' S (d + 4)) 4 = B := by
  rw [show (16 : Nat) = 4 + 12 from rfl, Fors.bytesAt_cat] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [TreeBase.bytesAt_length, hA])
  rw [show (12 : Nat) = 4 + 8 from rfl, Fors.bytesAt_cat] at h₂
  exact ⟨h₁, (List.append_inj h₂ (by rw [TreeBase.bytesAt_length, hB])).1⟩

theorem and1 (x : Nat) : BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 % 2 ^ 64 : Nat) = 1 from rfl, Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

theorem shr1 (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 1 = BitVec.ofNat 64 (x / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)).symm

/-- The authentication path's node `z` of lane `k`'s tree. -/
abbrev authOf (p : Params) (m : Mem) (sig : Addr) (t₀ k' z : Nat) : List Byte :=
  bytesAt m (sig + BitVec.ofNat 64 (sigOff p (tOf p t₀ k') + p.n + z * p.n)) p.n

/-- What lane `k`'s step at height `z` leaves. -/
structure UL (p : Params) (S : Addr) (kp z L : Nat) (X A : List Byte) (t t' : State) (k' : Nat) : Prop where
  keep : Keep (laneRegs k') t t'
  frame : Frame [tailA p S k'] t.mem t'.mem
  idx : t'.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (L / 2 ^ (z + 1))
  fld : bytesAt t'.mem (at' S (Layout.laneA k' + p.n + 16)) 16 = ufld 3 kp (z + 1) (L / 2 ^ (z + 1))
  msg : bytesAt t'.mem (at' S (Layout.laneA k' + p.n + 32)) (2 * p.n) = if L / 2 ^ z % 2 = 0 then X ++ A else A ++ X

theorem idx_ne' : ∀ j < 4, ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x28],
    r ∉ [Impl.SlhDsa.AArch64.Verify.idxReg j] := by decide

theorem idx_n6 : ∀ j < 4, Impl.SlhDsa.AArch64.Verify.idxReg j ∉ [Reg.x9, .x10, .x12, .x13, .x14, .x15] := by
  decide

theorem upLane_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) {k' t₀ z : Nat} (hk' : k' < 4) (ht₀ : t₀ < 2 ^ 32)
    (hz : z < p.a) {t : State} (hK : FK p σ S sig pk a I t) (h22 : t.gpr .x22 = BitVec.ofNat 64 t₀)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 z) {X : List Byte}
    (hl : Lane p S (σ.gpr .x2).toNat z (lOf p I t₀ k' / 2 ^ z) X t k') :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsUpLane p k') t
      (UL p S (σ.gpr .x2).toNat z (lOf p I t₀ k') X (authOf p σ.mem sig t₀ k' z) t · k') := by
  have hn32 := hF.n32
  have hn16 := hF.n16
  have hn8 := hF.n8
  have hL := ForsPk.laneA_eq k'
  have hw : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hK.wr]; exact c.scr
  obtain ⟨T, eT⟩ : ∃ T, T = tOf p t₀ k' := ⟨_, rfl⟩
  have hT : T < p.k := by rw [eT]; exact tOf_lt hF _ _
  have hLT : lOf p I t₀ k' < 2 ^ 32 := by
    show tOf p t₀ k' * 2 ^ p.a + I (tOf p t₀ k') < 2 ^ 32
    rw [← eT]; exact hF.leaf hT (hIa T hT)
  have hsl := forsSig_le hT (j := z + 1) (by omega)
  have hso : sigOff p T + p.n + z * p.n + p.n ≤ p.forsSigLen := by
    have e1 : p.n * (z + 1) = p.n * z + p.n := Nat.mul_succ _ _
    simp only [sigOff]; rw [Nat.mul_comm z p.n]; omega
  have hsf := c.sfit
  have e8 : 8 * (p.n / 8) = p.n := by omega
  have hnot : ∀ j < 4, Impl.SlhDsa.AArch64.Verify.idxReg j ∉
      [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x19, .x20, .x21, .x22, .x23] := by decide
  unfold Impl.SlhDsa.AArch64.Verify.forsUpLane
  simp only [Impl.SlhDsa.AArch64.Shake.layout, Layout.adrsOff, Layout.msgOff]
  refine WP.seq ?_
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine treeT_ok hF hk' ht₀ h22 fun t₁ o₁ e₁ => ?_
  rw [← eT] at e₁
  refine treeSig_ok hF e₁ (by rw [o₁.get .x21, hK.x21]) fun t₂ o₂ e₂ => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₃ o₃ e₃ => mulN_ok hF.nv (r := .x13) (tmp := .x14) (by decide)
    fun t₄ o₄ e₄ => ?_
  refine MlKem.AArch64.wp_add fun t₅ o₅ e₅ => MlKem.AArch64.wp_addImm (by omega) fun t₆ o₆ e₆ =>
    MlKem.AArch64.wp_movz fun t₇ o₇ e₇ => MlKem.AArch64.wp_and fun t₈ o₈ e₈ => WP.block_nil ?_
  have o₁₇ : Only [.x9, .x10, .x12, .x13, .x14, .x15] t t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono (by decide)
  have o₁₈ : Only [.x9, .x10, .x12, .x13, .x14, .x15] t t₈ := (o₁₇.trans o₈).mono (by decide)
  have hx₈ : t₈.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ z) := by
    rw [o₁₈.get _ (idx_n6 k' hk'), hl.idx]
  have hb₉ : t₈.gpr .x9 = BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ z % 2) := by
    rw [e₈, o₁₇.get _ (idx_n6 k' hk'), hl.idx, e₇, show (1 : BitVec 16).setWidth 64 = BitVec.ofNat 64 1 from rfl, and1]
  have h12 : t₈.gpr .x12 = sig + BitVec.ofNat 64 (sigOff p T + p.n + z * p.n) := by
    rw [o₈.get .x12, o₇.get .x12, e₆, e₅, o₄.get .x12, o₃.get .x12, e₂, e₄, e₃, o₂.get .x23, o₁.get .x23, h23,
      BitVec.add_zero, BitVec.ofNat_mul_ofNat, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
    congr 2; omega
  have hm₈ : t₈.mem = t.mem := o₁₈.mem
  have hb19 : t₈.gpr .x19 = S := by rw [o₁₈.get .x19, hK.x19]
  have hw₈ : (⟨S, 65536⟩ : Region) ∈ t₈.wr := by rw [o₁₈.wr]; exact hw
  have hrd₈ : t₈.rd = σ.rd := by rw [o₁₈.rd, hK.rd]
  have hso' : sigOff p T + p.n + z * p.n + 8 * (p.n / 8) ≤ p.forsSigLen := by rw [e8]; exact hso
  have hA : bytesAt t₈.mem (sig + BitVec.ofNat 64 (sigOff p T + p.n + z * p.n)) p.n = authOf p σ.mem sig t₀ k' z := by
    rw [hm₈, hK.sig hF c hso, authOf, ← eT]
  have hX : bytesAt t₈.mem (at' S (Layout.laneA k' + p.n + 32)) p.n = X := by rw [hm₈, hl.msg]
  have hsrc : InRegions (t₈.rd ++ t₈.wr) (t₈.gpr .x12 + BitVec.ofNat 64 0) (8 * (p.n / 8)) :=
    ⟨_, List.mem_append_left _ (by rw [hrd₈]; exact c.sigR), by
      rw [h12, BitVec.add_zero]; exact Offset.contains_base sig hso' (by omega)⟩
  have hsd : ∀ {o : Nat}, o + p.n ≤ 65536 → Region.Disjoint ⟨S + BitVec.ofNat 64 o, 8 * (p.n / 8)⟩
      ⟨t₈.gpr .x12 + BitVec.ofNat 64 0, 8 * (p.n / 8)⟩ := fun ho => by
    rw [h12, BitVec.add_zero]
    exact ((c.sss.sub_left (Offset.sub_base sig hso')).sub_right (Offset.sub_base S (by omega))).symm
  let MP : State → Prop := fun u => Keep [.x14] t₈ u ∧
    Frame [⟨at' S (Layout.laneA k' + p.n + 32), 2 * p.n⟩] t₈.mem u.mem ∧
    bytesAt u.mem (at' S (Layout.laneA k' + p.n + 32)) (2 * p.n) =
      if lOf p I t₀ k' / 2 ^ z % 2 = 0 then X ++ authOf p σ.mem sig t₀ k' z else authOf p σ.mem sig t₀ k' z ++ X
  have hb : isa.eval (.zero .x .x9) t₈ = some (decide (lOf p I t₀ k' / 2 ^ z % 2 = 0)) := by
    rw [MlKem.AArch64.eval_zero, hb₉, MlKem.AArch64.eq_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  have sub2 : ∀ x, x + p.n ≤ 2 * p.n → ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + 32 + x), p.n⟩ : Region)],
      ∃ R ∈ [(⟨at' S (Layout.laneA k' + p.n + 32), 2 * p.n⟩ : Region)], Region.Sub r R := fun x hx =>
    sub1 S (by omega) (by omega)
  refine WP.seq (WP.mono (Q := MP) (WP.ite _ hb (fun hb₁ => ?_) (fun hb₀ => ?_)) fun u hu => ?_)
  · rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords _ _ _ _ _)]
    refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA k' + (p.n + 32) + p.n) (d₁ := 0) (w := p.n / 8)
      ⟨by decide, by decide, by omega, by omega, hsrc, by rw [hb19]; exact in_scr hw₈ (by omega),
        by rw [hb19]; exact hsd (by omega)⟩ fun u k₁ f₁ c₁ => WP.block_nil ⟨k₁, ?_, ?_⟩
    · rw [hb19, e8, show Layout.laneA k' + (p.n + 32) + p.n = Layout.laneA k' + p.n + 32 + p.n by omega] at f₁
      exact f₁.sub (sub2 p.n (by omega))
    · rw [hb19, e8, show Layout.laneA k' + (p.n + 32) + p.n = Layout.laneA k' + p.n + 32 + p.n by omega] at f₁ c₁
      rw [h12, BitVec.add_zero] at c₁
      simp only [of_decide_eq_true hb₁, ↓reduceIte]
      rw [show 2 * p.n = p.n + p.n by omega, Fors.bytesAt_cat, c₁, hA,
        k1 f₁ (by omega) (by omega) (by omega), hX]
  · refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneA k' + (p.n + 32) + p.n)
      (d₁ := Layout.laneA k' + (p.n + 32)) (w := p.n / 8)
      ⟨by decide, by decide, by omega, by omega, by rw [hb19]; exact in_scr' hw₈ (by omega),
        by rw [hb19]; exact in_scr hw₈ (by omega), by rw [hb19, e8]; exact disj_scr S (by omega) (by omega) (by omega)⟩
      fun u₁ k₁ f₁ c₁ => ?_
    rw [hb19, e8, show Layout.laneA k' + (p.n + 32) + p.n = Layout.laneA k' + p.n + 32 + p.n by omega] at f₁ c₁
    rw [show Layout.laneA k' + (p.n + 32) = Layout.laneA k' + p.n + 32 by omega] at c₁
    have hb₁ : u₁.gpr .x19 = S := by rw [k₁.get .x19, hb19]
    have h12₁ : u₁.gpr .x12 = t₈.gpr .x12 := k₁.get .x12
    rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords _ _ _ _ _)]
    refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA k' + (p.n + 32)) (d₁ := 0) (w := p.n / 8)
      ⟨by decide, by decide, by omega, by omega, by rw [h12₁, k₁.rd, k₁.wr]; exact hsrc,
        by rw [hb₁]; exact in_scr (by rw [k₁.wr]; exact hw₈) (by omega),
        by rw [hb₁, h12₁]; exact hsd (by omega)⟩ fun u k₂ f₂ c₂ => WP.block_nil ⟨k₁.trans k₂ |>.mono (by decide), ?_, ?_⟩
    · rw [hb₁, e8, show Layout.laneA k' + (p.n + 32) = Layout.laneA k' + p.n + 32 by omega] at f₂
      exact (f₁.sub (sub2 p.n (by omega))).trans (f₂.sub (sub2 0 (by omega)))
    · rw [hb₁, e8, show Layout.laneA k' + (p.n + 32) = Layout.laneA k' + p.n + 32 by omega] at f₂ c₂
      rw [h12₁, h12, BitVec.add_zero] at c₂
      have hdec : ¬ (lOf p I t₀ k' / 2 ^ z % 2 = 0) := fun h => by simp [h] at hb₀
      simp only [hdec, ↓reduceIte]
      rw [show 2 * p.n = p.n + p.n by omega, Fors.bytesAt_cat, c₂, sig_frame c f₁ (by omega) hso, hA,
        k1 f₂ (by omega) (by omega) (by omega), c₁, hX]
  · obtain ⟨ku, fu, bu⟩ := hu
    have hbu : u.gpr .x19 = S := by rw [ku.get .x19, hb19]
    have hwu : (⟨S, 65536⟩ : Region) ∈ u.wr := by rw [ku.wr]; exact hw₈
    refine MlKem.AArch64.wp_lsr (by decide) fun u₁ o₁' e₁' => MlKem.AArch64.wp_addImm (by decide) fun u₂ o₂' e₂' => ?_
    have hid₂ : u₂.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ (z + 1)) := by
      rw [o₂'.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)), e₁',
        ku.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)), hx₈,
        shr1 _ (by have := Nat.div_le_self (lOf p I t₀ k') (2 ^ z); omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have h10₂ : u₂.gpr .x10 = BitVec.ofNat 64 (z + 1) := by
      rw [e₂', o₁'.get .x23 (idx_ne' k' hk' _ (by decide)),
        ku.get .x23, o₁₈.get .x23, h23, BitVec.ofNat_add_ofNat]
    have hb₂ : u₂.gpr .x19 = S := by
      rw [o₂'.get .x19, o₁'.get .x19 (idx_ne' k' hk' _ (by decide)),
        hbu]
    have hw₂ : (⟨S, 65536⟩ : Region) ∈ u₂.wr := by rw [o₂'.wr, o₁'.wr]; exact hwu
    have hzl : (BitVec.ofNat 64 (z + 1)).toNat = z + 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hF.a; omega)
    have hil : (BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ (z + 1))).toNat = lOf p I t₀ k' / 2 ^ (z + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := Nat.div_le_self (lOf p I t₀ k') (2 ^ (z + 1)); omega)
    refine setFieldR_ok (r := .x10) (by decide) (by rw [h10₂, hzl]; have := hF.a; omega) ⟨by omega, by omega⟩
      (by rw [hb₂]; exact in_scr hw₂ (by omega)) fun u₃ f₃ => ?_
    have hb₃ : u₃.gpr .x19 = S := by rw [f₃.keep.get .x19, hb₂]
    rw [← List.append_nil (Impl.SlhDsa.AArch64.setFieldR _ _ _)]
    refine setFieldR_ok (r := Impl.SlhDsa.AArch64.Verify.idxReg k') (by decide)
      (by rw [f₃.keep.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)), hid₂, hil];
          have := Nat.div_le_self (lOf p I t₀ k') (2 ^ (z + 1)); omega) ⟨by omega, by omega⟩
      (by rw [hb₃]; exact in_scr (by rw [f₃.keep.wr]; exact hw₂) (by omega)) fun u₄ f₄ => WP.block_nil ?_
    have e₃ := f₃.frame; have e₄ := f₄.frame; have b₃ := f₃.bytes; have b₄ := f₄.bytes
    rw [hb₂] at e₃ b₃
    rw [hb₃] at e₄ b₄
    rw [h10₂, hzl] at b₃
    rw [f₃.keep.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)), hid₂, hil] at b₄
    have hm₂ : u₂.mem = u.mem := by rw [o₂'.mem, o₁'.mem]
    rw [hm₂] at e₃
    have hfl : bytesAt u.mem (at' S (Layout.laneA k' + p.n + 16)) 16 = bytesAt t.mem (at' S (Layout.laneA k' + p.n + 16)) 16 := by
      rw [k1 fu (by omega) (by omega) (by omega), hm₈]
    obtain ⟨s₁, s₂⟩ := split16 (length_toByte' 3 4) (length_toByte' _ 4) (hfl.trans hl.fld)
    have hidx₄ : u₄.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ (z + 1)) := by
      rw [f₄.keep.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)),
        f₃.keep.get _ (fun h => idx_n6 k' hk' (by simp only [List.mem_singleton] at h; rw [h]; simp)), hid₂]
    have st : ∀ x l, 16 ≤ x → x + l ≤ 16 + p.n + 16 + 16 → ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + x), l⟩ : Region)],
        ∃ R ∈ [tailA p S k'], Region.Sub r R := fun x l h₁ h₂ =>
      sub1 S (by omega) (by simp only [Layout.strideA]; omega)
    have st' : ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + 32), 2 * p.n⟩ : Region)], ∃ R ∈ [tailA p S k'],
        Region.Sub r R := sub1 S (by omega) (by simp only [Layout.strideA]; omega)
    refine ⟨?_, ?_, hidx₄, ?_, ?_⟩
    · exact (((((o₁₈.keep.trans ku).trans o₁'.keep).trans o₂'.keep).trans f₃.keep).trans f₄.keep).mono (by
        rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
    · rw [hm₈] at fu
      exact ((fu.sub st').trans (e₃.sub (st 24 4 (by omega) (by omega)))).trans (e₄.sub (st 28 4 (by omega) (by omega)))
    · refine fld4 (m₁ := u.mem) (m₂ := u.mem) (by omega) (Frame.refl _ _)
        (by rw [show Layout.laneA k' + p.n + 16 + 8 = Layout.laneA k' + p.n + 24 by omega]; exact e₃)
        (by rw [show Layout.laneA k' + p.n + 16 + 12 = Layout.laneA k' + p.n + 28 by omega]; exact e₄) s₁ s₂
        (by rw [show Layout.laneA k' + p.n + 16 + 8 = Layout.laneA k' + p.n + 24 by omega]; exact b₃)
        (by rw [show Layout.laneA k' + p.n + 16 + 12 = Layout.laneA k' + p.n + 28 by omega]; exact b₄)
    · rw [k1 e₄ (by omega) (by omega) (by omega), k1 e₃ (by omega) (by omega) (by omega), bu]

end VG.Proof.SlhDsa.AArch64.ForsPk
