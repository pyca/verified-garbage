module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: a lane's leaf, and a call of `thash4` on the lanes `A`

A lane's state (`Lane`): its index register, its address's fields
(`FORS_TREE`, `kp`, the height, the index) and its node. The block of a
lane's leaf in `forsLeaves` (`leafLane_ok`): its index `t·2^a + I t` of its
tree `t`, its fields, its message the tree's private key value. A call of
`thash4` on the lanes `A` (`acall_ok`).
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

/-! ## Bytes of `scratch` -/

theorem k1 {m m' : Mem} {S : Addr} {o l q q' : Nat} (hf : Frame [⟨at' S o, l⟩] m m') (h : q + q' ≤ o ∨ o + l ≤ q)
    (h₁ : q + q' ≤ 65536) (h₂ : o + l ≤ 65536) : bytesAt m' (at' S q) q' = bytesAt m (at' S q) q' :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S h h₁ h₂) (by omega)

theorem sub1 (S : Addr) {o l o' l' : Nat} (h₁ : o' ≤ o) (h₂ : o + l ≤ o' + l') :
    ∀ r ∈ [(⟨at' S o, l⟩ : Region)], ∃ R ∈ [(⟨at' S o', l'⟩ : Region)], Region.Sub r R := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub S h₁ h₂⟩

/-- Four fields of 4 bytes, each written after the one before. -/
theorem fld4 {m₁ m₂ m₃ m₄ : Mem} {S : Addr} {d : Nat} (hd : d + 16 ≤ 65536) {A B C D : List Byte}
    (f₂ : Frame [⟨at' S (d + 4), 4⟩] m₁ m₂) (f₃ : Frame [⟨at' S (d + 8), 4⟩] m₂ m₃)
    (f₄ : Frame [⟨at' S (d + 12), 4⟩] m₃ m₄)
    (b₁ : bytesAt m₁ (at' S d) 4 = A) (b₂ : bytesAt m₂ (at' S (d + 4)) 4 = B)
    (b₃ : bytesAt m₃ (at' S (d + 8)) 4 = C) (b₄ : bytesAt m₄ (at' S (d + 12)) 4 = D) :
    bytesAt m₄ (at' S d) 16 = A ++ (B ++ (C ++ D)) := by
  have e₃ : bytesAt m₄ (at' S (d + 8)) 4 = C := (k1 f₄ (by omega) (by omega) (by omega)).trans b₃
  have e₂ : bytesAt m₄ (at' S (d + 4)) 4 = B :=
    (k1 f₄ (by omega) (by omega) (by omega)).trans ((k1 f₃ (by omega) (by omega) (by omega)).trans b₂)
  have e₁ : bytesAt m₄ (at' S d) 4 = A := (k1 f₄ (by omega) (by omega) (by omega)).trans
    ((k1 f₃ (by omega) (by omega) (by omega)).trans ((k1 f₂ (by omega) (by omega) (by omega)).trans b₁))
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, Fors.bytesAt_cat, Fors.bytesAt_cat, Fors.bytesAt_cat,
    show d + 4 + 4 = d + 8 by omega, show d + 8 + 4 = d + 12 by omega, e₁, e₂, e₃, b₄]

/-! ## A lane -/

/-- A lane's fields: the type, `kp`, the height, the index. -/
abbrev ufld (ty kp z i : Nat) : List Byte := toByte ty 4 ++ (toByte kp 4 ++ (toByte z 4 ++ toByte i 4))

/-- Lane `k'` at height `z`, index `i`, node `X`. -/
structure Lane (p : Params) (S : Addr) (kp z i : Nat) (X : List Byte) (t : State) (k' : Nat) : Prop where
  idx : t.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 i
  fld : bytesAt t.mem (at' S (Layout.laneA k' + p.n + 16)) 16 = ufld 3 kp z i
  msg : bytesAt t.mem (at' S (Layout.laneA k' + p.n + 32)) p.n = X

theorem idxReg_ne : ∀ j < 4, ∀ k < 4, j ≠ k →
    Impl.SlhDsa.AArch64.Verify.idxReg j ≠ Impl.SlhDsa.AArch64.Verify.idxReg k := by decide

theorem idxReg_cs : ∀ j < 4, Impl.SlhDsa.AArch64.Verify.idxReg j ∈ preserved ∧
    Impl.SlhDsa.AArch64.Verify.idxReg j ≠ .x30 ∧
    Impl.SlhDsa.AArch64.Verify.idxReg j ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x19, .x20, .x21, .x22,
      .x23, .x28] := by decide

/-- Lane `j`'s facts past a step that writes only lane `k`'s tail and keeps `j`'s index register. -/
theorem Lane.keep {S : Addr} {kp z i : Nat} {X : List Byte} {t t' : State} {j k : Nat} (hn : p.n ≤ 32)
    (h : Lane p S kp z i X t j) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hr : t'.gpr (Impl.SlhDsa.AArch64.Verify.idxReg j) = t.gpr (Impl.SlhDsa.AArch64.Verify.idxReg j))
    (hf : Frame [tailA p S k] t.mem t'.mem) : Lane p S kp z i X t' j := by
  have := ForsPk.laneA_eq j
  have := ForsPk.laneA_eq k
  refine ⟨by rw [hr, h.idx], ?_, ?_⟩
  · rw [k1 hf (by simp only [Layout.strideA]; omega) (by omega) (by simp only [Layout.strideA]; omega), h.fld]
  · rw [k1 hf (by simp only [Layout.strideA]; omega) (by omega) (by simp only [Layout.strideA]; omega), h.msg]

/-- Bytes of the signature, past a frame in `scratch`. -/
theorem sig_frame {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {m m' : Mem} {o l : Nat}
    (hf : Frame [⟨at' S o, l⟩] m m') (hol : o + l ≤ 65536) {off n : Nat} (h : off + n ≤ p.forsSigLen) :
    bytesAt m' (sig + BitVec.ofNat 64 off) n = bytesAt m (sig + BitVec.ofNat 64 off) n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (c.sss.sub_left (Offset.sub_base sig h)).sub_right (Offset.sub_base S hol)) (by have := c.sfit; omega)

/-! ## A lane's leaf -/

/-- Lane `k`'s leaf index in the group from `t₀`. -/
abbrev lOf (p : Params) (I : Nat → Nat) (t₀ k' : Nat) : Nat := tOf p t₀ k' * 2 ^ p.a + I (tOf p t₀ k')

/-- Lane `k`'s private key value. -/
abbrev skOf (p : Params) (m : Mem) (sig : Addr) (t₀ k' : Nat) : List Byte :=
  bytesAt m (sig + BitVec.ofNat 64 (sigOff p (tOf p t₀ k'))) p.n

/-- The block of lane `k`'s leaf. -/
abbrev leafL (p : Params) (k' : Nat) : List Instr :=
  Impl.SlhDsa.AArch64.Verify.treeT p k' ++
      [.lsl .x .x11 .x10 3, .add .x .x11 .x11 .x19, .ldr .x .x11 .x11 Layout.oFidx, .lsl .x .x13 .x10 p.a,
        .add .x (Impl.SlhDsa.AArch64.Verify.idxReg k') .x11 .x13] ++ Impl.SlhDsa.AArch64.Verify.treeSig p ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).adrsOff + 16) 3 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).adrsOff + 20) .x20 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).adrsOff + 24) 0 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).adrsOff + 28)
        (Impl.SlhDsa.AArch64.Verify.idxReg k') ++
      Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).msgOff) .x12 0 (p.n / 8)

theorem shl_ofNat (x k : Nat) : BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- The registers a lane's block may change. -/
abbrev laneRegs (k' : Nat) : List Reg :=
  [.x9, .x10, .x11, .x12, .x13, .x14, .x15, Impl.SlhDsa.AArch64.Verify.idxReg k']

theorem leafLane_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) {k' t₀ : Nat} (hk' : k' < 4) (ht₀ : t₀ < 2 ^ 32) {t : State}
    (hK : FK p σ S sig pk a I t) (h22 : t.gpr .x22 = BitVec.ofNat 64 t₀) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep (laneRegs k') t t' → Frame [tailA p S k'] t.mem t'.mem →
      Lane p S (σ.gpr .x2).toNat 0 (lOf p I t₀ k') (skOf p σ.mem sig t₀ k') t' k' → WP isa (.block is) t' Q) :
    WP isa (.block (leafL p k' ++ is)) t Q := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  have hL := ForsPk.laneA_eq k'
  have hw : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hK.wr]; exact c.scr
  obtain ⟨T, eT⟩ : ∃ T, T = tOf p t₀ k' := ⟨_, rfl⟩
  have hT : T < p.k := by rw [eT]; exact tOf_lt hF _ _
  have hIT := hIa T hT
  have hLT := hF.leaf hT hIT
  simp only [leafL, Impl.SlhDsa.AArch64.Shake.layout, Layout.adrsOff, Layout.msgOff, List.append_assoc,
    List.cons_append, List.nil_append]
  refine treeT_ok hF hk' ht₀ h22 fun t₁ o₁ e₁ => ?_
  rw [← eT] at e₁
  refine MlKem.AArch64.wp_lsl (by decide) fun t₂ o₂ e₂ => MlKem.AArch64.wp_add fun t₃ o₃ e₃ => ?_
  have ha₃ : t₃.gpr .x11 + BitVec.ofNat 64 Layout.oFidx = at' S (Layout.oFidx + 8 * T) := by
    rw [e₃, o₂.get .x19, o₁.get .x19, hK.x19, e₂, e₁, shl_ofNat, BitVec.add_comm _ S, BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_comm, Nat.mul_comm 8 T]
  refine MlKem.AArch64.wp_ldrx (by rw [oFidx_eq]; decide) ha₃
    (by rw [o₃.rd, o₂.rd, o₁.rd, o₃.wr, o₂.wr, o₁.wr]; exact in_scr' hw (by rw [oFidx_eq]; have := hF.k; omega))
    fun t₄ o₄ e₄ => ?_
  rw [o₃.mem, o₂.mem, o₁.mem, hK.fidx T hT] at e₄
  refine MlKem.AArch64.wp_lsl (by have := hF.a; omega) fun t₅ o₅ e₅ => MlKem.AArch64.wp_add fun t₆ o₆ e₆ => ?_
  have hx₆ : t₆.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (lOf p I t₀ k') := by
    rw [e₆, o₅.get .x11, e₄, e₅, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, shl_ofNat, ← BitVec.ofNat_add,
      Nat.add_comm]
    show _ = BitVec.ofNat 64 (tOf p t₀ k' * 2 ^ p.a + I (tOf p t₀ k'))
    rw [← eT]
  have h10₆ : t₆.gpr .x10 = BitVec.ofNat 64 T := by
    rw [o₆.get .x10 (by rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
      o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁]
  have hg₆ : ∀ r ∈ [Reg.x19, .x20, .x21], t₆.gpr r = t.gpr r := by
    have hn : ∀ r ∈ [Reg.x19, .x20, .x21], r ∉ laneRegs k' := by
      rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
    intro r hr
    exact ((o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono (by
      rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)).get r (hn r hr)
  refine treeSig_ok hF h10₆ (by rw [hg₆ .x21 (by simp), hK.x21]) fun t₇ o₇ e₇ => ?_
  have hb₇ : t₇.gpr .x19 = S := by rw [o₇.get .x19, hg₆ .x19 (by simp), hK.x19]
  have hw₇ : (⟨S, 65536⟩ : Region) ∈ t₇.wr := by rw [o₇.wr, o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact hw
  have hdA : ∀ x, x ≤ 28 → (Layout.laneA k' + p.n + x) % 4 = 0 → (Layout.laneA k' + p.n + x) % 4 = 0 ∧
      Layout.laneA k' + p.n + x < 16384 := fun x hx h => ⟨h, by omega⟩
  refine setField_ok (by decide) (hdA 16 (by decide) (by omega)) (by rw [hb₇]; exact in_scr hw₇ (by omega))
    fun t₈ f₈ => ?_
  have hb₈ : t₈.gpr .x19 = S := by rw [f₈.keep.get .x19, hb₇]
  have hw₈ : (⟨S, 65536⟩ : Region) ∈ t₈.wr := by rw [f₈.keep.wr]; exact hw₇
  have hkp₈ : t₈.gpr .x20 = σ.gpr .x2 := by rw [f₈.keep.get .x20, o₇.get .x20, hg₆ .x20 (by simp), hK.x20]
  refine setFieldR_ok (r := .x20) (by decide) (by rw [hkp₈]; exact c.kp) (hdA 20 (by decide) (by omega))
    (by rw [hb₈]; exact in_scr hw₈ (by omega)) fun t₉ f₉ => ?_
  have hb₉ : t₉.gpr .x19 = S := by rw [f₉.keep.get .x19, hb₈]
  have hw₉ : (⟨S, 65536⟩ : Region) ∈ t₉.wr := by rw [f₉.keep.wr]; exact hw₈
  refine setField_ok (by decide) (hdA 24 (by decide) (by omega)) (by rw [hb₉]; exact in_scr hw₉ (by omega))
    fun t₁₀ f₁₀ => ?_
  have hb₁₀ : t₁₀.gpr .x19 = S := by rw [f₁₀.keep.get .x19, hb₉]
  have hw₁₀ : (⟨S, 65536⟩ : Region) ∈ t₁₀.wr := by rw [f₁₀.keep.wr]; exact hw₉
  have hcs : ∀ r ∈ [Reg.x9], Impl.SlhDsa.AArch64.Verify.idxReg k' ∉ [r] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have hx₁₀ : t₁₀.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (lOf p I t₀ k') := by
    rw [f₁₀.keep.get _ (hcs _ (List.mem_singleton_self _)), f₉.keep.get _ (hcs _ (List.mem_singleton_self _)),
      f₈.keep.get _ (hcs _ (List.mem_singleton_self _)),
      o₇.get _ (by rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide), hx₆]
  have hLT' : lOf p I t₀ k' < 2 ^ 32 := by
    show tOf p t₀ k' * 2 ^ p.a + I (tOf p t₀ k') < 2 ^ 32
    rw [← eT]; exact hLT
  have hlo : (BitVec.ofNat 64 (lOf p I t₀ k')).toNat = lOf p I t₀ k' := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine setFieldR_ok (r := Impl.SlhDsa.AArch64.Verify.idxReg k') (by decide) (by rw [hx₁₀, hlo]; exact hLT')
    (hdA 28 (by decide) (by omega)) (by rw [hb₁₀]; exact in_scr hw₁₀ (by omega)) fun t₁₁ f₁₁ => ?_
  have hb₁₁ : t₁₁.gpr .x19 = S := by rw [f₁₁.keep.get .x19, hb₁₀]
  have hw₁₁ : (⟨S, 65536⟩ : Region) ∈ t₁₁.wr := by rw [f₁₁.keep.wr]; exact hw₁₀
  have h12₁₁ : t₁₁.gpr .x12 = sig + BitVec.ofNat 64 (sigOff p T) := by
    rw [f₁₁.keep.get .x12, f₁₀.keep.get .x12, f₉.keep.get .x12, f₈.keep.get .x12, e₇]
  have hrd₁₁ : t₁₁.rd = σ.rd := by
    rw [f₁₁.keep.rd, f₁₀.keep.rd, f₉.keep.rd, f₈.keep.rd, o₇.rd, o₆.rd, o₅.rd, o₄.rd, o₃.rd, o₂.rd, o₁.rd, hK.rd]
  have hsl := forsSig_le hT (j := 0) (Nat.zero_le _)
  have hso : sigOff p T + p.n ≤ p.forsSigLen := by simp only [sigOff]; omega
  have hsf := c.sfit
  have hn16 := hF.n16
  have e8 : 8 * (p.n / 8) = p.n := by omega
  refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA k' + (p.n + 32)) (d₁ := 0) (w := p.n / 8)
    ⟨by decide, by decide, by omega, by omega,
      ⟨_, List.mem_append_left _ (by rw [hrd₁₁]; exact c.sigR), by
        rw [h12₁₁, BitVec.add_zero, e8]; exact Offset.contains_base sig hso (by omega)⟩,
      by rw [hb₁₁]; exact in_scr hw₁₁ (by omega),
      by rw [hb₁₁, h12₁₁, BitVec.add_zero, e8]
         exact (c.sss.sub_left (Offset.sub_base sig hso)).sub_right (Offset.sub_base S (by omega)) |>.symm⟩
    fun t₁₂ k₁₂ f₁₂ c₁₂ => ?_
  rw [hb₁₁, e8, show Layout.laneA k' + (p.n + 32) = Layout.laneA k' + p.n + 32 by omega] at f₁₂ c₁₂
  rw [h12₁₁, BitVec.add_zero] at c₁₂
  have e₈ := f₈.frame; have e₉ := f₉.frame; have e₁₀ := f₁₀.frame; have e₁₁ := f₁₁.frame
  have b₈ := f₈.bytes; have b₉ := f₉.bytes; have b₁₀ := f₁₀.bytes; have b₁₁ := f₁₁.bytes
  rw [hb₇] at e₈ b₈
  rw [hb₈] at e₉ b₉
  rw [hkp₈] at b₉
  rw [hb₉] at e₁₀ b₁₀
  rw [hb₁₀] at e₁₁ b₁₁
  rw [hx₁₀, hlo] at b₁₁
  have hm₇ : t₇.mem = t.mem := by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  rw [hm₇] at e₈
  have dS : ∀ x, x + 4 ≤ 16 → Layout.laneA k' + p.n + 16 + x + 4 ≤ 65536 := fun x hx => by omega
  have fl : bytesAt t₁₁.mem (at' S (Layout.laneA k' + p.n + 16)) 16 = ufld 3 (σ.gpr .x2).toNat 0 (lOf p I t₀ k') :=
    fld4 (by omega) (by rw [show Layout.laneA k' + p.n + 16 + 4 = Layout.laneA k' + p.n + 20 by omega]; exact e₉)
      (by rw [show Layout.laneA k' + p.n + 16 + 8 = Layout.laneA k' + p.n + 24 by omega]; exact e₁₀)
      (by rw [show Layout.laneA k' + p.n + 16 + 12 = Layout.laneA k' + p.n + 28 by omega]; exact e₁₁)
      b₈ (by rw [show Layout.laneA k' + p.n + 16 + 4 = Layout.laneA k' + p.n + 20 by omega]; exact b₉)
      (by rw [show Layout.laneA k' + p.n + 16 + 8 = Layout.laneA k' + p.n + 24 by omega]; exact b₁₀)
      (by rw [show Layout.laneA k' + p.n + 16 + 12 = Layout.laneA k' + p.n + 28 by omega]; exact b₁₁)
  have hsk : bytesAt t₁₁.mem (sig + BitVec.ofNat 64 (sigOff p T)) p.n = skOf p σ.mem sig t₀ k' := by
    rw [sig_frame c e₁₁ (by omega) hso, sig_frame c e₁₀ (by omega) hso, sig_frame c e₉ (by omega) hso,
      sig_frame c e₈ (by omega) hso, hK.sig hF c hso, skOf, ← eT]
  have hT16 : Frame [tailA p S k'] t.mem t₁₂.mem := by
    have st : ∀ x l, 16 ≤ x → x + l ≤ 16 + p.n + 16 + 16 → ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + x), l⟩ : Region)],
        ∃ R ∈ [tailA p S k'], Region.Sub r R := fun x l h₁ h₂ =>
      sub1 S (by omega) (by simp only [Layout.strideA]; omega)
    exact ((((e₈.sub (st 16 4 (by omega) (by omega))).trans
      (e₉.sub (st 20 4 (by omega) (by omega)))).trans (e₁₀.sub (st 24 4 (by omega) (by omega)))).trans
      (e₁₁.sub (st 28 4 (by omega) (by omega)))).trans (f₁₂.sub (st 32 p.n (by omega) (by omega)))
  refine K t₁₂ ?_ hT16 ⟨?_, ?_, ?_⟩
  · exact ((o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
      o₇.keep)))))).trans ((f₈.keep.trans (f₉.keep.trans (f₁₀.keep.trans f₁₁.keep))).trans k₁₂)).mono (by
      rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
  · rw [k₁₂.get _ (by rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
      f₁₁.keep.get _ (hcs _ (List.mem_singleton_self _)), hx₁₀]
  · rw [k1 f₁₂ (by omega) (by omega) (by omega), fl]
  · rw [c₁₂, hsk]

/-! ## `FK` past a call -/

/-- `FK` past a step that keeps `x19`–`x21`, `x28`, `sp`, the permissions and
the low halves of `v8`–`v15`, and writes only `gw`. -/
theorem FK.keep' {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {t t' : State} (hF : FP p)
    (h : FK p σ S sig pk a I t) (cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x28], t'.gpr r = t.gpr r) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hf : Frame (gw p S) t.mem t'.mem) : FK p σ S sig pk a I t' := by
  have hn := hF.n32
  have hkn := hF.kn
  have hk35 := hF.k
  refine ⟨by rw [cs .x19 (by simp), h.x19], by rw [cs .x20 (by simp), h.x20], by rw [cs .x21 (by simp), h.x21],
    by rw [cs .x28 (by simp), h.x28], by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr],
    fun r hr => by rw [hv r hr, h.vcs r hr], env_gw hF h.env hf, ?_, fun i hi => ?_, ?_⟩
  · refine h.saved.frame_in (lo := 1280) (n := 80) slotsF_in hf fun r hr => ?_
    exact gw_disj hF S (by simp only [workUsed]; omega) (by omega) (fun j hj => by omega) (by omega) r hr
  · rw [readW_frame hf fun r hr => gw_disj hF S (by rw [oFidx_eq]; simp only [workUsed]; omega)
      (by rw [oFidx_eq]; omega) (fun j hj => by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega) r hr, h.fidx i hi]
  · exact h.frame.trans (hf.sub (gw_changes hF S))

/-- The parts of `gw` but the roots. -/
abbrev gwL (p : Params) (S : Addr) : List Region := ⟨S, workUsed⟩ :: (List.range 4).map (tailA p S)

theorem gwL_gw (S : Addr) : ∀ r ∈ gwL p S, r ∈ gw p S := fun _ hr => List.mem_append_left _ hr

/-! ## A call of `thash4` on the lanes `A` -/

/-- What a call of `thash4` on the lanes `A`, for messages of `len` bytes, leaves. -/
structure ACall (p : Params) (S : Addr) (len : Nat) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r
  vcs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  out : ∀ j < 4, bytesAt t'.mem (at' S (Layout.laneA j + p.n + 32)) p.n =
    shake256 (bytesAt t.mem (at' S (Layout.laneA j)) len) p.n
  frame : Frame (Wots4.t4ch p.n S Layout.oA Layout.strideA) t.mem t'.mem

theorem acall_ok (hz : Sz p) (T : Thash4Impl p.n) (name : String) {S : Addr} {t : State} {Q : State → Prop}
    {len : Nat} (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ 128)
    (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (K : ∀ t', ACall p S len t t' → Q t') :
    WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA len) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  unfold Impl.SlhDsa.AArch64.thashCall
  refine WP.seq ?_
  rw [Wots4.thashArgs_eq ⟨p.n, p.len⟩ (o := Layout.oA) (by decide)]
  refine TreeBase.wp_addi (imm := Layout.oA) (by decide) fun t₂ e₂ => TreeBase.wp_movz fun t₃ e₃ =>
    TreeBase.wp_movz fun t₄ e₄ => TreeBase.wp_addi (imm := p.n + 32) (by omega) fun t₅ e₅ =>
    TreeBase.wp_mov fun t₆ e₆ => WP.block_nil ?_
  have hm₆ : t₆.mem = t.mem := by rw [e₆.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem]
  have g0 : t₆.gpr .x0 = at' S Layout.oA := by
    rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19]
  refine Wots4.t4call_ok T name (s := t₆) (S := S) (o := Layout.oA) (st := Layout.strideA) (len := len)
    (by rw [e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr]; exact hw) hfit (by decide) (by decide) g0
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.gpr, Wots4.movz_ofNat (by decide)])
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.gpr, Wots4.movz_ofNat (by omega)])
    (by rw [e₆.other _ (by decide), e₅.gpr, e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19,
        TreeBase.at_add, Nat.add_assoc])
    (by rw [e₆.gpr, e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), h19])
    hlp hlm (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
    fun t₇ r₇ w₇ sp₇ g₇ v₇ o₇ f₇ => K t₇ ⟨by rw [r₇, e₆.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd],
      by rw [w₇, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr], by rw [sp₇, e₆.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp],
      fun r hr h30 => ?_, fun r hr => by rw [v₇ r hr, e₆.v, e₅.v, e₄.v, e₃.v, e₂.v], fun j hj => ?_,
      by rw [← hm₆]; exact f₇⟩
  · have hr' : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rw [g₇ r hr h30, e₆.other _ hr'.2.2.2.2, e₅.other _ hr'.2.2.2.1, e₄.other _ hr'.2.2.1, e₃.other _ hr'.2.1,
      e₂.other _ hr'.1]
  · have := o₇ j hj
    rw [hm₆, show Layout.oA + j * Layout.strideA = Layout.laneA j by
      simp only [Layout.laneA, Layout.strideA, Layout.oA]; omega] at this
    exact this

theorem t4ch_gw (hF : FP p) (S : Addr) : ∀ r ∈ Wots4.t4ch p.n S Layout.oA Layout.strideA, ∃ R ∈ gwL p S,
    Region.Sub r R := by
  have hn := hF.n32
  intro r hr
  simp only [Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · refine ⟨tailA p S j, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), ?_⟩
    simp only [tailA, laneA_eq, Layout.oA, Layout.strideA]
    exact Offset.sub S (by omega) (by omega)
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩

theorem cs_of : ∀ r ∈ [Reg.x19, .x20, .x21, .x28], r ∈ preserved ∧ r ≠ .x30 := by decide

/-- `FK` past such a call. -/
theorem FK.acall {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {t t' : State} (hF : FP p)
    (h : FK p σ S sig pk a I t) {len : Nat} (hc : ACall p S len t t') : FK p σ S sig pk a I t' :=
  h.keep' hF (fun r hr => hc.cs r (cs_of r hr).1 (cs_of r hr).2) hc.sp hc.rd hc.wr hc.vcs
    ((hc.frame.sub (t4ch_gw hF S)).mono (gwL_gw S))

/-- Lane `j`'s message for `thash4`: `PK.seed`, `a16`, the fields, `M`. -/
theorem lane_msg {m : Mem} {S : Addr} {pk a : List Byte} (henv : Env p m S pk a) {j : Nat} (hj : j < 4)
    {fl M : List Byte} {L : Nat} (hf : bytesAt m (at' S (Layout.laneA j + p.n + 16)) 16 = fl)
    (hM : bytesAt m (at' S (Layout.laneA j + p.n + 32)) L = M) :
    bytesAt m (at' S (Layout.laneA j)) (p.n + 32 + L) = pk ++ a ++ fl ++ M := by
  rw [show p.n + 32 + L = p.n + (16 + (16 + L)) by omega, Fors.bytesAt_cat, Fors.bytesAt_cat, Fors.bytesAt_cat,
    henv.adrsA j hj, show Layout.laneA j + p.n + 16 + 16 = Layout.laneA j + p.n + 32 by omega, hf, hM,
    ← henv.seedA j hj]
  simp only [List.append_assoc]

end VG.Proof.SlhDsa.AArch64.ForsPk
