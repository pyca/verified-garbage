module

-- separate module: a step of a group, which the groups' proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssGroup
public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsBase
public import VerifiedGarbage.Proof.SlhDsa.VerifySpec
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: a step of a group of chains

Step `j` of a group (`stepBody`): each lane's hash address set to `j`, the
four `F`s, and each lane whose digit is above `j` given its signature value
back (`step_ok`): each lane's value runs as `restoreRun` does
(`Proof/SlhDsa/VerifySpec.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.SlhDsa (adrsOf)
open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_subr wp_lsr wp_movz wp_mov wp_addi wp_subi)

variable {p : Params}

/-- The value of a lane after the steps from `t₀` up to `j`. -/
def V (p : Params) (pk a : List Byte) (idx c d : Nat) (X : List Byte) (t₀ j : Nat) : List Byte :=
  (List.range (j - t₀)).foldl (fun v j' => if t₀ + j' < d then X else F p pk (adrsOf a 0 idx c (t₀ + j')) v) X

theorem V_succ (p : Params) (pk a : List Byte) (idx c d : Nat) (X : List Byte) {t₀ j : Nat} (h : t₀ ≤ j) :
    V p pk a idx c d X t₀ (j + 1) = if j < d then X else F p pk (adrsOf a 0 idx c j) (V p pk a idx c d X t₀ j) := by
  simp only [V]
  rw [show j + 1 - t₀ = (j - t₀) + 1 by omega_using [h], List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, show t₀ + (j - t₀) = j by omega_using [h]]

/-- The fields of lane `k`'s address but its hash address. -/
structure LaneF (p : Params) (m : Mem) (S : Addr) (k idx c : Nat) : Prop where
  ty : bytesAt m (at' S (Layout.laneA k + p.n + 16)) 4 = toByte 0 4
  kp : bytesAt m (at' S (Layout.laneA k + p.n + 20)) 4 = toByte idx 4
  ch : bytesAt m (at' S (Layout.laneA k + p.n + 24)) 4 = toByte c 4

/-- The lanes `A` and `work`, which a step writes. -/
def aW (p : Params) (S : Addr) : List Region :=
  ⟨S, workUsed⟩ :: (List.range 4).map fun k => ⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩

theorem aW_sub (hz : Sz p) {S : Addr} {k o l : Nat} (hk : k < 4) (h₁ : Layout.laneA k + p.n + 16 ≤ o)
    (h₂ : o + l ≤ Layout.laneA k + Layout.strideA) : ∃ R ∈ aW p S, Region.Sub ⟨at' S o, l⟩ R := by
  have hn32 := hz.n32
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩),
    Offset.sub S h₁ (by simp only [Layout.strideA] at h₂ ⊢; omega)⟩

/-- Step `j` of group `g`, whose first step is `t₀`, from the group's state `tg`. -/
structure SI (p : Params) (σ tg : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (g t₀ j : Nat)
    (t : State) : Prop where
  xk : XK p σ S sig pk a D t
  x22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g)
  x23 : t.gpr .x23 = BitVec.ofNat 64 j
  x24 : t.gpr .x24 = BitVec.ofNat 64 t₀
  fields : ∀ k < 4, LaneF p t.mem S k (σ.gpr .x1).toNat (cOf p g k)
  msg : ∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
    V p pk a (σ.gpr .x1).toNat (cOf p g k) (D.getD (cOf p g k) 0)
      (bytesAt σ.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n) t₀ j
  frame : Frame (aW p S) tg.mem t.mem

/-! ## The hash addresses -/

/-- The hash addresses' fields. -/
def hW (p : Params) (S : Addr) : List Region :=
  (List.range 4).map fun k => ⟨at' S (Layout.laneA k + p.n + 28), 4⟩

/-- The four lanes' hash addresses set to `x23 = j`. -/
theorem hfields_ok (hz : Sz p) {t : State} {S : Addr} (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    {j : Nat} (hj : j < 2 ^ 32) (h23 : t.gpr .x23 = BitVec.ofNat 64 j) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x9] t t' → Frame (hW p S) t.mem t'.mem →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 28)) 4 = toByte j 4) → WP isa (.block is) t' Q) :
    WP isa (.block ((List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.setFieldR .x19
      (Layout.laneA k + p.n + 28) .x23) ++ is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  refine wp_rangeFlatMap (P := fun i u => Keep [.x9] t u ∧ Frame (hW p S) t.mem u.mem ∧
      ∀ k < i, bytesAt u.mem (at' S (Layout.laneA k + p.n + 28)) 4 = toByte j 4) 4
    ⟨Keep.refl _ _, Frame.refl _ _, fun k hk => absurd hk (by omega)⟩ (fun i hi u is' ⟨ku, fu, bu⟩ k' => ?_)
    fun u ⟨ku, fu, bu⟩ => K u ku fu bu
  have hjv : (u.gpr .x23).toNat = j := by rw [ku.get .x23, h23, BitVec.toNat_ofNat]; omega_using [hj]
  refine setFieldR_ok (b := .x19) (r := .x23) (by decide) (by rw [hjv]; exact hj)
    ⟨by rw [eA]; omega, by rw [eA]; omega⟩ (by rw [ku.get .x19, h19, ku.wr]; exact in_scr hw (by rw [eA]; omega))
    fun u' fp => k' u' ⟨(ku.trans fp.keep).mono (by simp), ?_, fun k hk => ?_⟩
  · rw [ku.get .x19, h19] at fp
    exact fu.trans (fp.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · have fb := fp.bytes
    have fr := fp.frame
    rw [ku.get .x19, h19, hjv] at fb
    rw [ku.get .x19, h19] at fr
    by_cases e : k = i
    · subst e; exact fb
    · rw [TreeBase.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (by rw [eA, eA]; omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by decide)]
      exact bu k (by omega)

/-! ## The call of `thash4` on the lanes `A` -/

/-- `thashCall` on the lanes `A`, with messages of `len` bytes. -/
theorem thA_ok (hz : Sz p) {n : Nat} (hn : n = p.n) (T : Thash4Impl n) (name : String) {t : State} {S : Addr}
    (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    {len : Nat} (hl : len = 2 * p.n + 32 ∨ len = 3 * p.n + 32) {Q : State → Prop}
    (K : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        shake256 (bytesAt t.mem (at' S (Layout.laneA k)) len) p.n) →
      Frame (Wots4.t4ch p.n S Layout.oA Layout.strideA) t.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA len) t Q := by
  subst hn
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hn16 := hz.n16
  have hlen : len < 65536 := by omega_using [hl, hn32]
  refine WP.seq (WP.mono (Q := fun (u : State) => u.gpr .x0 = at' S Layout.oA ∧ u.gpr .x1 = BitVec.ofNat 64 Layout.strideA ∧
      u.gpr .x2 = BitVec.ofNat 64 len ∧ u.gpr .x3 = at' S (Layout.oA + p.n + 32) ∧ u.gpr .x4 = S ∧
      Only [.x0, .x1, .x2, .x3, .x4] t u) ?_ ?_)
  · simp only [Impl.SlhDsa.AArch64.thashArgs, Impl.SlhDsa.AArch64.lea, show Layout.oA < 4096 by decide, ↓reduceIte,
      List.cons_append, List.nil_append]
    refine MlKem.AArch64.wp_addImm (by decide) fun u₁ o₁ e₁ => MlKem.AArch64.wp_movz fun u₂ o₂ e₂ =>
      MlKem.AArch64.wp_movz fun u₃ o₃ e₃ => MlKem.AArch64.wp_addImm (by simp only [Layout.msgOff]; omega)
      fun u₄ o₄ e₄ => MlKem.AArch64.wp_addImm (by decide) fun u₅ o₅ e₅ => MlKem.AArch64.wp_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).mono (by simp)⟩
    · rw [o₅.get .x0, o₄.get .x0, o₃.get .x0, o₂.get .x0, e₁, h19]
    · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, e₂, imm16 (by decide)]
    · rw [o₅.get .x2, o₄.get .x2, e₃, imm16 hlen]
    · rw [o₅.get .x3, e₄, o₃.get .x0, o₂.get .x0, e₁, h19, addr_add]; rfl
    · rw [e₅, BitVec.add_zero, o₄.get .x19, o₃.get .x19, o₂.get .x19, o₁.get .x19, h19]
  · intro u ⟨u0, u1, u2, u3, u4, ou⟩
    refine Wots4.t4call_ok T name (S := S) (o := Layout.oA) (st := Layout.strideA) (len := len)
      (by rw [ou.wr]; exact hw) hfit (by decide) (by decide) u0 u1 u2 u3 u4 (by omega_using [hl])
      (by omega_using [hl, hn8]) (by simp only [Layout.strideA]; omega_using [hl, hn32])
      (by simp only [Layout.strideA]; omega_using [hn32]) fun t' r' w' sp' g' v' b' f' => K t' (by rw [r', ou.rd])
      (by rw [w', ou.wr]) (by rw [sp', ou.sp]) (fun r hr h30 => by
        rw [g' r hr h30, ou.gpr r (by revert r; decide)]) (fun r hr => by rw [v' r hr, ou.vcs r hr])
      (fun k hk => ?_) (by rw [ou.mem] at f'; exact f')
    have := b' k hk
    rw [ou.mem, show Layout.oA + k * Layout.strideA = Layout.laneA k by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega] at this
    exact this

/-! ## A lane's signature value back -/

/-- `chainSig` and the copy of chain `c`'s signature value to lane `k`'s message. -/
theorem sigCopy_ok (hz : Sz p) {k c : Nat} (hk : k < 4) (hc : c < p.len) {t : State} {S sig : Addr}
    (hI : LaneIn p S sig t) (h10 : t.gpr .x10 = BitVec.ofNat 64 c) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x12, .x13, .x14] t t' → Frame [⟨at' S (Layout.laneA k + p.n + 32), p.n⟩] t.mem t'.mem →
      bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt t.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n →
      WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainSig p ++
      Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k + (p.n + 32)) .x12 0 (p.n / 8) ++ is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hl := hz.len
  have eA : Layout.laneA k = 3136 + 128 * k := rfl
  simp only [Impl.SlhDsa.AArch64.Verify.chainSig, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun t₅ u₅ => mulN_ok hz.nv (r := .x12) (tmp := .x13) (by decide) fun t₆ o₆ e₆ =>
    TreeBase.wp_addr fun t₇ u₇ => ?_
  have e12 : t₇.gpr .x12 = sig + BitVec.ofNat 64 (c * p.n) := by
    rw [u₇.gpr, e₆, u₅.gpr, h10, o₆.get .x21, u₅.other _ (by decide), hI.x21, ← BitVec.ofNat_mul, BitVec.add_comm]
  have hcn : c * p.n + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', ← Nat.succ_mul]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (show c + 1 ≤ p.len by omega_using [hc])) (Nat.le_add_right _ _)
  have hcn64 : c * p.n < 2 ^ 64 := by
    have : c * p.n ≤ 67 * 32 := Nat.mul_le_mul (by omega_using [hc, hl, hn32]) hn32
    omega_using [this]
  have g7 : t₇.gpr .x19 = S := by rw [u₇.other _ (by decide), o₆.get .x19, u₅.other _ (by decide), hI.x19]
  have w7 : t₇.wr = t.wr := by rw [u₇.wr, o₆.wr, u₅.wr]
  have r7 : t₇.rd = t.rd := by rw [u₇.rd, o₆.rd, u₅.rd]
  have m7 : t₇.mem = t.mem := by rw [u₇.mem, o₆.mem, u₅.mem]
  have h8n : 8 * (p.n / 8) = p.n := by omega_using [hn8]
  have dS : Region.Disjoint ⟨at' S (Layout.laneA k + (p.n + 32)), p.n⟩ ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ :=
    (hI.dsig.symm.sub_left (Offset.sub_base S (by rw [eA]; omega))).sub_right (Offset.sub_base sig hcn)
  refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA k + (p.n + 32)) (d₁ := 0) (w := p.n / 8)
    ⟨by decide, by decide, ⟨by decide, by omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
      (by rw [e12, BitVec.add_zero, r7, w7, h8n]
          exact ⟨_, List.mem_append_left _ hI.insig, Offset.contains_base sig hcn hcn64⟩),
      (by rw [g7, w7, h8n]; exact in_scr hI.scr (by rw [eA]; omega)),
      (by rw [g7, e12, BitVec.add_zero, h8n]; exact dS)⟩ fun t₈ k₈ fr₈ b₈ => ?_
  rw [h8n, g7, m7, show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega] at fr₈
  rw [e12, BitVec.add_zero, h8n, g7, m7, show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega] at b₈
  exact K t₈ (((((upOnly u₅).keep.trans o₆.keep).trans (upOnly u₇).keep).trans k₈).mono (by simp)) fr₈ b₈

/-- `restoreLane k` after step `j`: lane `k`'s message is its signature value
back if its digit is above `j`. -/
theorem restoreLane_ok (hz : Sz p) {g k j : Nat} (hg : 4 * g < p.len) (hk : k < 4) (hj : j < 16) {t : State}
    {S sig : Addr} (hI : LaneIn p S sig t) (h22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g))
    (h23 : t.gpr .x23 = BitVec.ofNat 64 j) {Q : State → Prop}
    (K : ∀ t', Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15] t t' →
      Frame [⟨at' S (Layout.laneA k + p.n + 32), p.n⟩] t.mem t'.mem →
      bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        (if j < digitAt t.mem S (cOf p g k) then bytesAt t.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n
          else bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n) → Q t') :
    WP isa (Impl.SlhDsa.AArch64.Verify.restoreLane p k) t Q := by
  have hl := hz.len
  have hn32 := hz.n32
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  refine WP.seq ?_
  refine chainOf_ok hz hg hk hI.x19 h22 hI.scr fun t₁ o₁ c₁ d₁ => wp_subr fun t₂ u₂ => wp_lsr (sh := 63) (by decide)
    fun t₃ u₃ => MlKem.AArch64.wp_nil ?_
  have hd16 : digitAt t.mem S (cOf p g k) < 2 ^ 63 := by
    have := (t.mem (at' S (Layout.oDigits + cOf p g k))).isLt; simp only [digitAt]; omega_using [this]
  have v13 : t₃.gpr .x13 = BitVec.ofNat 64 (if j < digitAt t.mem S (cOf p g k) then 1 else 0) := by
    rw [u₃.gpr, u₂.gpr, o₁.get .x23, h23, d₁, lt_bit (by omega_using [hj]) hd16]
  have K3 : Keep [.x10, .x13, .x14, .x15, .x11, .x13, .x13] t t₃ := (o₁.keep.trans (upOnly u₂).keep).trans (upOnly u₃).keep
  have m3 : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, o₁.mem]
  have hI3 : LaneIn p S sig t₃ := ⟨by rw [K3.get .x19, hI.x19], by rw [K3.get .x21, hI.x21],
    by rw [K3.get .x20]; exact hI.x20, by rw [K3.wr]; exact hI.scr, by rw [K3.rd]; exact hI.insig, hI.dsig, hI.slen⟩
  have x10₃ : t₃.gpr .x10 = BitVec.ofNat 64 (cOf p g k) := by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁]
  refine WP.ite (t₃.gpr .x13 == 0) (MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hn : ¬ j < digitAt t.mem S (cOf p g k) := by
      intro h; simp only [v13, h, ↓reduceIte] at hb; exact absurd hb (by decide)
    refine WP.block_nil (K t₃ (K3.mono (by simp)) (by rw [m3]; exact Frame.refl _ _) ?_)
    simp only [hn, ↓reduceIte, m3]
  · have hy : j < digitAt t.mem S (cOf p g k) := by
      by_contra h; simp only [v13, h, ↓reduceIte] at hb; exact absurd hb (by decide)
    have := sigCopy_ok hz hk hcl hI3 x10₃ (is := []) fun t' k' f' b' => WP.block_nil (K t' ((K3.trans k').mono (by simp))
      (by rw [m3] at f'; exact f') (by simp only [b', hy, ↓reduceIte, m3]))
    simp only [List.append_nil] at this; exact this

/-! ## `XK` past a step's pieces -/

section
variable {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}

theorem XK.laneIn (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    (hx : XK p σ S sig pk a D t) : LaneIn p S sig t :=
  ⟨hx.x19, hx.x21, by rw [hx.x20]; exact hidx, by rw [hx.wr]; exact TreeBase.regions_scr hR,
    by rw [hx.rd, hR.rd_eq]; exact List.mem_singleton_self _,
    (hR.rd_scr _ (List.mem_singleton_self _)), by have := hR.rd_fit _ (List.mem_singleton_self _); simp at this; omega⟩

/-- The signature, which is apart from `scratch`, is as on entry. -/
theorem XK.sigB (hz : Sz p) (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hx : XK p σ S sig pk a D t) {o l : Nat}
    (h : o + l ≤ p.xmssSigLen) : bytesAt t.mem (sig + BitVec.ofNat 64 o) l = bytesAt σ.mem (sig + BitVec.ofNat 64 o) l := by
  have hn32 := hz.n32
  have hd := hR.rd_scr _ (List.mem_singleton_self _)
  have hf := hR.rd_fit _ (List.mem_singleton_self _)
  simp only at hf
  refine TreeBase.bytesAt_frame hx.frame (fun r hr => ?_) (by omega)
  have hs : ∀ {o' l' : Nat}, o' + l' ≤ 65536 → Region.Disjoint ⟨sig + BitVec.ofNat 64 o, l⟩ ⟨at' S o', l'⟩ :=
    fun h' => (hd.sub_left (Offset.sub_base sig h)).sub_right (Offset.sub_base S h')
  simp only [changes, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl | rfl | rfl | rfl | rfl
  · exact (hd.sub_left (Offset.sub_base sig h)).sub_right (Region.sub_prefix (by simp [workUsed, scratchLen]))
  all_goals first
    | exact hs (by simp only [Layout.oVars, Layout.frameLen]; omega)
    | exact hs (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
    | exact hs (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
    | exact hs (by simp only [Layout.oDigits, Layout.oN, Layout.nodeSlots, Layout.oRoots, Layout.oMsg, Layout.oFidx]; omega)

/-- `XK` past a call that keeps the callee-saved registers but `x30` and
writes safe ranges only. -/
theorem XK.call (hz : Sz p) (hx : XK p σ S sig pk a D t) {t' : State} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) {W : List Region}
    (hf : Frame W t.mem t'.mem) (hW : ∀ r ∈ W, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l) : XK p σ S sig pk a D t' := by
  have hp : ∀ r : Reg, r ∉ ([.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
      .x16, .x17, .x22, .x23, .x24, .x25, .x26, .x30] : List Reg) → r ∈ preserved ∧ r ≠ .x30 := by
    intro r hr; cases r <;> simp_all [preserved]
  have hk : Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
      .x22, .x23, .x24, .x25, .x26, .x30] t t' :=
    ⟨fun r hr => hg r (hp r hr).1 (hp r hr).2, hrd, hwr, hsp, hv⟩
  exact XK.step hz hx (by decide) hk hf hW

/-- The `n + 32 + n` bytes of lane `k`. -/
theorem lane_bytes {m : Mem} {k : Nat} (hk : k < 4) (he : Env p m S pk a) {idx c j : Nat}
    (hF : LaneF p m S k idx c) (hh : bytesAt m (at' S (Layout.laneA k + p.n + 28)) 4 = toByte j 4) :
    bytesAt m (at' S (Layout.laneA k)) (2 * p.n + 32) =
      pk ++ adrsOf a 0 idx c j ++ bytesAt m (at' S (Layout.laneA k + p.n + 32)) p.n := by
  rw [show 2 * p.n + 32 = p.n + (16 + (4 + (4 + (4 + (4 + p.n))))) by omega]
  simp only [bytesAt_add, addr_add]
  have ty := hF.ty; have kp := hF.kp; have ch := hF.ch
  simp only [at'] at ty kp ch hh ⊢
  rw [he.seedA k hk, he.adrsA k hk, ty,
    show Layout.laneA k + p.n + 16 + 4 = Layout.laneA k + p.n + 20 by omega, kp,
    show Layout.laneA k + p.n + 16 + 4 + 4 = Layout.laneA k + p.n + 24 by omega, ch,
    show Layout.laneA k + p.n + 16 + 4 + 4 + 4 = Layout.laneA k + p.n + 28 by omega, hh,
    show Layout.laneA k + p.n + 16 + 4 + 4 + 4 + 4 = Layout.laneA k + p.n + 32 by omega]
  simp only [adrsOf, List.append_assoc]
theorem F_shake (hz : Sz p) (pk : List Byte) (ad : Adrs) (v : List Byte) : F p pk ad v = shake256 (pk ++ ad ++ v) p.n := by
  simp only [F, hz.shake, shakeAdrs]

/-- What a step keeps but the messages, from the step's start `t`. -/
structure Mid (p : Params) (σ tg t : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (g t₀ j : Nat)
    (u : State) : Prop where
  xk : XK p σ S sig pk a D u
  x22 : u.gpr .x22 = BitVec.ofNat 64 (4 * g)
  x23 : u.gpr .x23 = BitVec.ofNat 64 j
  x24 : u.gpr .x24 = BitVec.ofNat 64 t₀
  fields : ∀ k < 4, LaneF p u.mem S k (σ.gpr .x1).toNat (cOf p g k)
  frame : Frame (aW p S) tg.mem u.mem

/-- Lane `k`'s restore within a step, then `rest`. -/
theorem restore_step (hz : Sz p) (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {tg t : State} {g t₀ j k : Nat} (hg : 4 * g < p.len) (hk : k < 4) (hj : j < 16)
    (hM : Mid p σ tg t S sig pk a D g t₀ j t) {rest : Prog isa} {Q : State → Prop}
    (K : ∀ t', Mid p σ tg t S sig pk a D g t₀ j t' →
      bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        (if j < D.getD (cOf p g k) 0 then bytesAt σ.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n
          else bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n) →
      (∀ k' < 4, k' ≠ k → bytesAt t'.mem (at' S (Layout.laneA k' + p.n + 32)) p.n =
        bytesAt t.mem (at' S (Layout.laneA k' + p.n + 32)) p.n) → WP isa rest t' Q) :
    WP isa (.seq (Impl.SlhDsa.AArch64.Verify.restoreLane p k) rest) t Q := by
  have hn32 := hz.n32
  have hl := hz.len
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  refine WP.seq (restoreLane_ok hz hg hk hj (hM.xk.laneIn hR hidx) hM.x22 hM.x23 fun t' k' f' b' => ?_)
  have hW : ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ : Region)], ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, rfl, .inr (.inr ⟨k, hk, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩
  have dj : ∀ {o l : Nat}, (o + l ≤ Layout.laneA k + p.n + 32 ∨ Layout.laneA k + p.n + 32 + p.n ≤ o) →
      o + l ≤ 65536 → bytesAt t'.mem (at' S o) l = bytesAt t.mem (at' S o) l := fun h₁ h₂ =>
    TreeBase.bytesAt_frame f' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint S h₁ (by omega) (by rw [eA]; omega)) (by omega)
  have dig : digitAt t.mem S (cOf p g k) = D.getD (cOf p g k) 0 := hM.xk.dig _ hcl
  refine K t' ⟨XK.step hz hM.xk (by decide) k' f' hW, by rw [k'.get .x22, hM.x22], by rw [k'.get .x23, hM.x23],
    by rw [k'.get .x24, hM.x24], fun i hi => ?_, hM.frame.trans (f'.sub fun r hr => ?_)⟩ ?_ ?_
  · have F := hM.fields i hi
    exact ⟨by rw [dj (by rw [eA, eA]; omega) (by rw [eA]; omega)]; exact F.ty,
      by rw [dj (by rw [eA, eA]; omega) (by rw [eA]; omega)]; exact F.kp,
      by rw [dj (by rw [eA, eA]; omega) (by rw [eA]; omega)]; exact F.ch⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact aW_sub hz hk (by omega) (by simp only [Layout.strideA]; omega)
  · rw [b', dig, hM.xk.sigB hz hR (by
      rw [xmssSigLen_eq', ← Nat.succ_mul]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (show cOf p g k + 1 ≤ p.len by omega_using [hcl])) (Nat.le_add_right _ _))]
  · intro k₂ hk₂ hne
    exact dj (by rw [eA, eA]; omega) (by rw [eA]; omega)

theorem hW_safe (hz : Sz p) : ∀ r ∈ hW p S, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  exact ⟨_, _, rfl, .inr (.inr ⟨k, List.mem_range.mp hk, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩

theorem t4ch_safe (hz : Sz p) : ∀ r ∈ Wots4.t4ch p.n S Layout.oA Layout.strideA, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hk' := List.mem_range.mp hk
    exact ⟨_, _, rfl, .inr (.inr ⟨k, hk', .inl ⟨by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega,
      by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega⟩⟩)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨0, workUsed, by simp [at'], .inl (by omega)⟩

theorem aW_of_safeA (hz : Sz p) {W : List Region}
    (hW : ∀ r ∈ W, ∃ o l, r = ⟨at' S o, l⟩ ∧ ((o + l ≤ workUsed) ∨
      ∃ k < 4, Layout.laneA k + p.n + 16 ≤ o ∧ o + l ≤ Layout.laneA k + Layout.strideA)) :
    ∀ r ∈ W, ∃ R ∈ aW p S, Region.Sub r R := by
  intro r hr
  obtain ⟨o, l, rfl, h | ⟨k, hk, h₁, h₂⟩⟩ := hW r hr
  · exact ⟨_, List.mem_cons_self, Offset.sub_base S h⟩
  · exact aW_sub hz hk h₁ h₂

/-- Step `j` of a group. -/
theorem step_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {tg t : State} {g t₀ j : Nat} (hg : 4 * g < p.len) (h0 : t₀ ≤ j) (hj : j < 15)
    (hS : SI p σ tg S sig pk a D g t₀ j t) :
    WP isa (Impl.SlhDsa.AArch64.Verify.stepBody p f) t fun t' =>
      SI p σ tg S sig pk a D g t₀ (j + 1) t' ∧ t'.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 15 := by
  have hn32 := hz.n32
  have hl := hz.len
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  have hwS : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hS.xk.wr]; exact TreeBase.regions_scr hR
  unfold Impl.SlhDsa.AArch64.Verify.stepBody
  refine WP.seq ?_
  rw [← List.append_nil (List.flatMap _ _)]
  refine hfields_ok hz hS.xk.x19 hwS (by omega) hS.x23 fun t₁ k₁ f₁ b₁ => MlKem.AArch64.wp_nil ?_
  have X₁ : XK p σ S sig pk a D t₁ := XK.step hz hS.xk (by decide) k₁ f₁ (hW_safe hz)
  have F₁ : ∀ k < 4, LaneF p t₁.mem S k (σ.gpr .x1).toNat (cOf p g k) := fun k hk => by
    have F := hS.fields k hk
    have dj : ∀ {o l : Nat}, (o + l ≤ Layout.laneA k + p.n + 28) → Layout.laneA k ≤ o →
        bytesAt t₁.mem (at' S o) l = bytesAt t.mem (at' S o) l := fun h₁ h₂ =>
      TreeBase.bytesAt_frame f₁ (fun r hr => by
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
        have := List.mem_range.mp hk'
        exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA] at h₁ h₂ ⊢; omega)
          (by rw [eA] at h₁; omega) (by rw [eA]; omega)) (by rw [eA] at h₁; omega)
    exact ⟨by rw [dj (by omega) (by omega)]; exact F.ty, by rw [dj (by omega) (by omega)]; exact F.kp,
      by rw [dj (by omega) (by omega)]; exact F.ch⟩
  have M₁ : ∀ k < 4, bytesAt t₁.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n := fun k hk =>
    TreeBase.bytesAt_frame f₁ (fun r hr => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
      have := List.mem_range.mp hk'
      exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
        (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)
  refine WP.seq ?_
  rw [ht]
  refine thA_ok hz rfl T f.t4name X₁.x19 (by rw [X₁.wr]; exact TreeBase.regions_scr hR) hfit (.inl rfl)
    fun t₂ r₂ w₂ sp₂ g₂ v₂ b₂ fr₂ => ?_
  have X₂ : XK p σ S sig pk a D t₂ := XK.call hz X₁ r₂ w₂ sp₂ g₂ v₂ fr₂ (t4ch_safe hz)
  have keep2 : ∀ {o l : Nat}, o + l ≤ 65536 → (∀ k < 4, o + l ≤ Layout.laneA k + p.n + 32 ∨
      Layout.laneA k + p.n + 32 + p.n ≤ o) → workUsed ≤ o →
      bytesAt t₂.mem (at' S o) l = bytesAt t₁.mem (at' S o) l := fun hb hk hw =>
    TreeBase.bytesAt_frame fr₂ (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hr
        have hk'' := List.mem_range.mp hk'
        have := hk k hk''
        exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA] at this ⊢; omega)
          (by omega) (by simp only [Layout.oA, Layout.strideA]; omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base S hw (by omega)) (by omega)
  have F₂ : ∀ k < 4, LaneF p t₂.mem S k (σ.gpr .x1).toNat (cOf p g k) := fun k hk => by
    have F := F₁ k hk
    have h' : ∀ {o : Nat}, Layout.laneA k + p.n + 16 ≤ o → o + 4 ≤ Layout.laneA k + p.n + 32 →
        bytesAt t₂.mem (at' S o) 4 = bytesAt t₁.mem (at' S o) 4 := fun h₁ h₂ =>
      keep2 (by rw [eA] at h₂; omega) (fun k' hk' => by simp only [Layout.laneA, Layout.oA, Layout.strideA] at h₁ h₂ ⊢; omega)
        (by simp only [workUsed]; rw [eA] at h₁; omega)
    exact ⟨by rw [h' (by omega) (by omega)]; exact F.ty, by rw [h' (by omega) (by omega)]; exact F.kp,
      by rw [h' (by omega) (by omega)]; exact F.ch⟩
  have Fv : ∀ k < 4, bytesAt t₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      F p pk (adrsOf a 0 (σ.gpr .x1).toNat (cOf p g k) j)
        (V p pk a (σ.gpr .x1).toNat (cOf p g k) (D.getD (cOf p g k) 0)
          (bytesAt σ.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n) t₀ j) := fun k hk => by
    rw [b₂ k hk, lane_bytes hk X₁.env (F₁ k hk) (b₁ k hk), M₁ k hk, hS.msg k hk, F_shake hz]
  have hgx : ∀ r ∈ [Reg.x22, .x23, .x24], t₂.gpr r = t.gpr r := fun r hr => by
    rw [g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      k₁.get r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]
  have Fr₂ : Frame (aW p S) tg.mem t₂.mem := (hS.frame.trans (f₁.sub (aW_of_safeA hz fun r hr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, _, rfl, .inr ⟨k, List.mem_range.mp hk, by omega, by simp only [Layout.strideA]; omega⟩⟩))).trans
    (fr₂.sub (aW_of_safeA hz fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
        have hk' := List.mem_range.mp hk
        exact ⟨_, _, rfl, .inr ⟨k, hk', by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega,
          by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega⟩⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨0, workUsed, by simp [at'], .inl (by omega)⟩))
  have M₂ : Mid p σ tg t₂ S sig pk a D g t₀ j t₂ :=
    ⟨X₂, by rw [hgx .x22 (by simp), hS.x22], by rw [hgx .x23 (by simp), hS.x23], by rw [hgx .x24 (by simp), hS.x24],
      F₂, Fr₂⟩
  refine restore_step hz hR hidx hg (k := 0) (by decide) (by omega) M₂ fun t₃ M₃ r₃ o₃ => ?_
  refine restore_step hz hR hidx hg (k := 1) (by decide) (by omega) ⟨M₃.xk, M₃.x22, M₃.x23, M₃.x24, M₃.fields,
    M₃.frame⟩ fun t₄ M₄ r₄ o₄ => ?_
  refine restore_step hz hR hidx hg (k := 2) (by decide) (by omega) ⟨M₄.xk, M₄.x22, M₄.x23, M₄.x24, M₄.fields,
    M₄.frame⟩ fun t₅ M₅ r₅ o₅ => ?_
  refine restore_step (rest := .block _) hz hR hidx hg (k := 3) (by decide) (by omega) ⟨M₅.xk, M₅.x22, M₅.x23,
    M₅.x24, M₅.fields, M₅.frame⟩ fun t₆ M₆ r₆ o₆ => ?_
  refine wp_addi (by decide) fun t₇ u₇ => wp_subi (by decide) fun t₈ u₈ => MlKem.AArch64.wp_nil ⟨⟨?_, ?_, ?_, ?_,
    fun k hk => ?_, fun k hk => ?_, ?_⟩, ?_⟩
  · exact XK.step hz M₆.xk (by decide) ((upOnly u₇).keep.trans (upOnly u₈).keep) (by rw [u₈.mem, u₇.mem]; exact Frame.refl _ _)
      (fun r hr => absurd hr List.not_mem_nil)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), M₆.x22]
  · rw [u₈.other _ (by decide), u₇.gpr, M₆.x23, BitVec.ofNat_add]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), M₆.x24]
  · rw [u₈.mem, u₇.mem]; exact M₆.fields k hk
  · rw [u₈.mem, u₇.mem, V_succ p pk a _ _ _ _ h0]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [o₆ 0 (by decide) (by decide), o₅ 0 (by decide) (by decide), o₄ 0 (by decide) (by decide), r₃, Fv 0 (by decide)]
    · rw [o₆ 1 (by decide) (by decide), o₅ 1 (by decide) (by decide), r₄, o₃ 1 (by decide) (by decide), Fv 1 (by decide)]
    · rw [o₆ 2 (by decide) (by decide), r₅, o₄ 2 (by decide) (by decide), o₃ 2 (by decide) (by decide), Fv 2 (by decide)]
    · rw [r₆, o₅ 3 (by decide) (by decide), o₄ 3 (by decide) (by decide), o₃ 3 (by decide) (by decide), Fv 3 (by decide)]
  · rw [u₈.mem, u₇.mem]; exact M₆.frame
  · rw [u₈.gpr, u₇.gpr, M₆.x23, BitVec.ofNat_add]


end

end VG.Proof.SlhDsa.AArch64.XmssPk
