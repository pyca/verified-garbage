module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`). Each piece
is proved once for `o` in place or out of place; out of place, the
destination's addresses are the source's plus the distance in `s9`
(`toDst_ok`), and the whole blocks are `vg_aes_ctr32_to`'s.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

omit L in
/-- Out of place, `d :=` the distance to the destination (`s9`) plus the
source pointer (`s4`); in place, nothing. -/
theorem toDst_ok {o : Bool} {d : Reg} {s : State} (he : Env V sp s) :
    WP isa (.block (toDst o d)) s fun s' => (o = true → s'.gpr d = V .s9 + s.gpr .s4) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  cases o
  · simp only [toDst, Bool.false_eq_true, ↓reduceIte]
    exact WP.block_nil ⟨fun h => h.elim, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp only [toDst, ↓reduceIte]
    exact Steps.wp_add fun s₁ u₁ => WP.block_nil ⟨fun _ => by rw [u₁.gpr, he.fr .s9 (by decide)],
      fun r hr => u₁.other r hr, ⟨u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩⟩

omit L in
/-- The first `k` bytes of the source and destination alias as the whole do. -/
theorem Alias.take {o : Bool} {S D : Addr} {n k : Nat} (h : Alias o S D n) (hk : k ≤ n) : Alias o S D k := by
  cases o
  · exact h
  · exact (show (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ from h).sub_left (Region.sub_prefix hk)
      |>.sub_right (Region.sub_prefix hk)

omit L in
/-- From byte `j` on, the source and destination alias as the whole do. -/
theorem Alias.drop {o : Bool} {S D : Addr} {n j k : Nat} (h : Alias o S D n) (hjk : j + k ≤ n) :
    Alias o (S + BitVec.ofNat 64 j) (D + BitVec.ofNat 64 j) k := by
  cases o
  · exact congrArg (· + BitVec.ofNat 64 j) (show S = D from h)
  · exact (show (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ from h).sub_left (Offset.sub_base _ hjk)
      |>.sub_right (Offset.sub_base _ hjk)

omit L in
/-- In place, `S = D`. -/
theorem Alias.eq {S D : Addr} {n : Nat} (h : Alias false S D n) : S = D := h

omit L in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {s : State}
    (h : CrIn o V sp R icb P S D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa (cryptHeadWith o) s
      (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid o V sp R icb P S D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.s6 h.s5 (by omega_arith) hn') fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  have hk1 : 1 ≤ k := by omega_arith
  have hk16 : P % 16 + k ≤ 16 := by omega_arith
  have hkn : k ≤ n := by omega_arith
  have e30 : s₁.gpr .s1 = V .s1 := (hg _ (by decide) (by decide)).trans he.s1
  have e24 : s₁.gpr .s4 = S := (hg _ (by decide) (by decide)).trans h.s4
  have e25 : s₁.gpr .s5 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.s5
  have e26 : s₁.gpr .s6 = BitVec.ofNat 64 (P % 16) := (hg _ (by decide) (by decide)).trans h.s6
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  have h₂ : WP isa (.block [.addi .a0 .s1 64, .add .a0 .a0 .s6, mov .a1 .s4]) s₁ (fun s₂ : State =>
      s₂.gpr .a0 = V .s1 + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .a1 = S ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
    crun [Int.reduceNatCast', e30, e24, e26, mov]
    exact ⟨by rw [add_ofNat_assoc], fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.block_append (WP.block_append (WP.mono h₂ fun s₂ ⟨a0₂, a1₂, g₂, k₂⟩ => ?_)))
  have he₂ : Env V sp s₂ := he₁.keep (fun r hr => g₂ r (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd
    k₂.wr
  refine WP.mono (toDst_ok (d := .a4) he₂) fun s₃ ⟨d₃, g₃, k₃⟩ => ?_
  have e24₃ : s₃.gpr .s4 = S := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), e24]
  have e25₃ : s₃.gpr .s5 = BitVec.ofNat 64 n := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), e25]
  have e2₃ : s₃.gpr .a2 = BitVec.ofNat 64 k := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), h5]
  have h₄ : WP isa (.block [.add .s4 .s4 .a2, .sub .s5 .s5 .a2]) s₃ (fun s₄ : State =>
      s₄.gpr .s4 = S + BitVec.ofNat 64 k ∧ s₄.gpr .s5 = BitVec.ofNat 64 (n - k) ∧
      (∀ r, r ≠ .s4 → r ≠ .s5 → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄) := by
    crun [e24₃, e25₃, e2₃]
    exact ⟨ofNat_sub64 hkn hn', fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₄ fun s₄ ⟨h24, h25, g₄, k₄⟩ => ?_
  have hk₂' : Keeps s s₄ := hk.trans (k₂.trans (k₃.trans k₄))
  have hdk := h.data.take hkn
  have hsk := h.src.take hkn
  have hout : s₄.gpr (outReg o) = D := by
    cases o
    · simp only [outReg, Bool.false_eq_true, ↓reduceIte]
      rw [g₄ _ (by decide) (by decide), g₃ _ (by decide), a1₂, h.alias.eq]
    · simp only [outReg, ↓reduceIte]
      rw [g₄ _ (by decide) (by decide), d₃ rfl, g₂ _ (by decide) (by decide), e24, h.dst rfl,
        BitVec.sub_add_cancel]
  have lp : XorPre o s₄ (V .s1 + BitVec.ofNat 64 (64 + P % 16)) S D k := by
    refine ⟨by rw [g₄ _ (by decide) (by decide), g₃ _ (by decide), a0₂],
      by rw [g₄ _ (by decide) (by decide), g₃ _ (by decide), a1₂], hout,
      by rw [g₄ _ (by decide) (by decide), e2₃], hk1, by omega_arith, ?_, ?_, ?_, ?_, h.alias.take hkn⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.rd, hk₂'.wr]; exact hsk.rd
    · rw [hk₂'.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoopWith_ok o s₄ lp) fun s₅ ⟨hm₃, lo⟩ => ?_
  rw [hk₂'.mem] at hm₃
  have hxl := length_xorBytes s.mem S (V .s1 + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨D, k⟩] s.mem s₅.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)],
      (⟨V .s1 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨V .s1 + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → r ≠ .s4 → r ≠ .s5 →
      s₅.gpr r = s.gpr r :=
    fun r a b c d e f i j => by
      rw [lo.other r a b c d e (fun _ => f), g₄ r i j, g₃ r f, g₂ r b c, hg r d e]
  have he₃ : Env V sp s₅ := he.keep (fun r hr => g r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) (lo.keeps.2.2.trans hk₂'.sp) (lo.keeps.1.trans hk₂'.rd)
    (lo.keeps.2.1.trans hk₂'.wr)
  refine ⟨k, hk'.symm, he₃, hkn, ?_, ?_, h.s3, h.rounds,
    h.data.of_eq (lo.keeps.1.trans hk₂'.rd) (lo.keeps.2.1.trans hk₂'.wr) (lo.keeps.2.2.trans hk₂'.sp),
    h.src.of_eq (lo.keeps.1.trans hk₂'.rd) (lo.keeps.2.1.trans hk₂'.wr) (lo.keeps.2.2.trans hk₂'.sp), h.alias,
    h.dst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (fun _ => by decide), h24]
  · rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (fun _ => by decide), h25]
  · intro hc₀
    exact (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem S (V .s1 + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega_arith)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem S k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (h.alias.rest (j := 0) (l := k) (by omega_arith) h.data.ok.lt).symm) (by omega_arith)
  · by_cases hkk : k = n
    · left; omega_arith
    · right; omega_arith
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
theorem CrMid.data_eq {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMid o V sp R icb P S D n m₀ j s) : bytesAt s.mem D n =
      bytesAt s.mem D j ++ bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) := by
  rw [← bytesAt_add, Nat.add_sub_cancel' h.le]

omit L in
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : Addr} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64)
    (h24 : s.gpr .s4 = D + BitVec.ofNat 64 j) (h25 : s.gpr .s5 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block splitCtr) s fun s' =>
      s'.gpr .a3 = D + BitVec.ofNat 64 j ∧ s'.gpr .a4 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .s4 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .s5 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      (∀ r, r ≠ .t0 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → r ≠ .a6 → r ≠ .s4 → r ≠ .s5 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat64 (by omega_arith)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
      BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  simp only [splitCtr]
  crun [Int.reduceNatCast', h24, h25, mov, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega_arith), add_ofNat_assoc]
  refine ⟨by congr 1; omega_arith, fun r _ b c d e f g => by simp [b, c, d, e, f, g],
    ⟨rfl, rfl, rfl, rfl⟩⟩

omit L in
/-- `splitCtrWith o`: in place `splitCtr`; out of place the destination's
address in `a3` and the source's in `a6`. -/
theorem splitCtrWith_ok {o : Bool} {s : State} {S D : Addr} {n j : Nat} (he : Env V sp s) (hj : j ≤ n)
    (hn : n < 2 ^ 64) (ha : o = false → S = D) (hδ : o = true → V .s9 = D - S)
    (h24 : s.gpr .s4 = S + BitVec.ofNat 64 j) (h25 : s.gpr .s5 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block (splitCtrWith o)) s fun s' =>
      s'.gpr .a3 = D + BitVec.ofNat 64 j ∧ (o = true → s'.gpr .a6 = S + BitVec.ofNat 64 j) ∧
      s'.gpr .a4 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .s4 = S + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .s5 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      (∀ r, r ≠ .t0 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → r ≠ .a6 → r ≠ .a7 → r ≠ .s4 → r ≠ .s5 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  cases o
  · have e : S = D := ha rfl
    subst e
    simp only [splitCtrWith, Bool.false_eq_true, ↓reduceIte]
    exact WP.mono (splitCtr_ok hj hn h24 h25) fun s' ⟨a, b, c, d, g, k⟩ =>
      ⟨a, fun h => h.elim, b, c, d, fun r h0 h3 h4 h5 h6 _ h8 h9 => g r h0 h3 h4 h5 h6 h8 h9, k⟩
  · simp only [splitCtrWith, ↓reduceIte]
    refine WP.block_append (WP.mono (toDst_ok (o := true) (d := .a3) he) fun s₁ ⟨d₁, g₁, k₁⟩ => ?_)
    have hand := and15 (BitVec.ofNat 64 (n - j))
    rw [toNat64 (by omega_arith)] at hand
    have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
        BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
      rw [ofNat_sub64 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
    have e24 : s₁.gpr .s4 = S + BitVec.ofNat 64 j := by rw [g₁ _ (by decide), h24]
    have e25 : s₁.gpr .s5 = BitVec.ofNat 64 (n - j) := by rw [g₁ _ (by decide), h25]
    have e3 : s₁.gpr .a3 = D + BitVec.ofNat 64 j := by
      rw [d₁ rfl, h24, hδ rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    crun [Int.reduceNatCast', e24, e25, e3, mov, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega_arith),
      add_ofNat_assoc]
    refine ⟨by congr 1; omega_arith, fun r _ b c d e f g i => ?_, k₁.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    simp [c, d, e, f, g, i]; exact g₁ r b

omit L in
/-- The arguments of `vg_aes_ctr32` but the data and their number. -/
theorem ctrArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .s3 = BitVec.ofNat 64 R) :
    WP isa (.block (ctrArgs 48)) s fun s' =>
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = BitVec.ofNat 64 R ∧ s'.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s'.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a5 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h28 := he.s3; have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  simp only [ctrArgs]
  crun [Int.reduceNatCast', scrO, h28, h29, h30, h31, hR, mov]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {R : Nat} {D : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = D + BitVec.ofNat 64 j) (h7 : s.gpr .a4 = BitVec.ofNat 64 nb)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .s2) (V .s1) (V .s0) s (D + BitVec.ofNat 64 j) (16 * nb)) :
    CtrCall s (V .s2) (V .s1 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (V .s0 + BitVec.ofNat 64 512) R nb := by
  refine ⟨h3, h4, h5, h6, h7, h8, hR, hnb, ?_, ?_, ?_, ?_, ?_, ?_, hdj.ok.fit, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left hdj.wr)
        (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons hdj.wr
      (Covers.cons (he.perm.wC (by decide)) Covers.nil))

/-- The arguments of `vg_aes_ctr32_to` on `nb` whole blocks from `X` to `D + j`. -/
theorem ctrWholeTo_mk {R : Nat} {D X : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = D + BitVec.ofNat 64 j) (h7 : s.gpr .a4 = BitVec.ofNat 64 nb)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (h9 : s.gpr .a6 = X) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .s2) (V .s1) (V .s0) s (D + BitVec.ofNat 64 j) (16 * nb))
    (hx : DataOk (V .s1) (V .s0) s X (16 * nb)) (hxd : (⟨X, 16 * nb⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, 16 * nb⟩) :
    CtrToCall s (V .s2) (V .s1 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (V .s0 + BitVec.ofNat 64 512) X R nb := by
  have hc := ctrWhole_mk L he h3 h4 h5 h6 h7 h8 hR hnb hdj
  refine ⟨h3, h4, h5, h6, h7, h8, h9, hR, hnb, hc.kc, hc.kd, hc.ks, hc.cd, hc.cs, hc.ds,
    hx.st.sub_right (Lay.stSub (by decide)), hxd, hx.w.sub_right (Lay.wSub (by decide)), hc.fit, hx.fit, ?_,
    hc.writes⟩
  exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons hx.rd
    (Covers.cons (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left hdj.wr)
      (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil))))

/-- A call of `vg_aes_ctr32`, or out of place of `vg_aes_ctr32_to`, on `nb`
whole blocks from `X` (in place, `D + j`) to `D + j`. -/
theorem ctrCallWith_ok {o : Bool} {R : Nat} {D X : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = D + BitVec.ofNat 64 j) (h7 : s.gpr .a4 = BitVec.ofNat 64 nb)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (h9 : o = true → s.gpr .a6 = X)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .s2) (V .s1) (V .s0) s (D + BitVec.ofNat 64 j) (16 * nb))
    (hx : DataOk (V .s1) (V .s0) s X (16 * nb)) (ha : Alias o X (D + BitVec.ofNat 64 j) (16 * nb)) :
    WP isa (ctrCallWith o) s (CtrToPost s (V .s2) (V .s1 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j)
      (V .s0 + BitVec.ofNat 64 512) X R nb) := by
  cases o
  · have e : X = D + BitVec.ofNat 64 j := ha
    subst e
    simp only [ctrCallWith, Bool.false_eq_true, ↓reduceIte, ctrCall, Impl.AesCtr.RISCV64.ctrCall]
    exact WP.mono (ctr_call (ctrWhole_mk L he h3 h4 h5 h6 h7 h8 hR hnb hdj)) fun _ g =>
      ⟨g.rd, g.wr, g.sp, g.saved, g.frame, g.out, g.ctr⟩
  · simp only [ctrCallWith, ↓reduceIte]
    exact ctrTo_call (ctrWholeTo_mk L he h3 h4 h5 h6 h7 h8 (h9 rfl) hR hnb hdj hx ha)

/-- Whole blocks. -/
theorem cryptWhole_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMid o V sp R icb P S D n m₀ j s) (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa (cryptWholeWith o) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      CrMid o V sp R icb P S D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (splitCtrWith_ok he h.le hn' (fun ho => by subst ho; exact h.alias.eq) h.dst h.s4 h.s5)
    fun s₁ ⟨h6, h6', h7, h24, h25, hg₁, hk₁⟩ => ?_)
  generalize hnb : (n - j) / 16 = nb at h7 h24 h25
  have h16 : 16 * nb ≤ n - j := by omega_arith
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ := h.data.of_eq hk₁.rd hk₁.wr hk₁.sp
  have hs₁ := h.src.of_eq hk₁.rd hk₁.wr hk₁.sp
  refine WP.ite (decide (nb = 0)) (eval_zero h7 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, h.s3, h.rounds, hd₁, hs₁,
      h.alias, h.dst,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    have hsj := h.src.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (ctrArgs_ok he₁ h.s3) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_)
    have he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    have hk₁₂ := hk₁.trans hk₂
    refine WP.mono (ctrCallWith_ok L (X := S + BitVec.ofNat 64 j) he₂ a3 a4 a5
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7]) a8
      (fun ho => by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6' ho]) h.rounds (by omega_arith)
      (hdj.of_eq hk₁₂.rd hk₁₂.wr hk₁₂.sp) (hsj.of_eq hk₁₂.rd hk₁₂.wr hk₁₂.sp)
      (h.alias.drop (by omega_arith))) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_wholeTo (h.ctr hc₀) hw (m' := s₃.mem)
      (sp := S + BitVec.ofNat 64 j) (dp := D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    have hdis : ∀ r ∈ [⟨V .s1 + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
        ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩],
        (⟨S + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
      have hst := h.src.st; have hW := h.src.w
      have hs : Region.Sub ⟨S + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨S, n⟩ :=
        Offset.sub_base _ (by omega_arith)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
      · exact (h.alias.rest (j := j) (l := 16 * nb) (by omega_arith) hn').symm
      · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_, h.s3, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr) (g.sp.trans hk₂.sp),
      hs₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr) (g.sp.trans hk₂.sp), h.alias, h.dst, ?_, ?_, ?_,
      .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h25]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · intro hc₀
      have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (V .s2) R) icb (P + j) (bytesAt m₀ (S + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · rw [bytesAt_frame gframe hdis (by omega_arith)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (S + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (S + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .s3 = BitVec.ofNat 64 R) :
    WP isa (.block tailArgs) s fun s' =>
      s'.mem = (s.mem.writeW (V .s1 + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (V .s1 + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = BitVec.ofNat 64 R ∧ s'.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s'.gpr .a3 = V .s1 + BitVec.ofNat 64 64 ∧ s'.gpr .a4 = BitVec.ofNat 64 1 ∧
      s'.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h28 := he.s3; have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  have w₀ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  have a₀ := L.stal (d := 64) (by decide) (by decide)
  have a₁ := L.stal (d := 72) (by decide) (by decide)
  simp only [tailArgs, ctrArgs, List.cons_append, List.nil_append]
  crun [Int.reduceNatCast', scrO, h28, h29, h30, h31, hR, w₀, w₁, a₀, a₁, mov, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f i => by simp [a, b, c, d, e, f, i], ⟨rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on the keystream block. -/
theorem ctrTail_mk {R : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = V .s1 + BitVec.ofNat 64 64) (h7 : s.gpr .a4 = BitVec.ofNat 64 1)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s (V .s2) (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64)
      (V .s0 + BitVec.ofNat 64 512) R 1 := by
  refine ⟨h3, h4, h5, h6, h7, h8, hR, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · have := L.sw
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left (he.perm.stC (by decide)))
        (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons (he.perm.stC (by decide))
      (Covers.cons (he.perm.wC (by decide)) Covers.nil))

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (o : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (S D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s₀ s : State) : Prop where
  mid : CrMid o V sp R icb P S D n m₀ j s₀
  env : Env V sp s
  s4 : s.gpr .s4 = S + BitVec.ofNat 64 j
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n - j)
  ks : blockAt s.mem (V .s1 + BitVec.ofNat 64 64) =
    ciphOf m₀ (V .s2) R (blockAt s₀.mem (V .s1 + BitVec.ofNat 64 48))
  cb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (V .s1 + BitVec.ofNat 64 48))
  frame : Frame [⟨V .s1 + BitVec.ofNat 64 48, 32⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMid o V sp R icb P S D n m₀ j s) (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa (.seq (.block tailArgs) ctrCall) s (TailKs o V sp R icb P S D n m₀ j s) := by
  have he := h.env
  refine WP.seq (WP.mono (tailArgs_ok L he h.s3) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have fz : Frame [⟨V .s1 + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hKS0 : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 64) = 0 := by
    rw [hm₂, blockAt, zeroT_bytes]; decide
  have hCB : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 48) = blockAt s.mem (V .s1 + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : ciphOf s₂.mem (V .s2) R = ciphOf m₀ (V .s2) R := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, hc]
  refine WP.mono (ctr_call (ctrTail_mk L he₂ a3 a4 a5 a6 a7 a8 h.rounds)) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, hKS0, Proof.Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hk₂.rd], by rw [g.wr, hk₂.wr]⟩
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.s4]
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.s5]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

omit L in
/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s₀ s : State} (h : TailKs o V sp R icb P S D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block (([.addi .a0 .s1 64, mov .a1 .s4] : List Instr) ++ toDst o .a4 ++
      ([mov .a2 .s5] : List Instr))) (xorLoopWith o)) s
      (CrOut o V sp R icb P S D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt
  have hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  have hdj := hm.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have hsj := hm.src.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have he₃ := h.env
  have h30 := he₃.s1
  have h₂ : WP isa (.block [.addi .a0 .s1 64, mov .a1 .s4]) s fun s₂ =>
      s₂.gpr .a0 = V .s1 + BitVec.ofNat 64 64 ∧ s₂.gpr .a1 = S + BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    crun [Int.reduceNatCast', h30, h.s4, mov]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.block_append (WP.block_append (WP.mono h₂ fun s₂ ⟨a0₂, a1₂, g₂, k₂⟩ => ?_)))
  have he₂ : Env V sp s₂ := he₃.keep (fun r hr => g₂ r (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd
    k₂.wr
  refine WP.mono (toDst_ok (d := .a4) he₂) fun s₃ ⟨d₃, g₃, k₃⟩ => ?_
  have e25 : s₃.gpr .s5 = BitVec.ofNat 64 (n - j) := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), h.s5]
  refine Steps.wp_mv fun s₄ u₄ => WP.block_nil ?_
  have k₄ : Keeps s s₄ := k₂.trans (k₃.trans ⟨u₄.mem, u₄.rd, u₄.wr, u₄.sp⟩)
  have hout : s₄.gpr (outReg o) = D + BitVec.ofNat 64 j := by
    cases o
    · simp only [outReg, Bool.false_eq_true, ↓reduceIte]
      rw [u₄.other _ (by decide), g₃ _ (by decide), a1₂, hm.alias.eq]
    · simp only [outReg, ↓reduceIte]
      rw [u₄.other _ (by decide), d₃ rfl, g₂ _ (by decide) (by decide), h.s4, hm.dst rfl, ← BitVec.add_assoc,
        BitVec.sub_add_cancel]
  have lp : XorPre o s₄ (V .s1 + BitVec.ofNat 64 64) (S + BitVec.ofNat 64 j) (D + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨by rw [u₄.other _ (by decide), g₃ _ (by decide), a0₂],
      by rw [u₄.other _ (by decide), g₃ _ (by decide), a1₂], hout, by rw [u₄.gpr, e25], by omega_arith,
      by omega_arith, ?_, ?_, ?_, ?_, hm.alias.drop (by omega_arith)⟩
    · rw [k₄.rd, k₄.wr]; exact covers_left (he₃.perm.stC (by omega_arith))
    · rw [k₄.rd, k₄.wr, h.rd, h.wr]; exact hsj.rd
    · rw [k₄.wr, h.wr]; exact hdj.wr
    · exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoopWith_ok o s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [k₄.mem] at hm₅
  have hxl := length_xorBytes s.mem (S + BitVec.ofNat 64 j) (V .s1 + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have dst := hdj.ok.st; have dw := hdj.ok.w
  have hd₃ : bytesAt s.mem (S + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (S + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsj.st.sub_right (Lay.stSub (by decide))
    · exact hsj.w.sub_right (Lay.wSub (by decide))
  have ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (S + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega_arith)
    (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at ht
  have dS : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨V .s1 + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  have g : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₅.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [lo.other r a b c d e (fun _ => f), u₄.other r d, g₃ r f, g₂ r b c]
  refine ⟨he₃.keep (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide))
      (lo.keeps.2.2.trans k₄.sp) (lo.keeps.1.trans k₄.rd) (lo.keeps.2.1.trans k₄.wr), ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega_arith]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    have hdone : bytesAt s₅.mem D j = bytesAt s₀.mem D j := by
      have hdt := (hm.data.take hm.le).ok
      rw [bytesAt_frame fw (fun r hr => ?_) (by omega_arith), bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
      · simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    have hpiece : bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (V .s2) R) icb (P + j) (bytesAt m₀ (S + BitVec.ofNat 64 j) (n - j)) := by
      have e := bytesAt_writeBytes_self s.mem (D + BitVec.ofNat 64 j)
        (xorBytes s.mem (S + BitVec.ofNat 64 j) (V .s1 + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMid o V sp R icb P S D n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa (cryptTailWith o) s (CrOut o V sp R icb P S D n m₀) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n - j = 0)) (eval_zero h.s5 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => h.ctr hc₀, fun hc₀ => h.done hc₀, h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L h hc) fun _ ht => tailXor_ok ht hj h0)

theorem CrMid.ciph {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMid o V sp R icb P S D n m₀ j s) : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R :=
  ciph_frame h.frame (ctx_crFrame L h.data) h.rounds

omit L in
/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {s : State}
    (h : CrIn o V sp R icb P S D n s) (h0 : n ≠ 0) :
    WP isa (cryptFillWith o) s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid o V sp R icb P S D n s.mem j s') := by
  refine WP.ite (decide (P % 16 = 0)) (eval_zero h.s6 (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega_arith, by rw [h.s4, BitVec.add_zero], by rw [h.s5, Nat.sub_zero],
      h.s3, h.rounds, h.data, h.src, h.alias, h.dst, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [BitVec.add_zero, Nat.sub_zero], .inr (by omega_arith), Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (cryptHead_ok h h0 hP) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `cryptWith o`. -/
theorem crypt_ok {o : Bool} {R : Nat} {icb : Block} {P : Nat} {S D : Addr} {n : Nat} {s : State}
    (h : CrIn o V sp R icb P S D n s) :
    WP isa (cryptWith o) s (CrOut o V sp R icb P S D n s.mem) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.s5 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => hc₀, fun _ => by simp [bytesAt]; rfl, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (cryptFill_ok h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.RISCV64
