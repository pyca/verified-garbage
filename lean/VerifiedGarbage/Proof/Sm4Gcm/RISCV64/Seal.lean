module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Tag
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64

/-! ### `Sm4Gcm.RISCV64.OneEntry`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: the entry of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. AES-GCM's entry
(`Proof/AesGcm/RISCV64/OneEntry.lean`) with the arguments one register
earlier, and `tag` in `a7`: it loads `W` from the stack argument at
`sp + off`, saves our caller's registers there, keeps the arguments in
registers and the addresses of the additional data and the data in `W`
(`one1_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov aadO dataO save saved)
open VG.Proof.AesGcm.RISCV64 hiding SO1 one1_wp

/-- After the entry of `seal` or `open`, from `s₀`. -/
structure SO1 (W : Addr) (s₀ s₁ : State) : Prop where
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem W s₀
  frame : Frame [oneR W] s₀.mem s₁.mem
  aad : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s₀.gpr .a3
  dat : s₁.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5
  s0 : s₁.gpr .s0 = W
  s1 : s₁.gpr .s1 = W + BitVec.ofNat 64 16
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s4 : s₁.gpr .s4 = s₀.gpr .a1
  s5 : s₁.gpr .s5 = s₀.gpr .a2
  s7 : s₁.gpr .s7 = s₀.gpr .a2
  s10 : s₁.gpr .s10 = s₀.gpr .a4
  s11 : s₁.gpr .s11 = s₀.gpr .a6
  s9 : s₁.gpr .s9 = s₀.gpr .a7

theorem one1_wp {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 0 ∨ off = 8)
    (hW : Covers [⟨W, 2560⟩] s₀.wr) (hWa : W.toNat % 8 = 0) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block (oneEntry off)) s₀ (SO1 W s₀) := by
  simp only [oneEntry, List.cons_append, List.nil_append]
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega_using [hoff]) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega_using [hsa]) (by omega_using [hoff])) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => ?_
  have b12 : sB.gpr .t1 = W := by rw [uB.gpr, uA.mem, hWv]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (b := .t1) (by rw [b12, uB.wr, uA.wr]; exact hW) (by rw [b12]; exact hWa))
    fun s₂ ⟨hg, h31, hk, hsv, hf⟩ => ?_
  rw [b12] at h31 hsv hf
  have e : ∀ r, r ≠ .t1 → r ≠ .s0 → s₂.gpr r = s₀.gpr r := fun r a c => by
    rw [hg r c, uB.other r a, uA.other r a]
  have sv₂ : SavedAt s₂.mem W s₀ := hsv.congr fun p hp => by
    rw [uB.other _ (by revert hp; revert p; decide), uA.other _ (by revert hp; revert p; decide)]
  rw [uB.mem, uA.mem] at hf
  have kB : s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧ s₂.sp = s₀.sp :=
    ⟨by rw [hk.rd, uB.rd, uA.rd], by rw [hk.wr, uB.wr, uA.wr], by rw [hk.sp, uB.sp, uA.sp]⟩
  refine Steps.wp_mv fun s₄ u₄ =>
    Steps.wp_addi (imm := 16) (by decide) fun s₅ u₅ => Steps.wp_mv fun s₆ u₆ => Steps.wp_mv fun s₇ u₇ =>
    Steps.wp_mv fun s₈ u₈ => ?_
  have g₈ : s₈.gpr .s0 = W := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄,
    reduceCtorEq, ite_false, h31]
  have k₈ : s₈.rd = s₀.rd ∧ s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp ∧ s₈.mem = s₂.mem :=
    ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, kB.1], by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, kB.2.1],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, kB.2.2], by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]⟩
  refine Steps.wp_sd (off := aadO) (a := W + BitVec.ofNat 64 aadO) (by decide) (by rw [g₈])
    (Spill.al8 hWa (by decide)) (by rw [k₈.2.1]; exact in_off hW (by decide) (by decide)) fun s₉ m₉ => ?_
  refine Steps.wp_mv fun s₁₀ u₁₀ => ?_
  refine Steps.wp_sd (off := dataO) (a := W + BitVec.ofNat 64 dataO) (by decide)
    (by rw [u₁₀.other _ (by decide), m₉.gpr, g₈]) (Spill.al8 hWa (by decide))
    (by rw [u₁₀.wr, m₉.wr, k₈.2.1]; exact in_off hW (by decide) (by decide)) fun s₁₁ m₁₁ => ?_
  refine Steps.wp_mv fun s₁₂ u₁₂ => Steps.wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [u₁₃.sp, u₁₂.sp, m₁₁.sp, u₁₀.sp, m₉.sp, k₈.2.2.1]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, m₁₁.rd, u₁₀.rd, m₉.rd, k₈.1]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, m₁₁.wr, u₁₀.wr, m₉.wr, k₈.2.1]
  -- The memory: the two addresses stored after the saved registers.
  have v₄ : s₈.gpr .a3 = s₀.gpr .a3 := by
    simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false]
    exact e _ (by decide) (by decide)
  have v₆ : s₁₀.gpr .a5 = s₀.gpr .a5 := by
    rw [u₁₀.other _ (by decide), m₉.gpr]
    simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false]
    exact e _ (by decide) (by decide)
  generalize hM : (s₂.mem.writeW (W + BitVec.ofNat 64 aadO) (s₀.gpr .a3)).writeW (W + BitVec.ofNat 64 dataO)
    (s₀.gpr .a5) = M
  have m₁₃ : s₁₃.mem = M := by
    rw [u₁₃.mem, u₁₂.mem, m₁₁.mem, u₁₀.mem, v₆, m₉.mem, v₄, k₈.2.2.2, hM]
  have fM : Frame [oneR W] s₀.mem M := by
    rw [← hM]
    exact ((hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have dS : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 248 → (savedR W).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ :=
    fun h₁ h₂ => Offset.disjoint _ (.inl (by omega_using [h₁])) (by omega_using []) (by omega_using [h₂])
  refine ⟨⟨by rw [rd₁₃], by rw [wr₁₃], by rw [sp₁₃]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₃, ← hM]
    exact (sv₂.frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS (by decide) (by decide))).frame
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS (by decide) (by decide))
  · rw [m₁₃]; exact fM
  · rw [m₁₃, ← hM, Mem.readW_writeW_sep (Region.Disjoint.sep
      (Offset.disjoint W (d := aadO) (n := 8) (e := dataO) (k := 8) (.inl (by decide)) (by decide) (by decide))
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), Mem.readW_writeW_self64]
  · rw [m₁₃, ← hM, Mem.readW_writeW_self64]
  all_goals simp only [upd_gpr u₁₃, upd_gpr u₁₂, upd_gpr u₁₀, m₁₁.gpr, m₉.gpr, upd_gpr u₈,
    upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false, ite_true]
  all_goals first
    | exact h31
    | (rw [h31])
    | exact e _ (by decide) (by decide)

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.OneShot`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: the pieces of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. AES-GCM's pieces
(`Proof/AesGcm/RISCV64/OneShot.lean`), whose `oneAad` SM4-GCM shares, with
SM4's `crypt` and `tag`: `oneCrypt` runs counter mode over the data from the
first counter block (`oneCrypt_ok`), and `oneTag o` absorbs the data as
ciphertext, padded, then the lengths block, and writes the tag to `W + o`
(`oneTag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov dataO dataArgs absorb flush)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel cryptHead_ok ctrArgs_ok ctrWhole_mk cryptWhole_ok tailArgs_ok ctrTail_mk
  tailKs_ok tailXor_ok cryptTail_ok cryptFill_ok crypt_ok tagFrame TagOut TagMid tagLens_ok tagArgs_ok
  ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT oneTag_ok
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock padded)

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- The slots of the addresses are apart from what `crypt` writes. -/
theorem slot_crFrame (hb : Big V sp) {s : State} {D : Addr} {n : Nat}
    (hd : DataW (V .s2) (V .s1) (V .s0) s D n) {d : Nat} (hdd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ crFrame (V .s1) sp D n, (⟨V .s0 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by omega_using [hdd]))).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega_using [hdd], by omega_using [hdd]⟩)).symm
  · exact (hb.w.sub_right (Lay.wSub (by omega_using [hdd]))).symm

end

/-- After `oneCrypt`, from `m₀`. -/
structure OC (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (D : Addr) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  out : bytesAt s.mem D (V .s11).toNat = gctr (ciphOf m₀ (V .s2)) icb (bytesAt m₀ D (V .s11).toNat)
  frame : Frame (crFrame (V .s1) sp D (V .s11).toNat) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- `oneCrypt`: counter mode over the data (`len`, `s11`, bytes at `D`, in
`W + dataO`) from the counter block `icb`. -/
theorem oneCrypt_ok (hb : Big V sp) {D : Addr} {s : State} (he : Env V sp s)
    (hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat)
    (hbd : (below sp 3248).Disjoint ⟨D, (V .s11).toNat⟩)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    {icb : Block} (hcb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC V sp icb D s.mem) := by
  refine WP.seq (WP.mono (dataArgs_ok he L.wal hDs) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ci : CrIn V sp icb 0 D (V .s11).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26], hb, hbd, hd.of_eq k₁.rd k₁.wr k₁.sp⟩
  refine WP.mono (crypt_ok L ci) fun s₂ co => ?_
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (V .s1 + BitVec.ofNat 64 64) (ciphOf s.mem (V .s2)) hcb
  exact ⟨co.env, by rw [co.out c0, ← Proof.Gcm.gctr_eq], co.frame⟩

end

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w : Addr) (o : Nat) (sp : Addr) : List Region :=
  [⟨st, 48⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩,
    below sp 3248]

theorem abs_otSub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ absFrame st w 16 sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, below_sub⟩

theorem t_otSub {st w sp : Addr} {o : Nat} : ∀ r ∈ tFrame st w 16 sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, below_sub⟩

theorem tag_otSub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ tagFrame st w o sp, ∃ r' ∈ otFrame st w o sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`
(`D`), from the counter block `J`. -/
structure OT (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H : Block) (a : List Byte) (J : Block) (D : Addr)
    (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt m₀ D (V .s11).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ D (V .s11).toNat).length)] ^^^ ciphOf m₀ (V .s2) J)
  frame : Frame (otFrame (V .s1) (V .s0) o sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

theorem oneTag_ok [VG.Proof.Gcm.RISCV64.GhashLaw] (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a : List Byte} {D : Addr}
    {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hl : (V .s10).toNat = a.length)
    (hab : Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hd : DataOk (V .s1) (V .s0) s D (V .s11).toNat)
    (hDs : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (oneTag o) s (OT V sp o H a (blockAt s.mem (V .s1)) D s.mem) := by
  have hk := he.stk'
  have dC : ∀ r ∈ otFrame (V .s1) (V .s0) o sp, (⟨V .s2, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega_using [ho]))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact hb.c.symm
  have dJ : ∀ r ∈ absFrame (V .s1) (V .s0) 16 sp ++ tFrame (V .s1) (V .s0) 16 sp,
      (⟨V .s1, 16⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simpa using stb_abs16 L hk (d := 0) (.inl rfl) r hr
    · simpa using stb_t16 L hk (d := 0) (.inl rfl) r hr
  have hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (dataArgs_ok he L.wal hDs) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ai : AbsIn V sp 16 H (a ++ zeros (padLen a.length)) D (V .s11).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26, hx], hd.of_eq k₁.rd k₁.wr k₁.sp, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) ai) fun s₂ ab => ?_)
  rw [k₁.mem] at ab
  have h23 := ab.env.fr .s11 (by decide)
  have hand := and15 (V .s11)
  have h₃ : WP isa (.block [.logicImm .and .s6 .s11 15]) s₂ fun s₃ =>
      s₃.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
        (∀ r, r ≠ .s6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    crun [Int.reduceNatCast', h23, hand]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨a26', g₃, k₃⟩ => ?_)
  have he₃ := ab.env.keep (fun r hr => g₃ r (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  have hH₂ : blockAt s₂.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl) hk)]; exact hH
  let ct := bytesAt s.mem D (V .s11).toNat
  have hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (V .s11).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega_using [hx]
  refine WP.seq (WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := (a ++ zeros (padLen a.length)) ++ ct) (H := H)
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [a26', hlx])) fun s₄ fl => ?_)
  rw [k₃.mem] at fl
  have e22 := fl.env.fr .s10 (by decide)
  have e23 := fl.env.fr .s11 (by decide)
  have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s₄ fun s₅ =>
      s₅.gpr .s4 = V .s10 ∧ s₅.gpr .s6 = V .s11 ∧ (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    crun [Int.reduceNatCast', mov, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, g₅, k₅⟩ => ?_)
  have he₅ := fl.env.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  refine WP.mono (tag_ok L hb ho he₅ (H := H) (by rw [k₅.mem]; exact fl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, k₅.mem] at tg
  have f₄ : Frame (absFrame (V .s1) (V .s0) 16 sp ++ tFrame (V .s1) (V .s0) 16 sp) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      (fl.frame.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨tg.env, ?_, ?_⟩
  · rw [tg.out]
    have hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [padded_eq] at hw
    rw [hw, ciph_frame f₄ (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨r', hr', hs⟩ := abs_otSub (o := o) r hr; exact (dC r' hr').sub_right hs
        · obtain ⟨r', hr', hs⟩ := t_otSub (o := o) r hr; exact (dC r' hr').sub_right hs),
      blockAt_frame f₄ dJ, hl]
    simp only [ct, length_bytesAt]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    rcases List.mem_append.mp hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr

end

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/Seal.lean`) with SM4's pieces: the entry loads `W`
from the stack argument and keeps the arguments (`one1_wp`), then `oneAad`,
`oneCrypt` and `oneTag 0` run on the state at `W + 16`, and `tagOut`
copies the tag to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tagOut dataO oneAad)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok SO1 one1_wp one_env saved_otFrame seal_wp sealPre sealRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ctxH encryptWith)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- The stack below `sp`, for the state at `W + 16`. -/
theorem one_stk3 {s : State} {rs : List Region} (h : stkOk3 s rs) {c W : Addr} (hc : ⟨c, 256⟩ ∈ rs)
    (hw : ⟨W, 2560⟩ ∈ rs) : StkOk c (W + BitVec.ofNat 64 16) W s.sp :=
  ⟨h.buf hc, (h.buf hw).sub_left (Lay.wSub (by decide)), h.buf hw, h.1, by have := h.2.1; omega_using [this]⟩

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W : Addr} (h1 : SO1 W s₀ s₁)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp) :
    Env s₁.gpr s₀.sp s₁ := by
  obtain perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.keeps.rd h1.keeps.wr
  exact ⟨fun _ _ => rfl, h1.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.keeps.sp]; exact hk⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_otFrame {sp : Addr} (hbw : (below sp 3248).Disjoint ⟨w, 2560⟩) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega_using [ho]) (.inl (by omega_using [ho]))
  · exact saved_w (by decide) (.inr (by decide))
  · exact (hbw.sub_right (Lay.wSub (by decide))).symm

end

theorem seal_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : sealRISCV64.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealRISCV64.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    ca, wa⟩ := h'
  obtain L₀ := oneLay fc fW dcW ca wa
  obtain hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp :=
    one_stk3 hstk (by simp) (by simp)
  obtain bc₀ : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a0, 256⟩ := hstk.buf3 (by simp)
  obtain bw₀ : (below s₀.sp 3248).Disjoint ⟨stackArg s₀ 0, 2560⟩ := hstk.buf3 (by simp)
  obtain bd₀ : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ := hstk.buf3 (by simp)
  obtain bs₀ : (below s₀.sp 3248).Disjoint ⟨stackArg s₀ 0 + BitVec.ofNat 64 16, 80⟩ :=
    bw₀.sub_right (Lay.wSub (by decide))
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 1] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  refine WP.seq (WP.mono (one1_wp (off := 0) (W := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 0) (by decide)) rfl) fun s₁ h1 => ?_)
  obtain he₁ := one_env h1 hC hW hk₀
  obtain hb₁ : Big s₁.gpr s₀.sp := ⟨hstk.2.1, by rw [h1.s2]; exact bc₀, by rw [h1.s1]; exact bs₀,
    by rw [h1.s0]; exact bw₀⟩
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ := h1.frame
  have hk₁ := h1.keeps
  obtain cO : ∀ r ∈ [oneR (stackArg s₀ 0)], (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dcW.sub_right (Lay.wSub (by decide))
  -- `oneAad`
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ cO
  obtain hN : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a1) (s₀.gpr .a2).toNat := by
    rw [h1.s1, h1.s0]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a2).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain hAd : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a3) (s₁.gpr .s10).toNat := by
    rw [h1.s1, h1.s0, h1.s10]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a4).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.s4 (by rw [h1.s5]; exact toN)
    (by rw [h1.s7]; exact toN) hN hAd (by rw [h1.s0]; exact h1.aad))) fun s₂ ⟨oa, rd₂, wr₂, sp₂⟩ => ?_)
  -- `oneCrypt`
  obtain hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₀.gpr .a5) (s₁.gpr .s11).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s11]
    obtain hDw : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [sp₂, hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩
  obtain hD₂s : s₂.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oa.frame (slot_j0 L he₁.stk' (by decide)), h1.s0]; exact h1.dat
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L hb₁ oa.env hd₂ (by rw [h1.s11]; exact bd₀) hD₂s oa.cb))
    fun s₃ ⟨oc, rd₃, wr₃, sp₃⟩ => ?_)
  -- `oneTag 0`
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L hb₁ hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  obtain hb := Nat.mod_lt (bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat).length)).length (show 16 > 0 by decide)
  obtain hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame hb₁.st hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame hb₁.st hd₂ (by omega_using [])) (by omega_using []))
  obtain hD₃s : s₃.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oc.frame (slot_crFrame L hb₁ hd₂ (by decide))]; exact hD₂s
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L hb₁ (o := 0) (.inl rfl) oc.env hH₃
    (length_bytesAt _ _ _).symm hab₃ (hd₂.ok.of_eq rd₃ wr₃ sp₃) hD₃s)) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  obtain hTw : Covers [⟨s₁.gpr .s9, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, wr₂, hk₁.wr, h1.s9, hwr]; exact covers_mem (by simp)
  obtain hTd' : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
    rw [h1.s9, h1.s0]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  obtain he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  rw [h1.s1, h1.s0] at of₄
  have cf₃ := oc.frame
  rw [h1.s1, h1.s11] at cf₃
  have jf₂ := oa.frame
  rw [h1.s1, h1.s0] at jf₂
  obtain hd₂₀ : DataW (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₂ (s₀.gpr .a5)
      (s₀.gpr .a6).toNat := by rw [← h1.s2, ← h1.s1, ← h1.s0, ← h1.s11]; exact hd₂
  have sv₁ : SavedAt s₁.mem (stackArg s₀ 0) s₀ := h1.saved
  obtain sv₅ : SavedAt s₅.mem (stackArg s₀ 0) s₀ :=
    (((sv₁.frame jf₂ (saved_j0Frame L₀ hk₀)).frame cf₃ (saved_crFrame L₀ bw₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ bw₀ (.inl rfl))).frame (by rw [h1.s9] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  obtain e31 : s₅.gpr .s0 = stackArg s₀ 0 := (he₅.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 wa (by have := he₅.perm.w; rw [h1.s0] at this; exact Covers.right this) sv₅
    he₅.sp) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  obtain f₂ : Frame (oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp)
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dc₂ : ∀ r ∈ oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp,
      (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact hk₀.c
  obtain dD : ∀ r ∈ oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp,
      (⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok (sp₂.trans hk₁.sp) r hr
  obtain hc₂ := ciph_keep f₂ dc₂
  obtain hc₃ : ciphOf s₃.mem (s₀.gpr .a0) = ctxCiph s₀.mem (s₀.gpr .a0) := by
    rw [ciph_frame cf₃ (ctx_crFrame' L₀ bc₀ hd₂₀), hc₂]
  obtain hD₂ : bytesAt s₂.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .a6).isLt; omega_using [])
  obtain hiv : bytesAt s₁.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat = bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a2).isLt; omega_using [])
  obtain haad : bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat = bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := by
    rw [h1.s10]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a4).isLt; omega_using [])
  obtain hj₃ : blockAt s₃.mem (stackArg s₀ 0 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame bs₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.s1]
    exact oa.j
  obtain hD₃ : bytesAt s₃.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0))
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat) := by
    have := oc.out
    rw [h1.s11, h1.s2, hc₂, hD₂, hiv] at this
    exact this
  obtain hD₄ : bytesAt s₄.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₃.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .a6).isLt; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact bd₀.symm
  obtain hD₅ : bytesAt s₅.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₄.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]; exact ddt)
      (by have := (s₀.gpr .a6).isLt; omega_using [])
  have ho := ot.out
  rw [h1.s2, h1.s1, h1.s11, h1.s0, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.s0, h1.s9] at hb₅
  simp only [sealRISCV64, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

end VG.Proof.Sm4Gcm.RISCV64
