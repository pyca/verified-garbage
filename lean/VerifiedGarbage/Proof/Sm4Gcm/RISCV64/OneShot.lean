module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Tag
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset

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
  · exact (hd.ok.w.sub_right (Lay.wSub (by omega))).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (hb.w.sub_right (Lay.wSub (by omega))).symm

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
    (hbd : (below sp 3232).Disjoint ⟨D, (V .s11).toNat⟩)
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
    below sp 3232]

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

theorem oneTag_ok (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a : List Byte} {D : Addr}
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
    · exact L.cw'.sub_right (Lay.wSub (by omega))
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
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega
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
