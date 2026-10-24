module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Tag
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# SM4-GCM on PPC64LE: the pieces of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/OneShot.lean`), whose `oneAad` (and `oneAad_ok`)
SM4-GCM shares: both keep a streaming state at `W + 16`; `oneCrypt` runs counter mode over the data from the first counter block
(`oneCrypt_ok`), and `oneTag o` absorbs the data as ciphertext, padded, then
the lengths block, and writes the tag to `W + o` (`oneTag_ok`). The pieces
are stated for an environment `Env V sp s`, whose registers the entries of
`seal` and `open` fill.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov dataArgs absorb flush)
open VG.Proof.AesGcm.PPC64LE (Env Lay Keeps DataW DataOk AbsIn absFrame tFrame absorb_ok flush_ok ctx_absFrame
  stb_abs16 stb_t16 and15 bytesAt_frame blockAt_frame dataArgs_ok padded_eq length_bytesAt WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock padded)

/-- After `oneCrypt`, from `m₀`. -/
structure OC (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .r27) (V .r23).toNat =
    gctr (ciphOf m₀ (V .r29)) icb (bytesAt m₀ (V .r27) (V .r23).toNat)
  frame : Frame (crFrame (V .r30) (V .r28) (V .r27) (V .r23).toNat) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
  (X : XOk (V .r29) (V .r30) (V .r31) (V .r28))
include L X

/-- `oneCrypt`: counter mode over the data (`len`, `r23`, bytes at `r27`) from
the counter block `icb`. -/
theorem oneCrypt_ok {s : State} (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) (hxw : Covers [xR (V .r28)] s.wr)
    (hdx : (⟨V .r27, (V .r23).toNat⟩ : Region).Disjoint (xR (V .r28)))
    {icb : Block} (hcb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC V sp icb s.mem) := by
  refine WP.seq (WP.mono (dataArgs_ok he) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ci : CrIn V sp icb 0 (V .r27) (V .r23).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26], hd.of_eq k₁.rd k₁.wr, by rw [k₁.wr]; exact hxw, hdx⟩
  refine WP.mono (crypt_ok L X ci) fun s₂ co => ?_
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (V .r30 + BitVec.ofNat 64 64) (ciphOf s.mem (V .r29)) hcb
  exact ⟨co.env, by rw [co.out c0, ← Proof.Gcm.gctr_eq], co.frame⟩

end

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w x : Addr) (o : Nat) : List Region :=
  [⟨st, 48⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, xR x]

theorem abs_otSub {st w x : Addr} {o : Nat} : ∀ r ∈ absFrame st w 16, ∃ r' ∈ otFrame st w x o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩

theorem t_otSub {st w x : Addr} {o : Nat} : ∀ r ∈ tFrame st w 16, ∃ r' ∈ otFrame st w x o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩

theorem tag_otSub {st w x : Addr} {o : Nat} : ∀ r ∈ tagFrame st w x o, ∃ r' ∈ otFrame st w x o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`
(`r27`), from the counter block `J`. -/
structure OT (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H : Block) (a : List Byte) (J : Block) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt m₀ (V .r27) (V .r23).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (V .r27) (V .r23).toNat).length)] ^^^ ciphOf m₀ (V .r29) J)
  frame : Frame (otFrame (V .r30) (V .r31) (V .r28) o) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
  (X : XOk (V .r29) (V .r30) (V .r31) (V .r28))
include L X

theorem oneTag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a : List Byte} {s : State} (he : Env V sp s)
    (hxw : Covers [xR (V .r28)] s.wr)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) (hl : (V .r22).toNat = a.length)
    (hab : Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hd : DataOk (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    WP isa (oneTag o) s (OT V sp o H a (blockAt s.mem (V .r30)) s.mem) := by
  have dC : ∀ r ∈ otFrame (V .r30) (V .r31) (V .r28) o, (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact X.cx
  have dJ : ∀ r ∈ absFrame (V .r30) (V .r31) 16 ++ tFrame (V .r30) (V .r31) 16,
      (⟨V .r30, 16⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simpa using stb_abs16 L (d := 0) (.inl rfl) r hr
    · simpa using stb_t16 L (d := 0) (.inl rfl) r hr
  have hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (dataArgs_ok he) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ai : AbsIn V sp 16 H (a ++ zeros (padLen a.length)) (V .r27) (V .r23).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26, hx], hd.of_eq k₁.rd k₁.wr, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₂ ⟨ab, _, wr₂, _⟩ => ?_)
  rw [k₁.mem] at ab
  have h23 := ab.env.fr .r23 (by decide)
  have hand := and15 (V .r23)
  have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) s₂ fun s₃ =>
      s₃.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
        (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    crun [h23, hand]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨a26', g₃, k₃⟩ => ?_)
  have he₃ := ab.env.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  have hH₂ : blockAt s₂.mem (V .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH
  let ct := bytesAt s.mem (V .r27) (V .r23).toNat
  have hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (V .r23).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := (a ++ zeros (padLen a.length)) ++ ct)
    (H := H) ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [a26', hlx]))) fun s₄ ⟨fl, _, wr₄, _⟩ => ?_)
  rw [k₃.mem] at fl
  have e22 := fl.env.fr .r22 (by decide)
  have e23 := fl.env.fr .r23 (by decide)
  have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s₄ fun s₅ =>
      s₅.gpr .r24 = V .r22 ∧ s₅.gpr .r26 = V .r23 ∧ (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    crun [mov, BitVec.or_self, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, g₅, k₅⟩ => ?_)
  have he₅ := fl.env.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  refine WP.mono (tag_ok L X ho he₅ (by rw [k₅.wr, wr₄, k₃.wr, wr₂, k₁.wr]; exact hxw) (H := H)
    (by rw [k₅.mem]; exact fl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, k₅.mem] at tg
  have f₄ : Frame (absFrame (V .r30) (V .r31) 16 ++ tFrame (V .r30) (V .r31) 16) s.mem s₄.mem :=
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

end VG.Proof.Sm4Gcm.PPC64LE
