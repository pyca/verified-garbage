module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: the pieces of `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/OneShot.lean`): both keep a streaming state at `W + 16`;
`oneAad` writes `J₀` and absorbs the additional data, padded (`oneAad_ok`),
`oneCrypt` runs counter mode over the data from the first counter block
(`oneCrypt_ok`), and `oneTag o` absorbs the data as ciphertext, padded, then
the lengths block, and writes the tag to `W + o` (`oneTag_ok`). The pieces
are stated for an environment `Env V sp s`, whose registers the entries of
`seal` and `open` fill.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock padded)

theorem abs16_j0 {st w : Addr} : ∀ r ∈ absFrame st w 16, ∃ r' ∈ j0Frame st w, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_j0 {st w : Addr} : ∀ r ∈ tFrame st w 16, ∃ r' ∈ j0Frame st w, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- A buffer apart from the state and `W` is apart from what `j0` writes. -/
theorem data_j0 {st w : Addr} {s : State} {D : Addr} {n : Nat} (hd : DataOk st w s D n) :
    ∀ r ∈ j0Frame st w, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.st
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))

/-- After `oneAad`, from `m₀`: `J₀` of `iv`, the first counter block, and the
additional data `a` absorbed and padded. -/
structure OA (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv a : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  j : blockAt s.mem (V .r30) = j0 H iv
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv)
  abs : Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))
  frame : Frame (j0Frame (V .r30) (V .r31)) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

/-- The counter blocks are apart from what `absorb 16` and `flush 16` write. -/
theorem stb_abs16 {d : Nat} (hd : d = 0 ∨ d = 48) :
    ∀ r ∈ absFrame (V .r30) (V .r31) 16, (⟨V .r30 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

theorem stb_t16 {d : Nat} (hd : d = 0 ∨ d = 48) :
    ∀ r ∈ tFrame (V .r30) (V .r31) 16, (⟨V .r30 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

/-- `oneAad`: `J₀` of the `n`-byte nonce at `Np`, then the additional data
(`aad_len`, `r22`, bytes at `r21`) absorbed and padded. -/
theorem oneAad_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) (h24 : s.gpr .r24 = Np)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 n) (h18 : V .r18 = BitVec.ofNat 64 n) (hN : DataOk (V .r30) (V .r31) s Np n)
    (hA : DataOk (V .r30) (V .r31) s (V .r21) (V .r22).toNat) :
    WP isa oneAad s (OA V sp H (bytesAt s.mem Np n) (bytesAt s.mem (V .r21) (V .r22).toNat) s.mem) := by
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L ⟨he, hH, h24, h25, h18, hN⟩)) fun s₂ ⟨jo, rd₂, wr₂, _⟩ => ?_)
  have h21 := jo.env.fr .r21 (by decide)
  have h22 := jo.env.ofNat (r := .r22) (by decide)
  have h₃ : WP isa (.block [mov .r24 .r21, mov .r25 .r22, .li .r26 0]) s₂ fun s₃ =>
      s₃.gpr .r24 = V .r21 ∧ s₃.gpr .r25 = BitVec.ofNat 64 (V .r22).toNat ∧ s₃.gpr .r26 = BitVec.ofNat 64 0 ∧
        (∀ r, r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    crun [mov, BitVec.or_self, h21, h22]
    exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ => ?_)
  have he₃ := jo.env.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₃.sp k₃.rd k₃.wr
  have hAm : bytesAt s₃.mem (V .r21) (V .r22).toNat = bytesAt s.mem (V .r21) (V .r22).toNat := by
    rw [k₃.mem]; exact bytesAt_frame jo.frame (data_j0 hA) (by have := hA.lt; omega)
  have ai : AbsIn V sp 16 H [] (V .r21) (V .r22).toNat s₃ :=
    ⟨he₃, a24, a25, by rw [a26]; rfl, hA.of_eq (k₃.rd.trans rd₂) (k₃.wr.trans wr₂), by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) ai) fun s₄ ab => ?_)
  rw [hAm, List.nil_append] at ab
  have h22' := ab.env.fr .r22 (by decide)
  have hand := and15 (V .r22)
  have h₅ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s₄ fun s₅ =>
      s₅.gpr .r26 = BitVec.ofNat 64 ((V .r22).toNat % 16) ∧
        (∀ r, r ≠ .r0 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    crun [h22', hand]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨a26', g₅, k₅⟩ => ?_)
  have he₅ := ab.env.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have hH₄ : blockAt s₄.mem (V .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl)), k₃.mem]; exact jo.hH
  refine WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := bytesAt s.mem (V .r21) (V .r22).toNat) (H := H)
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [a26', length_bytesAt])) fun s₆ fl => ?_
  have flf := fl.frame
  rw [k₅.mem] at flf
  have abf := ab.frame
  rw [k₃.mem] at abf
  have blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (V .r30 + BitVec.ofNat 64 d) =
      blockAt s₂.mem (V .r30 + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame flf (stb_t16 L hd), blockAt_frame abf (stb_abs16 L hd)]
  refine ⟨fl.env, fl.hH, ?_, ?_, fl.abs (by rw [k₅.mem]; exact ab.abs (by
    rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y)), ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [BitVec.add_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact (jo.frame.trans (abf.sub abs16_j0)).trans (flf.sub t16_j0)

end

/-- After `oneCrypt`, from `m₀`. -/
structure OC (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .r27) (V .r23).toNat =
    gctr (ciphOf m₀ (V .r29) R) icb (bytesAt m₀ (V .r27) (V .r23).toNat)
  frame : Frame (crFrame (V .r30) (V .r31) (V .r27) (V .r23).toNat) m₀ s.mem

theorem dataArgs_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block dataArgs) s fun s' =>
      s'.gpr .r24 = V .r27 ∧ s'.gpr .r25 = BitVec.ofNat 64 (V .r23).toNat ∧ s'.gpr .r26 = BitVec.ofNat 64 0 ∧
        (∀ r, r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h27 := he.fr .r27 (by decide)
  have h23 := he.ofNat (r := .r23) (by decide)
  simp only [dataArgs]
  crun [mov, BitVec.or_self, h27, h23]
  exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

/-- `oneCrypt`: counter mode over the data (`len`, `r23`, bytes at `r27`) from
the counter block `icb`. -/
theorem oneCrypt_ok {R : Nat} {s : State} (he : Env V sp s) (h28 : V .r28 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    {icb : Block} (hcb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC V sp R icb s.mem) := by
  refine WP.seq (WP.mono (dataArgs_ok he) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    k₁.sp k₁.rd k₁.wr
  have ci : CrIn V sp R icb 0 (V .r27) (V .r23).toNat s₁ :=
    ⟨he₁, a24, a25, by rw [a26], h28, hR, hd.of_eq k₁.rd k₁.wr⟩
  refine WP.mono (crypt_ok L ci) fun s₂ co => ?_
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (V .r30 + BitVec.ofNat 64 64) (ciphOf s.mem (V .r29) R) hcb
  exact ⟨co.env, by rw [co.out c0, ← Proof.Gcm.gctr_eq], co.frame⟩

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w : Addr) (o : Nat) : List Region :=
  [⟨st, 48⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 2048⟩]

theorem abs_otSub {st w : Addr} {o : Nat} : ∀ r ∈ absFrame st w 16, ∃ r' ∈ otFrame st w o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

theorem t_otSub {st w : Addr} {o : Nat} : ∀ r ∈ tFrame st w 16, ∃ r' ∈ otFrame st w o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

theorem tag_otSub {st w : Addr} {o : Nat} : ∀ r ∈ tagFrame st w o, ∃ r' ∈ otFrame st w o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`
(`r27`), from the counter block `J`. -/
structure OT (V : Reg → BitVec 64) (sp : Addr) (o R : Nat) (H : Block) (a : List Byte) (J : Block) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt m₀ (V .r27) (V .r23).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (V .r27) (V .r23).toNat).length)] ^^^ ciphOf m₀ (V .r29) R J)
  frame : Frame (otFrame (V .r30) (V .r31) o) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

theorem oneTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a : List Byte} {s : State} (he : Env V sp s)
    (h28 : V .r28 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) (hl : (V .r22).toNat = a.length)
    (hab : Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hd : DataOk (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    WP isa (oneTag o) s (OT V sp o R H a (blockAt s.mem (V .r30)) s.mem) := by
  have dC : ∀ r ∈ otFrame (V .r30) (V .r31) o, (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
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
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) ai) fun s₂ ab => ?_)
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
  refine WP.seq (WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := (a ++ zeros (padLen a.length)) ++ ct) (H := H)
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [a26', hlx])) fun s₄ fl => ?_)
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
  refine WP.mono (tag_ok L ho he₅ h28 hR (H := H) (by rw [k₅.mem]; exact fl.hH) rfl) fun s₆ tg => ?_
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
        · obtain ⟨r', hr', hs⟩ := t_otSub (o := o) r hr; exact (dC r' hr').sub_right hs) hR,
      blockAt_frame f₄ dJ, hl]
    simp only [ct, length_bytesAt]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    rcases List.mem_append.mp hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr

end

end VG.Proof.AesGcm.PPC64LE
