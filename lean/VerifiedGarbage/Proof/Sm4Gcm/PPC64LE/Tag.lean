module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on PPC64LE: the tag (`tag o`)

Untrusted: everything here is checked by Lean. AES-GCM's `tag o`
(`Proof/AesGcm/PPC64LE/Tag.lean`) with SM4's counter mode inlined: the
lengths block of `r24` and `r26` bytes absorbed, the accumulator `S` copied
to `W + o` and `CIPH_K(J₀)` XORed into it, from the counter block `J₀` at
the state (`tag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov lens)
open VG.Proof.AesGcm.PPC64LE (Env Lay Keeps' covers_left covers_prefix add_ofNat_assoc blockAt_frame
  blocksAt_one tFrame lens_ok j_tFrame bytesAt_copy2 ctr32_single write_8 WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (st w : Addr) (o : Nat) : List Region :=
  [⟨st, 32⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, xR w]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ (V .r29) J)
  frame : Frame (tagFrame (V .r30) (V .r31) o) m₀ s.mem

/-- After the lengths block: what the arguments of the counter mode need. -/
structure TagMid (V : Reg → BitVec 64) (sp : Addr) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hY : blockAt s.mem (V .r30 + BitVec.ofNat 64 16) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  hJ : blockAt s.mem (V .r30) = J
  hc : ciphOf s.mem (V .r29) = ciphOf m₀ (V .r29)
  frame : Frame (tFrame (V .r30) (V .r31) 16) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
  (X : XOk (V .r29) (V .r30) (V .r31))
include L

/-- The lengths block absorbed, before the copy. -/
theorem tagLens_ok {H J : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .r30) = J) :
    WP isa (lens 16) s (TagMid V sp H (blockAt s.mem (V .r30 + BitVec.ofNat 64 16)) J
      (s.gpr .r24).toNat (s.gpr .r26).toNat s.mem) := by
  refine WP.mono (lens_ok L (.inr rfl) he hH) fun s₁ ⟨he₁, _, hY₁, _, f₁⟩ => ?_
  exact ⟨he₁, hY₁, by rw [blockAt_frame f₁ (j_tFrame L), hJ], ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))), f₁⟩

omit L in
/-- The accumulator copied to `W + o`, and the arguments of SM4's counter mode. -/
theorem tagArgs_ok {o : Nat} (ho : o + 16 ≤ 128) (ho4 : o % 4 = 0) {s : State} (he : Env V sp s) :
    WP isa (.block (tagArgs o)) s fun s' =>
      s'.mem = (s.mem.writeW (V .r31 + BitVec.ofNat 64 o) (s.mem.readW (V .r30 + BitVec.ofNat 64 16) 64)).writeW
        (V .r31 + BitVec.ofNat 64 (o + 8))
        ((s.mem.writeW (V .r31 + BitVec.ofNat 64 o) (s.mem.readW (V .r30 + BitVec.ofNat 64 16) 64)).readW
          (V .r30 + BitVec.ofNat 64 24) 64) ∧
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = V .r30 ∧ s'.gpr .r5 = V .r31 + BitVec.ofNat 64 o ∧
      s'.gpr .r6 = BitVec.ofNat 64 1 ∧ s'.gpr .r7 = V .r31 + BitVec.ofNat 64 sO ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  have r₀ := he.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 24 + 8 ≤ 80 by decide)
  have w₀ := he.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have o₀ : o < 2 ^ 15 := by omega
  have o₁ : o + 8 < 2 ^ 15 := by omega
  have ho4' : (o + 8) % 4 = 0 := by omega
  apply WP.of_runBlock
  simp only [tagArgs, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.write, Size.bytes, h29, h30, h31, r₀, r₁, w₀, w₁, o₀, o₁, ho4, ho4', sO,
    Proof.Gcm.PPC64LE.read_8, write_8, mov, BitVec.or_self, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow,
    Nat.reduceMul, Nat.reduceMod, ↓reduceIte, and_self, implies_true, BitVec.setWidth_eq]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial,
    fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl, rfl⟩⟩

include X in
/-- The arguments of SM4's counter mode on the tag at `W + o`, with the counter block `J₀` at the state. -/
theorem ctrTag_mk {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env V sp s)
    (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = V .r30) (h5 : s.gpr .r5 = V .r31 + BitVec.ofNat 64 o)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 1) (h7 : s.gpr .r7 = V .r31 + BitVec.ofNat 64 sO)
    (hxw : Covers [xR (V .r31)] s.wr) :
    CtrCall s (V .r29) (V .r30) (V .r31 + BitVec.ofNat 64 o) (V .r31 + BitVec.ofNat 64 sO) 1 := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have hfx := X.fit
  have hf : (V .r31).toNat + 5824 ≤ 2 ^ 64 := hfx
  refine ⟨h3, h4, h5, h6, h7, by decide, ?_, ?_, ctx_x X, ?_, by simpa using st_x X (a := 0) (k := 16) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))
  · simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  · exact VG.Offset.disjoint _ (.inl (by simp only [sO]; omega)) (by omega) (by simp only [sO, sBytes]; omega)
  · have := L.cw; omega
  · have := L.sw; omega
  · have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [sO, sBytes]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2560) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (covers_prefix he.perm.st (by decide))) (Covers.cons (covers_left (he.perm.wC (by omega)))
        (Covers.cons (covers_left hxw) Covers.nil)))
  · exact Covers.cons (covers_prefix he.perm.st (by decide)) (Covers.cons (he.perm.wC (by omega))
      (Covers.cons hxw Covers.nil))

include X in
/-- The copy and SM4's counter mode on it. -/
theorem tagCall_ok {o : Nat} (ho : o = 0 ∨ o = 112) {H Y J : Block} {aLen cLen : Nat} {m₀ : Mem} {s : State}
    (h : TagMid V sp H Y J aLen cLen m₀ s) (hxw : Covers [xR (V .r31)] s.wr) :
    WP isa (.seq (.block (tagArgs o)) Impl.Sm4.PPC64LE.ctr32) s (TagOut V sp o H Y J aLen cLen m₀) := by
  have he := h.env
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine WP.seq (WP.mono (tagArgs_ok (by omega) (by omega) he) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, hg₂, hk₂⟩ => ?_)
  rw [show V .r31 + BitVec.ofNat 64 (o + 8) = V .r31 + BitVec.ofNat 64 o + BitVec.ofNat 64 8 from
      (add_ofNat_assoc _ _ _).symm,
    show V .r30 + BitVec.ofNat 64 24 = V .r30 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc]; rfl] at hm₂
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have f₂ : Frame [⟨V .r31 + BitVec.ofNat 64 o, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 o) 16 = bytesAt s.mem (V .r30 + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy2 _ (by
      rw [add_ofNat_assoc]; exact (L.st_w (a := 24) (n := 8) (d := o) (k := 8) (by decide) (by omega)).symm)]
  have dJo : (⟨V .r30, 16⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem (V .r30) = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, h.hJ]
  have hc₂ : ciphOf s₂.mem (V .r29) = ciphOf m₀ (V .r29) := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))), h.hc]
  have hcall := ctrTag_mk L X ho he₂ a3 a4 a5 a6 a7 (by rw [hk₂.wr]; exact hxw)
  refine WP.mono (ctr_wp hcall) fun s₃ g => ?_
  have gout := g.out; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s₂.mem (V .r29)) = ciphOf s₂.mem (V .r29) from rfl,
      hc₂, show blockAt s₂.mem (V .r31 + BitVec.ofNat 64 o) = blockAt s.mem (V .r30 + BitVec.ofNat 64 16)
        by rw [blockAt, blockAt, hT], h.hY]
  · have fA : Frame (tagFrame (V .r30) (V .r31) o) m₀ s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (V .r30) (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨V .r31 + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

include X in
/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env V sp s)
    (hxw : Covers [xR (V .r31)] s.wr)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .r30) = J) :
    WP isa (tag o) s (TagOut V sp o H (blockAt s.mem (V .r30 + BitVec.ofNat 64 16)) J
      (s.gpr .r24).toNat (s.gpr .r26).toNat s.mem) :=
  WP.seq (WP.mono (WP.with_rdwr (tagLens_ok L he hH hJ)) fun _ ⟨hm, _, hwr, _⟩ =>
    tagCall_ok L X ho hm (by rw [hwr]; exact hxw))

end

end VG.Proof.Sm4Gcm.PPC64LE
