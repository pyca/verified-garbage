module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: absorbing the text (`textAbsorb`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/TextAbsorb.lean`): `textAbsorb` absorbs the `len` bytes
(`r19`) at `data` (`r20`) into GHASH as text: before the first text
(`text_len`, `r23`, 0) it pads the additional data (of `aad_len` bytes,
`r22`) first (`firstFlush`), and it does nothing for no bytes
(`textAbsorb_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (st w : Addr) : List Region :=
  [⟨st + BitVec.ofNat 64 16, 16⟩, ⟨st + BitVec.ofNat 64 32, 16⟩, ⟨w + BitVec.ofNat 64 96, 16⟩,
    ⟨w + BitVec.ofNat 64 512, 256⟩]

/-- After `textAbsorb`, from `m₀`: GHASH has absorbed `x`. -/
structure TaOut (V : Reg → BitVec 64) (sp : Addr) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H x
  frame : Frame (taFrame (V .r30) (V .r31)) m₀ s.mem

theorem abs_taFrame {st w : Addr} {m m' : Mem} (h : Frame (absFrame st w 16) m m') :
    Frame (taFrame st w) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem t_taFrame {st w : Addr} {m m' : Mem} (h : Frame (tFrame st w 16) m m') : Frame (taFrame st w) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', e, q⟩ := h
  exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- A frozen register, as the number it holds. -/
theorem Env.ofNat {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) {r : Reg} (hr : r ∈ frozen) :
    s.gpr r = BitVec.ofNat 64 (V r).toNat := by
  rw [he.fr r hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem textArgs_ok {s : State} :
    WP isa (.block textArgs) s fun s' =>
      s'.gpr .r24 = s.gpr .r20 ∧ s'.gpr .r25 = s.gpr .r19 ∧
      s'.gpr .r26 = BitVec.ofNat 64 ((s.gpr .r23).toNat % 16) ∧
      (∀ r, r ≠ .r0 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (s.gpr .r23)
  simp only [textArgs]
  crun [mov, BitVec.or_self, hand]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

theorem textAbsorb_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} {H : Block} {a ct : List Byte} (he : Env V sp s)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H)
    (hd : DataOk (V .r30) (V .r31) s (V .r20) (V .r19).toNat)
    (ha : a.length % 16 = (V .r22).toNat % 16) (hP : (V .r23).toNat = ct.length) :
    WP isa textAbsorb s (TaOut V sp H (ghashInput a ct)
      (ghashInput a (ct ++ bytesAt s.mem (V .r20) (V .r19).toNat)) s.mem) := by
  have hn := (V .r19).isLt
  refine WP.ite _ (eval_zero (he.ofNat (r := .r19) (by decide)) hn) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : (V .r19).toNat = 0 := by simpa using ht
    rw [h0]
    refine WP.block_nil ⟨he, hH, fun hab => ?_, Frame.refl _ _⟩
    simp only [bytesAt, List.range_zero, List.map_nil, List.append_nil]; exact hab
  have h0 : (V .r19).toNat ≠ 0 := by simpa using hf'
  -- the additional data padded, before the first text
  let x' := if ct = [] then a ++ zeros (padLen a.length) else ghashInput a ct
  have hx' : x'.length % 16 = ct.length % 16 := by
    by_cases hc : ct = []
    · subst hc; simp only [x', ite_true, List.length_append, Proof.Gcm.length_zeros, List.length_nil]
      exact Proof.Gcm.length_pad_mod _
    · simp only [x', hc, ite_false, Proof.Gcm.ghashInput_of_ne hc, List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length; omega
  have hlt := Nat.mod_lt a.length (show 16 > 0 by decide)
  have mid : WP isa (.ite (.zero .d .r23) firstFlush (.block [])) s fun s₄ => Env V sp s₄ ∧
      blockAt s₄.mem (V .r29 + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (ghashInput a ct) →
        Absorbed s₄.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H x') ∧
      Frame (tFrame (V .r30) (V .r31) 16) s.mem s₄.mem := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .r23) (by decide)) (V .r23).isLt) (fun ht => ?_) (fun hf₂ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have h22 := he.fr .r22 (by decide)
      have hand := and15 (V .r22)
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 (a.length % 16) ∧ (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧
            Keeps s s₃ := by
        crun [h22, hand, ha]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.seq (WP.mono h₃ fun s₃ ⟨h26, hg₃, hk₃⟩ => ?_)
      have he₃ := he.keep (fun r hr => hg₃ r (by revert r; decide) (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
      refine WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := a) (H := H) ⟨he₃, by rw [hk₃.mem]; exact hH⟩ h26)
        fun s₄ hfl => ?_
      have hf₄ := hfl.frame
      rw [hk₃.mem] at hf₄
      refine ⟨hfl.env, hfl.hH, fun hab => ?_, hf₄⟩
      simp only [x', hc, ite_true]
      refine hfl.abs ?_
      rw [hk₃.mem]; subst hc; exact hab
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf₂
      refine WP.block_nil ⟨he, hH, fun hab => ?_, Frame.refl _ _⟩
      simp only [x', hc, ite_false]; exact hab
  refine WP.seq (WP.mono (WP.with_rdwr mid) fun s₄ ⟨⟨he₄, hH₄, hab₄, hf₄⟩, rd₄, wr₄, _⟩ => ?_)
  -- the arguments of `absorb`
  have h20 := he₄.fr .r20 (by decide); have h19 := he₄.ofNat (r := .r19) (by decide)
  have h23 := he₄.fr .r23 (by decide)
  have hand := and15 (V .r23)
  have h₅ : WP isa (.block textArgs) s₄ fun s₅ =>
      s₅.gpr .r24 = V .r20 ∧ s₅.gpr .r25 = BitVec.ofNat 64 (V .r19).toNat ∧
      s₅.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
      (∀ r, r ≠ .r0 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    simp only [textArgs]
    crun [h20, h19, h23, hand, mov, BitVec.or_self]
    exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h25₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := he₄.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  have hai : AbsIn V sp 16 H x' (V .r20) (V .r19).toNat s₅ :=
    ⟨he₅, h24₅, h25₅, by rw [h26₅, hx', hP], hd.of_eq (hk₅.rd.trans rd₄) (hk₅.wr.trans wr₄),
      by rw [hk₅.mem]; exact hH₄⟩
  refine WP.mono (absorb_ok L (.inr rfl) hai) fun s₆ ho => ?_
  have hdat : bytesAt s₅.mem (V .r20) (V .r19).toNat = bytesAt s.mem (V .r20) (V .r19).toNat := by
    rw [hk₅.mem]
    exact bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.st.sub_right (Lay.stSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))) (by have := hd.lt; omega)
  have hne : bytesAt s.mem (V .r20) (V .r19).toNat ≠ [] := by
    intro e; have := congrArg List.length e; rw [length_bytesAt] at this; exact h0 (by simpa using this)
  refine ⟨ho.env, ?_, ?_, ?_⟩
  · rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl)), hk₅.mem, hH₄]
  · intro hab
    have := ho.abs (by rw [hk₅.mem]; exact hab₄ hab)
    rw [hdat] at this
    rw [Proof.Gcm.ghashInput_append _ _ _ hne]
    exact this
  · have f₆ := ho.frame
    rw [hk₅.mem] at f₆
    exact (t_taFrame hf₄).trans (abs_taFrame f₆)

end

end VG.Proof.AesGcm.PPC64LE
