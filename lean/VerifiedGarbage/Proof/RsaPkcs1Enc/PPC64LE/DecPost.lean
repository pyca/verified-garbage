module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecPriv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: after the private-key operation

From the private-key operation's result in its slot to the output, the
function writes only the first `scrBytes` bytes of `scratch`, the stack
below its frame and its slots `oI` and `oNB` (`Safe`): through all of it,
`Fr2`, the result `R` in its slot and `EM` in `out` stay as they are
(`Post`, `Post.step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

/-- `scratch + a`. -/
abbrev scA (s : State) (a : Nat) : Addr := stackArg s 13 + BitVec.ofNat 64 a

/-- The part of `scratch` used. -/
abbrev SC (s : State) : Region := ⟨stackArg s 13, scrBytes⟩

/-- The stack below our frame, which the private-key operation used and the
hash functions' frames use. -/
abbrev LOW (s : State) : Region :=
  ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem scr_le {s : State} (h : DPre s) : scrBytes ≤ (stackArg s 14).toNat * 8 := by
  have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *; unfold scrBytes; omega

theorem sc_sub {s : State} (h : DPre s) : Region.Sub (SC s) (sR s) := Region.sub_prefix (scr_le h)

theorem scSub {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA s a, n⟩ (SC s) :=
  Offset.sub_base _ ha

theorem scD {s : State} (h : DPre s) {a n b m : Nat} (hab : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes)
    (hb : b + m ≤ scrBytes) : Region.Disjoint ⟨scA s a, n⟩ ⟨scA s b, m⟩ := by
  have := h.ws; have := scr_le h
  exact Offset.disjoint _ hab (by omega) (by omega)

theorem low_sub (s : State) {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) :
    Region.Sub (below (fb s) n) (LOW s) :=
  Offset.sub_below _ hn (by omega)

/-- A word of our frame misses the stack below it. -/
theorem fr_low (s : State) {d n : Nat} (hd : d + n ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ (LOW s) :=
  Offset.disjoint_below _ (by unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega)

/-- What a step after the private-key operation may write. -/
def Safe (s : State) (r : Region) : Prop :=
  Region.Sub r (SC s) ∨ Region.Sub r (LOW s) ∨
    ∃ d, oI ≤ d ∧ d + r.len ≤ oLr ∧ r.base = fb s + BitVec.ofNat 64 d

theorem safe_frame {s : State} (h : DPre s) {r : Region} (hr : Safe s r) {d n : Nat}
    (hd : d + n ≤ oI ∨ oLr ≤ d) (hn : d + n ≤ frameBytes) : Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact ((h.ks.sub_left (frame_sub s hn)).sub_right (sc_sub h)).sub_right hr
  · exact (fr_low s hn).sub_right hr
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    unfold oI oLr at *; unfold frameBytes at hn
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem safe_out {s : State} (h : DPre s) {r : Region} (hr : Safe s r) : Region.Disjoint (oR s) r := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact (h.os.sub_right (sc_sub h)).sub_right hr
  · exact h.ko.symm.sub_right (sub_trans hr (callee_sub s))
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    exact h.ko.symm.sub_right (frame_sub s (by unfold oLr frameBytes at *; omega))

theorem safe_in {s : State} (h : DPre s) {r : Region} (hr : Safe s r) :
    ∃ X ∈ [kR s, oR s, sR s], Region.Sub r X := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact ⟨_, by simp, sub_trans hr (sc_sub h)⟩
  · exact ⟨_, by simp, sub_trans hr (callee_sub s)⟩
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    exact ⟨_, by simp, frame_sub s (by unfold oLr frameBytes at *; omega)⟩

theorem savedSlots_words : ∀ p ∈ savedSlots, p.2 + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR ∨ oLr ≤ p.2 := by
  decide

/-- The slots stay through a step that writes none of their words. -/
theorem Slots.words {s : State} {m m' : Mem} (S : Slots s m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ d, d + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR ∨ oLr ≤ d → d + 8 ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r) : Slots s m' := by
  have one : ∀ {d : Nat}, d + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun h₁ =>
    hf.readW (Region.contains_self _ _) (fun r hr => hd r hr _ (.inl h₁)
      (by unfold Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR frameBytes at *; omega)) (by decide)
  refine ⟨S.sv.frame hf fun p hp r hr => hd r hr _ (savedSlots_words p hp) ?_, ?_, ?_, ?_⟩
  · have : p ∈ savedSlots := hp
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [one (by decide)]; exact S.dl
  · rw [one (by decide)]; exact S.inp
  · rw [one (by decide)]; exact S.scr

/-- The slots stay through a step that writes only where it may. -/
theorem Slots.safe {s : State} (h : DPre s) {m m' : Mem} (S : Slots s m) {ws : List Region}
    (hf : Frame ws m m') (hs : ∀ r ∈ ws, Safe s r) : Slots s m' :=
  S.words hf fun r hr d hd hn => safe_frame h (hs r hr)
    (hd.imp_left fun h' => by unfold Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR oI at *; omega) hn

section
variable {s : State} {m : Mem} (S : Slots s m)
include S

theorem Slots.out : m.readW (fb s + BitVec.ofNat 64 oOut) 64 = s.gpr .r3 :=
  (S.sv (.r3, oOut) (by decide)).trans (by simp [slotVal])
theorem Slots.ml : m.readW (fb s + BitVec.ofNat 64 oML) 64 = s.gpr .r5 :=
  (S.sv (.r5, oML) (by decide)).trans (by simp [slotVal])
theorem Slots.k : m.readW (fb s + BitVec.ofNat 64 oK) 64 = s.gpr .r7 :=
  (S.sv (.r7, oK) (by decide)).trans (by simp [slotVal])
theorem Slots.d : m.readW (fb s + BitVec.ofNat 64 oD) 64 = s.gpr .r10 :=
  (S.sv (.r10, oD) (by decide)).trans (by simp [slotVal])
theorem Slots.lr : m.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr :=
  (S.sv (.r0, oLr) (by decide)).trans (by simp [slotVal])

end

/-- A slot of the frame can be read. -/
theorem slotIn {s u : State} (hwr : u.wr = fr s :: s.wr) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 d) 8 := by
  rw [hwr]; exact in_fr' s _ _ h₁ h₂

theorem slotOut {s u : State} (hwr : u.wr = fr s :: s.wr) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions u.wr (fb s + BitVec.ofNat 64 d) 8 := by
  rw [hwr]; exact in_fr s _ h₁ h₂

/-- After the private-key operation: `Fr2`, its result `R` in its slot and
`EM` in `out`. -/
structure Post (s : State) (R : BitVec 64) (EM : List Byte) (u : State) : Prop extends Fr2 s u where
  r : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R
  em : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat = EM
  /-- The result is a 32-bit value. -/
  rb : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63

section
variable {s : State} {R : BitVec 64} {EM : List Byte} {t t' : State}

/-- A step that writes only where it may keeps `Post`. -/
theorem Post.step (h : DPre s) (hc : Post s R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe s r) : Post s R EM t' := by
  refine ⟨⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hc.mem.trans (hf.sub fun r hr => safe_in h (hs r hr)), hc.sl.safe h hf hs⟩, ?_, ?_, hc.rb⟩
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => safe_frame h (hs X hX) (.inl (by decide)) (by decide))
      (by decide)]
    exact hc.r
  · rw [← hc.em]
    exact bytes_of_frame (s := t) hf (fun X hX => by have := safe_out h (hs X hX); rwa [← outR_eq h] at this)
      (by have := h.wo; rw [h.h4] at this; omega)

/-- Code that changes only registers but the callee-saved ones keeps `Post`. -/
theorem Post.regs (hc : Post s R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Post s R EM t' :=
  ⟨⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hm ▸ hc.mem, hm ▸ hc.sl⟩, by rw [hm]; exact hc.r, by rw [hm]; exact hc.em, hc.rb⟩

end

/-- A range of `scratch` is writable. -/
theorem scCov {s u : State} (h : DPre s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    Covers [⟨scA s a, n⟩] u.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨sR s, by rw [hwr, h.hwr]; simp, a, rfl, by have := scr_le h; dsimp only; omega⟩

theorem scIn {s u : State} (h : DPre s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    InRegions u.wr (scA s a) n :=
  scCov h hwr ha _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem scInR {s u : State} (h : DPre s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    InRegions (u.rd ++ u.wr) (scA s a) n :=
  let ⟨r, hr, hc⟩ := scIn h hwr ha
  ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
