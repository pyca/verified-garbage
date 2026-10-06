import VerifiedGarbage.Impl.RsaPss.AArch64
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-!
# RSASSA-PSS on AArch64: the working space and masks

`Rep m S V`: in memory `m`, byte `o` of our part of the working space `S`
(the first `oRsa` bytes) is `V o`; a store changes `V` where it writes
(`Rep.wb`, `Rep.wx`, `Rep.writeBytes`), and memory changed elsewhere keeps
it (`Rep.frame`). `Lay t F S`: the frame `F` and the working space `S` of a
state `t`, where the code runs, with `x20 = S`. The masks the code computes
without branches (`eq1_val`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes

/-- `p + o`. -/
abbrev off (p : Addr) (o : Nat) : Addr := p + BitVec.ofNat 64 o

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem off_inj (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : off p a = off p b ↔ a = b :=
  ⟨fun h => by
    have := congrArg (fun x => (x - p).toNat) h
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      at this
    exact this, fun h => h ▸ rfl⟩

/-! ## The working space, as bytes -/

/-- In `m`, byte `o` of our part of the working space at `S` is `V o`. -/
def Rep (m : Mem) (S : Addr) (V : Nat → Byte) : Prop := ∀ o < oRsa, m (off S o) = V o

/-- `V` with byte `o` replaced by `b`. -/
def upd (V : Nat → Byte) (o : Nat) (b : Byte) : Nat → Byte := fun x => if x = o then b else V x

theorem Rep.wb {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o : Nat} (ho : o < oRsa) (b : Byte) :
    Rep (m.writeW (off S o) b) S (upd V o b) := by
  intro x hx
  rw [writeW8_apply, upd]
  by_cases e : x = o
  · subst e; simp
  · rw [ite_eq_right fun h' => e ((off_inj S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega)).mp h'),
      ite_eq_right e]
    exact h x hx

/-- `V` with the bytes `xs` from `o`. -/
def updL (V : Nat → Byte) (o : Nat) (xs : List Byte) : Nat → Byte :=
  fun x => if o ≤ x ∧ x < o + xs.length then xs.getD (x - o) 0 else V x

theorem Rep.writeBytes {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o : Nat} {xs : List Byte}
    (ho : o + xs.length ≤ oRsa) : Rep (VG.WriteBytes.writeBytes m (off S o) xs) S (updL V o xs) := by
  intro x hx
  simp only [VG.WriteBytes.writeBytes, updL]
  by_cases e : o ≤ x
  · rw [show off S x = off (off S o) (x - o) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show x - o < 2 ^ 64 by unfold oRsa at *; omega)]
    by_cases e' : x - o < xs.length
    · rw [ite_eq_left e', ite_eq_left ⟨e, by omega⟩]
    · rw [ite_eq_right e', ite_eq_right (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show o + (x - o) = x by omega]
      exact h x hx
  · have : ¬ ((off S x - off S o).toNat < xs.length) := by
      rw [show off S x - off S o = BitVec.ofNat 64 (2 ^ 64 - (o - x)) by
        apply BitVec.eq_of_toNat_eq
        simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
        unfold oRsa at *; omega]
      simp only [BitVec.toNat_ofNat]; unfold oRsa at *; omega
    rw [ite_eq_right this, ite_eq_right (by omega)]
    exact h x hx

/-- Memory changed only apart from the working space keeps it. -/
theorem Rep.frame {m m' : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨S, oRsa⟩ r) : Rep m' S V := by
  intro x hx
  rw [← h x hx]
  exact hf.bytes (R := ⟨S, oRsa⟩) (fun r hr => hd r hr) (show oRsa ≤ 2 ^ 64 by decide) hx

/-- The same memory. -/
theorem Rep.congr {m : Mem} {S : Addr} {V V' : Nat → Byte} (h : Rep m S V) (e : ∀ o < oRsa, V o = V' o) :
    Rep m S V' := fun o ho => (h o ho).trans (e o ho)

/-- The bytes of the working space. -/
theorem Rep.bytes {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o n : Nat} (ho : o + n ≤ oRsa) :
    Spec.Rsa.bytesAt m (off S o) n = (List.range n).map fun i => V (o + i) := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega)

/-! ## Where the code runs -/

/-- The frame at `F` (`sp`) and our part of the working space at `S`
(`x20`), both writable, apart from each other and not wrapping around. -/
structure Lay (t : State) (F S : Addr) : Prop where
  sp : t.sp = F
  x20 : t.gpr .x20 = S
  fw : (⟨F, frameBytes⟩ : Region) ∈ t.wr
  sw : ∃ r ∈ t.wr, Region.Prefix ⟨S, oRsa⟩ r
  Fw : F.toNat + frameBytes ≤ 2 ^ 64
  Sw : S.toNat + oRsa ≤ 2 ^ 64
  dFS : Region.Disjoint ⟨F, frameBytes⟩ ⟨S, oRsa⟩

theorem Lay.congr {t t' : State} {F S : Addr} (L : Lay t F S) (hsp : t'.sp = t.sp) (hwr : t'.wr = t.wr)
    (h20 : t'.gpr .x20 = t.gpr .x20) : Lay t' F S :=
  ⟨hsp.trans L.sp, h20.trans L.x20, hwr ▸ L.fw, hwr ▸ L.sw, L.Fw, L.Sw, L.dFS⟩

/-- Bytes of the working space are writable. -/
theorem Lay.st {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    InRegions t.wr (off S o) n := by
  obtain ⟨⟨b, l⟩, hr, hb, hl⟩ := L.sw
  dsimp only at hb hl
  subst hb
  exact ⟨_, hr, Offset.contains_base _ (by omega) (by unfold oRsa at *; omega)⟩

theorem Lay.ld {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    InRegions (t.rd ++ t.wr) (off S o) n :=
  let ⟨r, hr, hc⟩ := L.st h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Words of the frame are writable and readable. -/
theorem Lay.fst {t : State} {F S : Addr} (L : Lay t F S) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions t.wr (off F d) n :=
  ⟨_, L.fw, Offset.contains_base _ h (by unfold frameBytes at *; omega)⟩

theorem Lay.fld {t : State} {F S : Addr} (L : Lay t F S) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (off F d) n :=
  let ⟨r, hr, hc⟩ := L.fst h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Masks -/

/-- `((a ⊕ b) - 1) >> 63`: 1 if `a = b`, 0 otherwise, for `a, b < 2^63`. -/
theorem eq1_val {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    ((a ^^^ b) - BitVec.ofNat 64 1) >>> 63 = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [BitVec.xor_self, ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    have hx : (a ^^^ b).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow ha hb
    have hn : (a ^^^ b).toNat ≠ 0 := fun e => h (by
      have : a ^^^ b = 0#64 := BitVec.eq_of_toNat_eq (by simpa using e)
      exact BitVec.xor_eq_zero_iff.mp this)
    generalize a ^^^ b = x at hx hn
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have h1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
    rw [h1, show (2 ^ 64 - 1 + x.toNat) % 2 ^ 64 = x.toNat - 1 by omega]
    show (x.toNat - 1) / 2 ^ 63 = 0
    exact Nat.div_eq_of_lt (by omega)

end VG.Proof.RsaPss.AArch64
