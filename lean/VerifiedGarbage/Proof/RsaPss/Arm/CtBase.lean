module

public import VerifiedGarbage.Proof.RsaPss.Arm.Prims
public import VerifiedGarbage.Proof.RsaPss.Arm.Hash
public import VerifiedGarbage.Proof.RsaPss.CtPad
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Memory

/-!
# RSASSA-PSS on ARMv7: hashing a message of secret length, the setting

The hash function's sizes (`PssHash.B`, …); ranges of our part of
`scratch` as buffers (`Geo.wbuf`); facts about memory that writes elsewhere
keep (`bytes_keep`, `slot_keep`); and the bytes of `Y` after the padding
loop (`padY`), which are the padded message over its blocks (`padY_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.MdStream (Md)

namespace PssHash

variable (h : PssHash)

abbrev B : Nat := h.H.md.st.B
abbrev D : Nat := h.H.md.st.D
abbrev N : Nat := h.H.md.N
abbrev L : Nat := h.H.md.L

/-- `omega` does not see through abbreviations: the sizes as one form. -/
theorem eqs : h.H.md.B = h.B ∧ h.H.md.D = h.D ∧ blk h.H = h.B ∧ dig h.H = h.D ∧ hvN h.H = h.N ∧ lenL h.H = h.L :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev md : Md h.B h.N h.L := h.ok.md

theorem B_cases : h.B = 64 ∨ h.B = 128 := h.ok.sizes.B
theorem N_le : h.N ≤ 64 := h.ok.sizes.N64
theorem L_le : h.L ≤ 16 := h.ok.sizes.L16
theorem D_le : h.D ≤ h.N := h.ok.sizes.DN
theorem D_pos : 0 < h.D := h.ok.sizes.D0
theorem NL : h.N + h.L ≤ h.B := h.ok.sizes.NL
theorem so_le : h.H.md.so ≤ 512 := by have := h.ok.sizes.so; have := h.ok.sizes.W; omega
theorem B_le : h.B ≤ 128 := by rcases h.B_cases with e | e <;> omega
theorem B_ge : 64 ≤ h.B := by rcases h.B_cases with e | e <;> omega
theorem S_eq : h.H.md.st.S = h.N + h.B := h.ok.sizes.S

theorem lg : lgB h.H = 6 ∧ h.B = 64 ∨ lgB h.H = 7 ∧ h.B = 128 := by
  unfold lgB
  rcases h.B_cases with e | e
  · exact .inl ⟨by show Nat.log2 h.B = 6; rw [e]; decide, e⟩
  · exact .inr ⟨by show Nat.log2 h.B = 7; rw [e]; decide, e⟩

theorem pow_lg : 2 ^ lgB h.H = h.B := by rcases h.lg with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] <;> rfl

theorem lg_range : 1 ≤ lgB h.H ∧ lgB h.H ≤ 31 := by rcases h.lg with ⟨a, _⟩ | ⟨a, _⟩ <;> rw [a] <;> decide

end PssHash

theorem offs : oCW = 0 ∧ oSt = 512 ∧ oSel = 768 ∧ oDig = 832 ∧ oLen = 896 ∧ oEm = 1024 ∧ oY = 2048 ∧
    oRsa = 8192 ∧ frameBytes = 128 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers, and the hash function's sizes in one form. -/
macro "pomega" : tactic => `(tactic| (have _ : VG.Impl.RsaPss.Arm.oCW = 0 := rfl; have _ : VG.Impl.RsaPss.Arm.oSt = 512 := rfl; have _ : VG.Impl.RsaPss.Arm.oSel = 768 := rfl; have _ : VG.Impl.RsaPss.Arm.oDig = 832 := rfl; have _ : VG.Impl.RsaPss.Arm.oLen = 896 := rfl; have _ : VG.Impl.RsaPss.Arm.oEm = 1024 := rfl; have _ : VG.Impl.RsaPss.Arm.oY = 2048 := rfl; have _ : VG.Impl.RsaPss.Arm.oRsa = 8192 := rfl; have _ : VG.Impl.RsaPss.Arm.frameBytes = 128 := rfl; (try simp only [VG.Impl.RsaPss.Arm.blk, VG.Impl.RsaPss.Arm.dig, VG.Impl.RsaPss.Arm.hvN, VG.Impl.RsaPss.Arm.lenL, VG.Impl.Pbkdf2.Md.Arm.Hash.B, VG.Impl.Pbkdf2.Md.Arm.Hash.D, VG.Proof.RsaPss.Arm.PssHash.B, VG.Proof.RsaPss.Arm.PssHash.D, VG.Proof.RsaPss.Arm.PssHash.N, VG.Proof.RsaPss.Arm.PssHash.L] at *); omega))

variable {L : Lay} {scr : BitVec 32}

namespace Geo

variable (hg : Geo L scr)
include hg

theorem scr_lt {o : Nat} (h : o ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat = scr.toNat + o := by
  have := hg.fit; unfold oRsa at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem byteAt_scr {o i : Nat} (h : o + i < oRsa) : byteAt (scr + BitVec.ofNat 32 o) i = sa scr (o + i) := by
  rw [byteAt, hg.addr (by omega), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A range of our part of `scratch`, as a buffer the body writes. -/
theorem wbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : WBuf L (scr + BitVec.ofNat 32 o) n := by
  obtain ⟨σ, ok⟩ := hg.ok
  obtain ⟨k, hk, hR⟩ := hg.sub
  have fit := hg.fit
  unfold oRsa at h hk fit
  refine ⟨by rw [hg.scr_lt (by unfold oRsa; omega)]; omega, by omega, ⟨_, List.mem_cons_of_mem _ hR, ?_⟩, ?_⟩
  · rw [hg.addr (by unfold oRsa; omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [hg.addr (by unfold oRsa; omega)]
    exact hg.slot ok (o := o) (n := n) (by unfold oRsa; omega) (by rw [hg.F]; decide)

theorem rbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : RBuf L (scr + BitVec.ofNat 32 o) n := (hg.wbuf h hn).rbuf

end Geo

/-! ## Facts that writes elsewhere keep -/

theorem bytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = f i) : ∀ i < n, m' (a + BitVec.ofNat 64 i) = f i :=
  fun i hi => (hf.bytes (R := ⟨a, n⟩) hd hn hi).trans (h i hi)

theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat} {v : BitVec 32}
    (hd : ∀ r ∈ rs, (slotR L d).Disjoint r) (h : m.readW (L.fr d) 32 = v) : m'.readW (L.fr d) 32 = v := by
  rw [hf.readW (r := slotR L d) (Region.contains_self _ _) hd (by decide)]; exact h

/-- A byte of our part of `scratch` after a byte is written there. -/
theorem sa_write (scr : BitVec 32) (m : Mem) {o i : Nat} (b : Byte) (ho : o < 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (sa scr o) b) (sa scr i) = if i = o then b else m (sa scr i) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases e : i = o
  · subst e; simp
  · rw [ite_eq_right (Offset.add_ofNat_ne _ hi ho e), ite_eq_right e]

/-- A byte written within a range of our part of `scratch`. -/
theorem frame_byte (scr : BitVec 32) (m : Mem) {o n x : Nat} (b : Byte) (h₁ : o ≤ x) (h₂ : x < o + n)
    (hn : o + n < 2 ^ 64) : Frame [sR scr o n] m (m.writeW (sa scr x) b) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ (by omega) (by omega))

/-- Bytes of our part of `scratch` kept by writes elsewhere. -/
theorem sbytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o n) r) (hn : o + n < 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (sa scr (o + i)) = f i) : ∀ i < n, m' (sa scr (o + i)) = f i := fun i hi => by
  rw [← h i hi]
  refine hf _ fun r hr hc => hd r hr _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega)) hc

/-- A hash value kept by writes elsewhere. -/
theorem stateAt_keep (h : PssHash) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o h.N) r) : h.md.stateAt m' (sa scr o) = h.md.stateAt m (sa scr o) :=
  h.md.stateAt_congr fun _ hi => hf.bytes (R := sR scr o h.N) hd (by show h.N ≤ 2 ^ 64; have := h.N_le; omega) hi

/-- A frame within a sub-list of regions. -/
theorem Frame.subset {rs rs' : List Region} {m m' : Mem} (h : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ rs') :
    Frame rs' m m' := h.mono hs

/-! ## The padded message in `Y` -/

/-- Byte `j` of the block at `oLen`: zeros, then the length field `lenB`. -/
def lenBlk (B L : Nat) (lenB : List Byte) (j : Nat) : Byte :=
  if j < B - L then 0 else lenB.getD (j - (B - L)) 0

/-- Byte `i` of `Y` after the padding loop, for the message `msg` followed by
zeros: `0x80` ORed into byte `ℓ`, and the block at `oLen` into the last
block of the padded message. -/
def padY (B L : Nat) (msg lenB : List Byte) (i : Nat) : Byte :=
  msg.getD i 0 ||| (if i = msg.length then 0x80 else 0) |||
    (if i / B = (msg.length + L) / B then lenBlk B L lenB (i % B) else 0)

theorem or_zero (x : Byte) : x ||| 0 = x := by revert x; decide
theorem zero_or (x : Byte) : 0 ||| x = x := by revert x; decide

theorem getD_ge {l : List Byte} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Over the blocks of the padded message, `padY` is the padded message. -/
theorem padY_eq {B L : Nat} (hB : 0 < B) (hLB : L < B) (msg lenB : List Byte) {i : Nat}
    (hi : i < B * ((msg.length + L) / B + 1)) :
    padY B L msg lenB i = RsaPss.padded B L msg lenB i := by
  have hlt := Nat.lt_mul_div_succ (msg.length + L) hB
  have hge := Nat.mul_div_le (msg.length + L) B
  generalize hfb : (msg.length + L) / B = fb at hlt hge hi
  have hdiv : i / B ≤ fb := by
    have := (Nat.div_lt_iff_lt_mul hB).mpr (show i < (fb + 1) * B by rw [Nat.mul_comm]; exact hi)
    omega
  have hmod := Nat.div_add_mod i B
  have hmodl := Nat.mod_lt i hB
  have e2 : B * (fb + 1) = B * fb + B := Nat.mul_succ _ _
  rw [Nat.mul_comm] at hge
  simp only [padY, RsaPss.padded, RsaPss.lastBlk, hfb, lenBlk]
  by_cases h1 : i < msg.length
  · rw [ite_eq_left h1, ite_eq_right (by omega)]
    by_cases h3 : i / B = fb
    · have e1 : B * (i / B) = B * fb := by rw [h3]
      rw [ite_eq_left h3, ite_eq_left (by omega), or_zero, or_zero]
    · rw [ite_eq_right h3, or_zero, or_zero]
  · rw [ite_eq_right h1, getD_ge (by omega), zero_or]
    by_cases h2 : i = msg.length
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : i / B = fb
      · have e1 : B * (i / B) = B * fb := by rw [h3]
        rw [ite_eq_left h3, ite_eq_left (by omega), or_zero]
      · rw [ite_eq_right h3, or_zero]
    · rw [ite_eq_right h2, ite_eq_right h2, zero_or]
      by_cases h3 : i / B = fb
      · rw [ite_eq_left h3]
        have e1 : B * (i / B) = B * fb := by rw [h3]
        have hm : i % B = i - B * fb := by omega
        by_cases h4 : B * fb + B - L ≤ i ∧ i < B * fb + B
        · rw [ite_eq_right (by omega), ite_eq_left h4]
          congr 1; omega
        · rw [ite_eq_right h4, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by
          intro ⟨h5, _⟩
          exact h3 (Nat.le_antisymm hdiv ((Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.mul_comm]; omega))))]

end VG.Proof.RsaPss.Arm
