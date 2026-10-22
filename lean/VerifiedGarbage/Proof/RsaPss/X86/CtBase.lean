module

public import VerifiedGarbage.Proof.RsaPss.X86.Prims
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.RsaPss.CtPad
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing a message of secret length, the setting

The hash function's sizes (`PssHash.B`, …); ranges of our part of
`scratch` as buffers (`Geo.wbuf`); the masks of the borrow of a subtraction
(`isZero`, `zmask`); `psrun`, which runs a block of the body symbolically
(ML-DSA's `xrun`, with the memory operands `⟨b, d⟩`); and the bytes of `Y`
after the padding loop (`padY`), which are the padded message over its
blocks (`padY_eq`), as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

namespace PssHash

variable (h : PssHash)

abbrev B : Nat := h.H.B
abbrev D : Nat := h.H.D
abbrev N : Nat := h.H.N
abbrev L : Nat := h.H.L
abbrev md : Md h.B h.N h.L := h.ok.md

theorem B_cases : h.B = 64 ∨ h.B = 128 := h.ok.sizes.B
theorem N_le : h.N ≤ 64 := h.ok.sizes.N.2.1
theorem N4 : h.N % 4 = 0 := h.ok.sizes.N.2.2
theorem D_le : h.D ≤ h.N := h.ok.sizes.D.2.1
theorem D_pos : 0 < h.D := h.ok.sizes.D.1
theorem DL : h.D + h.L + 4 ≤ h.B := h.ok.sizes.DL
theorem so_le : h.H.so ≤ 512 := by have := h.ok.sizes.so; have := h.ok.sizes.W; omega
theorem B_le : h.B ≤ 128 := by rcases h.B_cases with e | e <;> omega
theorem B_ge : 64 ≤ h.B := by rcases h.B_cases with e | e <;> omega
theorem S_eq : h.H.S = h.N + h.B := h.ok.sizes.S
theorem L_le : h.L ≤ 16 := h.L16
theorem NL : h.N + h.L ≤ h.B := h.NLB

theorem lg : lgB h.H = 6 ∧ h.B = 64 ∨ lgB h.H = 7 ∧ h.B = 128 := by
  unfold lgB
  rcases h.B_cases with e | e
  · exact .inl ⟨by show Nat.log2 h.B = 6; rw [e]; decide, e⟩
  · exact .inr ⟨by show Nat.log2 h.B = 7; rw [e]; decide, e⟩

theorem pow_lg : 2 ^ lgB h.H = h.B := by rcases h.lg with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] <;> rfl

theorem lg_range : 1 ≤ lgB h.H ∧ lgB h.H ≤ 31 := by rcases h.lg with ⟨a, _⟩ | ⟨a, _⟩ <;> rw [a] <;> decide

end PssHash

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers. -/
macro "pomega" : tactic => `(tactic| (have _ : VG.Impl.RsaPss.X86.oCW = 0 := rfl; have _ : VG.Impl.RsaPss.X86.oSt = 512 := rfl; have _ : VG.Impl.RsaPss.X86.oSel = 768 := rfl; have _ : VG.Impl.RsaPss.X86.oDig = 832 := rfl; have _ : VG.Impl.RsaPss.X86.oLen = 896 := rfl; have _ : VG.Impl.RsaPss.X86.oEm = 1024 := rfl; have _ : VG.Impl.RsaPss.X86.oY = 2048 := rfl; have _ : VG.Impl.RsaPss.X86.oRsa = 8192 := rfl; have _ : VG.Impl.RsaPss.X86.frameBytes = 144 := rfl; omega))

/-! ## Masks -/

/-- The mask `sub r, 1; sbb r, r` leaves: all ones if `x` is zero. -/
def zmask (x : BitVec 32) : BitVec 32 := if x = 0 then BitVec.allOnes 32 else 0

theorem sbb_zero (x : BitVec 32) :
    x - 1 - (x - 1) - (BitVec.ofBool (decide (x.toNat < (1 : BitVec 32).toNat))).setWidth 32 = zmask x := by
  rw [sbb_self, zmask]
  by_cases h : x = 0
  · subst h; simp
  · have h1 : decide (x.toNat < (1 : BitVec 32).toNat) = false := by
      have e : (1 : BitVec 32).toNat = 1 := rfl
      rw [e, decide_eq_false_iff_not]
      intro h'; exact h (BitVec.eq_of_toNat_eq (by show x.toNat = 0; omega))
    simp only [h1, h, Bool.false_eq_true, ↓reduceIte]

theorem zmask_xor {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    zmask (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b) = if a = b then BitVec.allOnes 32 else 0 := by
  unfold zmask
  by_cases h : a = b
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right fun e => h (by
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)]

/-! ## Running blocks -/

/-- Runs a block of the body symbolically (`xrun`), with its memory operands
`⟨b, d⟩` at `addr (s.gpr b) d`. -/
syntax "psrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| psrun) => `(tactic| psrun [])
  | `(tactic| psrun [$ls,*]) => `(tactic| xrun [ea_mk, Impl.RsaPkcs1Sig.X86.stk, Impl.RsaPkcs1Sig.X86.at_,
      sbb_zero, $ls,*])

variable {L : Lay} {scr : BitVec 32}

namespace Geo

variable (hg : Geo L scr)
include hg

/-- A range of our part of `scratch`, as a buffer the body writes. -/
theorem wbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : WBuf L (scr + BitVec.ofNat 32 o) n := by
  obtain ⟨k, hk, hR⟩ := hg.sub
  have fit := hg.fit
  unfold oRsa at h hk fit
  refine ⟨by rw [hg.scr_lt (by unfold oRsa; omega)]; omega, by omega, ⟨_, List.mem_cons_of_mem _ hR, ?_⟩⟩
  rw [hg.scrA (by unfold oRsa; omega)]
  exact Offset.contains_base _ (by omega) (by omega)

theorem rbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : RBuf L (scr + BitVec.ofNat 32 o) n := (hg.wbuf h hn).rbuf

theorem byteAt_scr {o i : Nat} (h : o + i < oRsa) : byteAt (scr + BitVec.ofNat 32 o) i = sa scr (o + i) := by
  rw [byteAt, hg.scrA (by omega), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A slot's address. -/
theorem aFr {σ : State} (ok : L.Ok σ) : ∀ d, d + 4 ≤ frameBytes → VG.X86.addr L.B d = L.fr d :=
  fun d hd => ok.addrB (by rw [hg.F]; simp only [Lay.A]; omega)

/-- An argument's address. -/
theorem aArg {σ : State} (ok : L.Ok σ) : ∀ j, j < L.argv.length →
    VG.X86.addr L.B (Impl.RsaPkcs1Sig.X86.argOff frameBytes j) = L.argA j :=
  fun j hj => by
    rw [Lay.argA, hg.F]
    exact ok.addrB (by rw [hg.F]; simp only [Lay.A, Impl.RsaPkcs1Sig.X86.argOff]; omega)

end Geo

theorem Ctx.rFr {σ s : State} (hg : Geo L scr) (h : Ctx L scr σ s) :
    ∀ d, d + 4 ≤ frameBytes → InRegions (s.rd ++ s.wr) (L.fr d) 4 :=
  fun d hd => h.st.inFrR (by rw [hg.F]; exact hd)

theorem Ctx.wFr {σ s : State} (hg : Geo L scr) (h : Ctx L scr σ s) :
    ∀ d, d + 4 ≤ frameBytes → InRegions s.wr (L.fr d) 4 :=
  fun d hd => h.st.inFr (by rw [hg.F]; exact hd)

theorem slot_frame (L : Lay) (m : Mem) (d : Nat) (v : BitVec 32) : Frame [slotR L d] m (m.writeW (L.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

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

end VG.Proof.RsaPss.X86
