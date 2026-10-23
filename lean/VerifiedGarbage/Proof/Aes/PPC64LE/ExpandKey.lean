module

public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Proof.Aes.KeyExp
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.PPC64LE.Keys
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Keys

/-!
# The AES key expansion on PPC64LE

As on x86-64 (`Proof/Aes/X86_64/ExpandKey.lean`): `subAll` (`toBs`, the
S-box, `fromBs`) applies the S-box to every byte of the eight words
(`subAll_wp`, from the bitsliced layers' lemmas); each word of the schedule
is then a few scalar instructions around it (`word_ok`), and the loop over
the words keeps the schedule's bytes so far equal to the specification's
(`WInv`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_expand_key_scratch(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32. The
pointers and `key_len` are public; the key is secret. -/
def expandKeyPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sched : Region := ⟨s.gpr .r5, 240⟩
    let scratch : Region := ⟨s.gpr .r6, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .r4).toNat = 16 ∨ (s.gpr .r4).toNat = 24 ∨ (s.gpr .r4).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .r5) (16 * (Spec.Aes.rounds ((s.gpr .r4).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)

/-! ## The S-box on every byte -/

/-- The four states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 64) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (b + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_stOf (Q : Nat → BitVec 64) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem subAll_wp {s : State} (hok : Ok linCfg s) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, ∀ t < 8, (Q s' k).extractLsb' (8 * t) 8 = sbox ((Q s k).extractLsb' (8 * t) 8)) →
      s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) →
      Frame [⟨s.gpr sb, 8 * 40⟩] s.mem s'.mem → P s') :
    WP isa (.block subAll) s P := by
  simp only [subAll]
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁, hs₁, h₁, rd₁, wr₁, o₁, f₁⟩ := toBs_ok hok
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ sb (by decide)
  have ok₁ : Ok linCfg s₁ := hok.congr hb₁ hb₁ rd₁ wr₁
  obtain ⟨s₂, hs₂, h₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (s := s₁) ok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hb₂ : s₂.gpr sb = s.gpr sb := (o₂ sb (by decide)).trans hb₁
  have ok₂ : Ok linCfg s₂ := hok.congr hb₂ hb₂ (rd₂.trans rd₁) (wr₂.trans wr₁)
  obtain ⟨s₃, hs₃, h₃, rd₃, wr₃, o₃, f₃⟩ := fromBs_ok ok₂
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hin := in_of_bs h₃ (bs_subBytes h₂ (bs_of_in h₁ (inRel_stOf (Q s))))
  refine h s₃ (fun k hk t ht => ?_) (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁))
    (fun r hr => (o₃ r hr).trans ((o₂ r hr).trans (o₁ r hr))) ?_
  · refine byte_ext fun j hj => ?_
    have := hin (k % 4) (by omega) (t + 8 * (k / 4)) (by omega) j hj
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show 8 * ((t + 8 * (k / 4)) % 8) + j = 8 * t + j by omega] at this
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, this, getD_eq _ (by omega)]
    simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show (t + 8 * (k / 4)) % 8 = t by omega]
  · have e₁ : slotRegion linCfg s = ⟨s.gpr sb, 8 * 40⟩ := rfl
    have e₂ : slotRegion sboxCfg s₁ = ⟨s.gpr sb, 8 * 40⟩ := by
      simp only [slotRegion, sboxCfg, hb₁]
    have e₃ : slotRegion linCfg s₂ = ⟨s.gpr sb, 8 * 40⟩ := by
      simp only [slotRegion, linCfg, hb₂]
    rw [e₁] at f₁; rw [e₂] at f₂; rw [e₃] at f₃
    exact (f₁.trans f₂).trans f₃

/-! ## Bytes -/

/-- The round constant after one more round. -/
def rcNext (v : BitVec 64) : BitVec 64 :=
  ((v + v) ^^^ ((BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofNat 64 0x1b)) &&& BitVec.ofNat 64 0xff

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 64 := (Nat.repeat xtimes k (1 : Byte)).setWidth 64

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp

theorem xor32_byte (x : BitVec 64) (y : BitVec 32) {t : Nat} (ht : t < 4) :
    ((x ^^^ y.setWidth 64).setWidth 32).extractLsb' (8 * t) 8 =
      x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega]
  intro; omega

theorem rot_byte (x c : BitVec 64) {t : Nat} (ht : t < 4) :
    ((((x.setWidth 32).rotateRight 8).setWidth 64) ^^^ c).extractLsb' (8 * t) 8 =
      x.extractLsb' (8 * ((t + 1) % 4)) 8 ^^^ c.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain ⟨Ta, Tb, Tc, Td, Te⟩ := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
    (show (List.range 4).all (fun t => (List.range 8).all fun j => decide (8 * t + j < 64 ∧ 8 * t + j < 32 ∧
      8 * ((t + 1) % 4) + j < 32 ∧ (8 * t + j < 32 - 8 % 32 → 8 % 32 + (8 * t + j) = 8 * ((t + 1) % 4) + j) ∧
      (¬ 8 * t + j < 32 - 8 % 32 → 8 * t + j - (32 - 8 % 32) = 8 * ((t + 1) % 4) + j))) = true by
      decide +kernel) t (List.mem_range.mpr ht)) j (List.mem_range.mpr hj))
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight]
  simp only [hj, decide_true, Bool.true_and, Ta]
  by_cases h : 8 * t + j < 32 - 8 % 32
  · rw [ite_eq_left h,
      Td h]
    simp [Tc]
  · rw [ite_eq_right h,
      Te h]
    simp [Tc]
    intro; omega

theorem ld_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 4) :
    ((m.readW a 32).setWidth 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [Mem.readW_byte m a ht]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega]
  intro; omega

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega

/-! ## One word -/

/-- The slot of the round constant. -/
abbrev rcAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * 61)

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `B`, and the key `kl` of `nk` words. -/
structure WSetup (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

/-- Before word `i`. -/
structure WInv (s₀ : State) (S B : Addr) (kl : List Byte) (nk i : Nat) (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  r11 : s.gpr .r11 = S + BitVec.ofNat 64 (4 * (i - 1))
  r10 : s.gpr .r10 = S + BitVec.ofNat 64 (4 * (i - nk))
  r12 : s.gpr .r12 = BitVec.ofNat 64 (4 * (i % nk))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (4 * nk)
  r4 : s.gpr .r4 = BitVec.ofNat 64 (4 * (nk + 7) - i)
  r8 : s.gpr .r8 = B
  r2 : s.gpr .r2 = s₀.gpr .r2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 4 * i, s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  rc : s.mem.readW (rcAddr B) 64 = rcW ((i - 1) / nk)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the last word. -/
structure WDone (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = B
  r2 : s.gpr .r2 = s₀.gpr .r2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 16 * (nk + 7), s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- `temp` computed (in the low 32 bits of `q 0`), from `s`. -/
structure Mid (B : Addr) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr (q 0)).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨B, 8 * 40⟩, ⟨rcAddr B, 8⟩] s.mem s'.mem
  rc : s'.mem.readW (rcAddr B) 64 = rcW (i / nk)

theorem slot_disj (B : Addr) : Region.Disjoint ⟨rcAddr B, 8⟩ ⟨B, 8 * 40⟩ :=
  Offset.disjoint_base B (by decide) (by decide)

theorem rotTail_wp {s : State} {B : Addr} (hb : s.gpr sb = B) (hw : (⟨B, 512⟩ : Region) ∈ s.wr)
    {P : State → Prop}
    (h : ∀ s', s'.gpr (q 0) = (((s.gpr (q 0)).setWidth 32).rotateRight 8).setWidth 64 ^^^
        s.mem.readW (rcAddr B) 64 →
      s'.mem = s.mem.writeW (rcAddr B) (rcNext (s.mem.readW (rcAddr B) 64)) →
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block rotTail) s P := by
  have hw' : (⟨B, 512⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hw
  unfold rotTail
  simp only [ldS, stS, rconSlot]
  refine wp_rotr_w (by decide) fun s₁ u₁ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [u₁.other _ (by decide), hb])
    (by rw [u₁.rd, u₁.wr]; exact in_off hw' (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_sub fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => wp_and fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => ?_
  refine wp_and fun s₁₂ u₁₂ => ?_
  have hb₁₂ : s₁₂.gpr sb = B := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb]
  refine wp_std (by decide) ⟨by decide, by decide⟩ (by rw [hb₁₂])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact in_off hw (by omega) (by omega)) fun s₁₃ u₁₃ => wp_nil ?_
  -- The round constant and its successor.
  have hne : q 0 ≠ q 1 ∧ q 0 ≠ q 2 ∧ q 0 ≠ q 3 ∧ q 1 ≠ q 2 ∧ q 1 ≠ q 3 ∧ q 2 ≠ q 3 ∧ q 1 ≠ t0 ∧
      q 2 ≠ t0 ∧ q 3 ≠ t0 ∧ q 0 ≠ t0 := by decide
  obtain ⟨n01, n02, n03, n12, n13, n23, n1t, n2t, n3t, n0t⟩ := hne
  let v := s.mem.readW (rcAddr B) 64
  have rc₂ : s₂.gpr (q 1) = v := by rw [u₂.gpr, u₁.mem]
  have q2₄ : s₄.gpr (q 2) = v >>> 7 := by rw [u₄.gpr, u₃.other _ (Ne.symm n01), rc₂]
  have q3₆ : s₆.gpr (q 3) = BitVec.ofNat 64 0 - (v >>> 7) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ n23, q2₄]
  have q3₈ : s₈.gpr (q 3) = (BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofNat 64 0x1b := by
    rw [u₈.gpr, u₇.other _ n3t, q3₆, u₇.gpr]
  have q1₈ : s₈.gpr (q 1) = v := by
    rw [u₈.other _ n13, u₇.other _ n1t, u₆.other _ n13, u₅.other _ n13, u₄.other _ n12,
      u₃.other _ (Ne.symm n01), rc₂]
  have q1₁₀ : s₁₀.gpr (q 1) = (v + v) ^^^ ((BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofNat 64 0x1b) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other _ (Ne.symm n13), q1₈, q3₈]
  have q1₁₂ : s₁₂.gpr (q 1) = rcNext v := by
    rw [u₁₂.gpr, u₁₁.other _ n1t, u₁₁.gpr, q1₁₀]; rfl
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem]
  refine h s₁₃ ?_ ?_ (fun r hr => ?_) ?_ ?_
  · rw [u₁₃.gpr, u₁₂.other _ n01, u₁₁.other _ n0t, u₁₀.other _ n01, u₉.other _ n01, u₈.other _ n03,
      u₇.other _ n0t, u₆.other _ n03, u₅.other _ n03, u₄.other _ n02, u₃.gpr,
      u₂.other _ n01, u₁.gpr, rc₂]
  · rw [u₁₃.mem, m₁₂, q1₁₂]
  · have hq : r ≠ q 0 ∧ r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 ∧ r ≠ t0 := by
      revert hr; cases r <;> decide
    obtain ⟨a0, a1, a2, a3, a4⟩ := hq
    rw [u₁₃.gpr, u₁₂.other _ a1, u₁₁.other _ a4, u₁₀.other _ a1, u₉.other _ a1, u₈.other _ a3,
      u₇.other _ a4, u₆.other _ a3, u₅.other _ a3, u₄.other _ a2, u₃.other _ a0, u₂.other _ a1,
      u₁.other _ a0]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
      u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr,
      u₁.wr]

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`, and the next round constant. -/
theorem rot_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) {s₁ : State}
    (hw : ∀ t < 4, (s₁.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0)
    (hok : Ok linCfg s₁) (hb₁ : s₁.gpr sb = B) (hwS : (⟨B, 512⟩ : Region) ∈ s₁.wr)
    (o₁ : ∀ r, r ≠ q 0 → s₁.gpr r = s.gpr r) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) (h0 : i % nk = 0) :
    WP isa (.block rotWordStep) s₁ (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hi1 := hi.hi
  have hn := hi.hn
  have hlen := kw_length hs.len (by omega) (i - 1)
  simp only [rotWordStep]
  rw [WP.block_append_iff (M := isa)]
  refine subAll_wp hok fun s₂ h₂ rd₂ wr₂ o₂ f₂ => ?_
  have hb₂ : s₂.gpr sb = B := (o₂ sb (by decide)).trans hb₁
  refine rotTail_wp hb₂ (by rw [wr₂]; exact hwS) fun s₃ q₃ m₃ o₃ rd₃ wr₃ => ?_
  rw [hb₁] at f₂
  have rc₂ : s₂.mem.readW (rcAddr B) 64 = rcW ((i - 1) / nk) := by
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), m₁, hi.rc]
  refine ⟨fun t ht => ?_, fun r hr => ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_, ?_⟩
  · rw [q₃, rot_byte _ _ ht, show s₂.gpr (q 0) = Q s₂ 0 from rfl, h₂ 0 (by omega) _ (by omega),
      show Q s₁ 0 = s₁.gpr (q 0) from rfl, hw _ (by omega), rc₂, rcW_byte _ ht]
    simp only [kTemp, h0, ite_true]
    rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
      subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
      ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
  · rw [o₃ r hr, o₂ r hr, o₁ r (fun e => hr (e ▸ by decide))]
  · rw [m₃, ← m₁]
    refine Frame.writeW (r := ⟨rcAddr B, 8⟩) ?_ (by simp) _ (Region.contains_self _ _)
    exact f₂.mono (by simp)
  · rw [m₃, Mem.readW_writeW_self64, rc₂, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]

theorem temp_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) {s₁ : State}
    (q0₁ : s₁.gpr (q 0) = (s.mem.readW (S + BitVec.ofNat 64 (4 * (i - 1))) 32).setWidth 64)
    (o₁ : ∀ r, r ≠ q 0 → s₁.gpr r = s.gpr r)
    (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) :
    WP isa (.ite (.zero .d .r12) (.block rotWordStep)
        (.seq (.block [.subi t0 .r12 16])
          (.ite (.zero .d t0) (.seq (.block [.subi t0 .r7 32]) (.ite (.zero .d t0) (.block subAll) (.block [])))
            (.block [])))) s₁ (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have hwS : (⟨B, 512⟩ : Region) ∈ s₁.wr := by rw [wr₁, hi.wr]; exact hs.scr
  have hb₁ : s₁.gpr sb = B := by rw [show sb = .r8 from rfl, o₁ .r8 (by decide), hi.r8]
  -- The bytes of `w[i − 1]`.
  have hw : ∀ t < 4, (s₁.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0 := by
    intro t ht
    rw [q0₁, ld_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, hi.sched _ (by omega),
      show (4 * (i - 1) + t) / 4 = i - 1 by omega, show (4 * (i - 1) + t) % 4 = t by omega]
  have hlen := kw_length hs.len hnk (i - 1)
  have hok : Ok linCfg s₁ := Ok.of_region hwS hb₁.symm (by simp only [linCfg]; omega)
    (by show 512 < 2 ^ 64; decide) rfl
  have mid_of : ∀ s', s'.gpr (q 0) = s₁.gpr (q 0) → (∀ r, r ∉ sboxWrites → s'.gpr r = s₁.gpr r) →
      s'.mem = s.mem → s'.rd = s₁.rd → s'.wr = s₁.wr → i % nk ≠ 0 →
      kTemp nk i (kw kl nk (i - 1)) = kw kl nk (i - 1) → Mid B kl nk i s s' := by
    intro s' hq hk hm hrd hwr hne ht
    refine ⟨fun t htt => by rw [hq, hw t htt, ht], fun r hr => (hk r hr).trans (o₁ r ?_),
      hrd.trans rd₁, hwr.trans wr₁, by rw [hm]; exact Frame.refl _ _, ?_⟩
    · intro h; subst h; exact hr (by decide)
    · rw [hm, hi.rc, div_pred_ne h3 hne]
  have r12₁ : s₁.gpr .r12 = BitVec.ofNat 64 (4 * (i % nk)) := by rw [o₁ _ (by decide), hi.r12]
  refine WP.ite (decide (4 * (i % nk) = 0)) (eval_zero_ofNat _ _ (by omega) r12₁)
    (fun hb => ?_) (fun hb => ?_)
  · exact rot_wp hs hi hw hok hb₁ hwS o₁ m₁ rd₁ wr₁ (by simp at hb; omega)
  · have h0 : i % nk ≠ 0 := by simp at hb; omega
    refine WP.seq (wp_subi (by decide) (by decide) fun s₄ u₄ => wp_nil ?_)
    have t₄ : isa.eval (.zero .d t0) s₄ = some (decide (4 * (i % nk) = 16)) := by
      rw [eval_zero, u₄.gpr, r12₁, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    refine WP.ite (decide (4 * (i % nk) = 16)) t₄ (fun hb₄ => ?_) (fun hb₄ => ?_)
    · have h4 : 4 * (i % nk) = 16 := by simpa using hb₄
      refine WP.seq (wp_subi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_)
      have t₅ : isa.eval (.zero .d t0) s₅ = some (decide (4 * nk = 32)) := by
        rw [eval_zero, u₅.gpr, u₄.other _ (by decide), o₁ _ (by decide), hi.r7,
          Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
      have g₅ : ∀ r, r ≠ t0 → s₅.gpr r = s₁.gpr r := fun r h => by
        rw [u₅.other _ h, u₄.other _ h]
      refine WP.ite (decide (4 * nk = 32)) t₅ (fun hb₅ => ?_) (fun hb₅ => ?_)
      · -- `SUBWORD(temp)`.
        have h8 : nk = 8 := by simp at hb₅; omega
        have ok₅ : Ok linCfg s₅ := hok.congr (g₅ _ (by decide)) (g₅ _ (by decide))
          (u₅.rd.trans u₄.rd) (u₅.wr.trans u₄.wr)
        refine subAll_wp ok₅ fun s₆ h₆ rd₆ wr₆ o₆ f₆ => ?_
        rw [g₅ _ (by decide), hb₁, u₅.mem, u₄.mem, m₁] at f₆
        refine ⟨fun t ht => ?_, fun r hr => ?_, by rw [rd₆, u₅.rd, u₄.rd, rd₁],
          by rw [wr₆, u₅.wr, u₄.wr, wr₁], f₆.mono (by simp), ?_⟩
        · rw [show s₆.gpr (q 0) = Q s₆ 0 from rfl, h₆ 0 (by omega) _ (by omega),
            show Q s₅ 0 = s₁.gpr (q 0) by simp only [Q]; rw [g₅ _ (by decide)], hw _ ht]
          rw [kTemp, ite_eq_right h0, ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega),
            subWord_getD (by rw [hlen]; exact ht)]
        · rw [o₆ r hr, g₅ _ (fun h => by subst h; exact hr (by decide)),
            o₁ r (fun h => by subst h; exact hr (by decide))]
        · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), hi.rc,
            div_pred_ne h3 h0]
      · have h8 : nk ≠ 8 := by simp at hb₅; omega
        refine WP.block_nil (mid_of s₅ (g₅ _ (by decide))
          (fun r hr => g₅ r (fun h => by subst h; exact hr (by decide)))
          (by rw [u₅.mem, u₄.mem, m₁]) (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]) h0 ?_)
        rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]
    · have h4 : 4 * (i % nk) ≠ 16 := by simpa using hb₄
      refine WP.block_nil (mid_of s₄ (u₄.other _ (by decide))
        (fun r hr => u₄.other r (fun h => by subst h; exact hr (by decide))) (by rw [u₄.mem, m₁])
        u₄.rd u₄.wr h0 ?_)
      rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- `Saved`, after writes that miss slots 40–57. -/
theorem saved_frame' {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 144⟩ r) :
    Saved s₀ b m' := saved_frame h hf hd

/-- The memory after word `i` is stored. -/
def storeMem (s₂ : State) (S : Addr) (nk i : Nat) : Mem :=
  s₂.mem.writeW (S + BitVec.ofNat 64 (4 * i))
    ((s₂.gpr (q 0) ^^^ (s₂.mem.readW (S + BitVec.ofNat 64 (4 * (i - nk))) 32).setWidth 64).setWidth 32)

theorem store_facts {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s s₂ : State} (hi : WInv s₀ S B kl nk i s) (hm : Mid B kl nk i s s₂) :
    (∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0) ∧
    Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) ∧ Saved s₀ B (storeMem s₂ S nk i) ∧
    (storeMem s₂ S nk i).readW (rcAddr B) 64 = rcW (i / nk) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have fS : ∀ k < 240, s₂.mem (S + BitVec.ofNat 64 k) = s.mem (S + BitVec.ofNat 64 k) := fun k hk =>
    hm.frame.bytes (R := ⟨S, 240⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.sep.sub_right (Region.sub_prefix (by decide))
      · exact hs.sep.sub_right (Offset.sub_base B (by decide))) (by simp) hk
  have sched' : ∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0 := by
    intro k hk
    unfold storeMem
    by_cases hki : k < 4 * i
    · rw [writeW32_other _ (Offset.disjoint S (Or.inl (by omega)) (by omega) (by omega)), fS k (by omega),
        hi.sched k hki]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * i + t := ⟨k - 4 * i, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, xor32_byte _ _ ht, hm.temp t ht,
        ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, fS _ (by omega),
        hi.sched _ (by omega), show (4 * (i - nk) + t) / 4 = i - nk by omega,
        show (4 * (i - nk) + t) % 4 = t by omega, show (4 * i + t) / 4 = i by omega,
        show (4 * i + t) % 4 = t by omega, kw_step kl hnk hi1,
        xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) := by
    unfold storeMem
    refine Frame.writeW (hi.frame.trans (hm.frame.sub fun r hr => ?_)) (r := ⟨S, 240⟩) (by simp) _
      (c_off S (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 512⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨B, 512⟩, by simp, Offset.sub_base B (by decide)⟩
  have hdS : ∀ r ∈ [(⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region)],
      Region.Disjoint ⟨B + BitVec.ofNat 64 320, 144⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 320, 144⟩ :=
      hs.sep.sub_right (Offset.sub_base B (d := 320) (n := 144) (k := 512) (by decide))
    have d2 : Region.Disjoint ⟨S + BitVec.ofNat 64 (4 * i), 4⟩ ⟨B + BitVec.ofNat 64 320, 144⟩ :=
      d1.sub_left (Offset.sub_base S (d := 4 * i) (n := 4) (k := 240) (by omega))
    exact d2.symm
  have sv : Saved s₀ B (storeMem s₂ S nk i) := by
    unfold storeMem
    refine saved_frame (saved_frame hi.saved hm.frame fun r hr => ?_)
      (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (4 * i), 4⟩] _) (by simp) _
        (Region.contains_self _ _)) hdS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base B (by decide) (by decide)
    · exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide)
  have rc : (storeMem s₂ S nk i).readW (rcAddr B) 64 = rcW (i / nk) := by
    rw [storeMem, Mem.readW_writeW_sep ((hs.sep.sub_right (Offset.sub_base B (by decide))).symm.sep
      (Region.contains_self _ _) (c_off S (by omega) (by omega))) (by decide), hm.rc]
  exact ⟨sched', fr, sv, rc⟩

theorem ofNat_sub_one {j : Nat} (h : 0 < j) :
    BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem add4 (S : Addr) (x : Nat) :
    S + BitVec.ofNat 64 x + BitVec.ofNat 64 4 = S + BitVec.ofNat 64 (x + 4) := Offset.add_add S x 4

theorem word_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) :
    WP isa wordBody s fun s' =>
      (isa.eval (.nonzero .d .r4) s' = some true ∧ WInv s₀ S B kl nk (i + 1) s') ∨
      (isa.eval (.nonzero .d .r4) s' = some false ∧ WDone s₀ S B kl nk s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  unfold wordBody
  refine WP.seq ?_
  have hrS : (⟨S, 240⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ (by rw [hi.wr]; exact hs.sch)
  refine wp_lwz (by decide) (by decide) (by rw [hi.r11, BitVec.add_zero])
    (in_off hrS (by omega) (by omega)) fun s₁ u₁ => wp_nil ?_
  refine WP.seq (WP.mono (temp_wp hs hi u₁.gpr u₁.other u₁.mem u₁.rd u₁.wr) fun s₂ hm => ?_)
  have k₂ : ∀ r ∈ [Reg.r2, .r4, .r7, .r8, .r10, .r11, .r12], s₂.gpr r = s.gpr r := fun r hr =>
    hm.keep r (by revert hr; revert r; decide)
  have r11₂ := (k₂ .r11 (by simp)).trans hi.r11
  have r10₂ := (k₂ .r10 (by simp)).trans hi.r10
  have r12₂ := (k₂ .r12 (by simp)).trans hi.r12
  have r7₂ := (k₂ .r7 (by simp)).trans hi.r7
  have hwS : (⟨S, 240⟩ : Region) ∈ s₂.wr := by rw [hm.wr, hi.wr]; exact hs.sch
  -- `w[i] := w[i − Nk] ⊕ temp`.
  refine WP.seq ?_
  refine wp_lwz (by decide) (by decide) (by rw [r10₂, BitVec.add_zero])
    (in_off (List.mem_append_right _ hwS) (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  have r11₄ : s₄.gpr .r11 = S + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), r11₂]
  refine wp_stw (a := S + BitVec.ofNat 64 (4 * i)) (by decide) (by decide)
    (by rw [r11₄, add4, show 4 * (i - 1) + 4 = 4 * i by omega])
    (by rw [u₄.wr, u₃.wr]; exact in_off hwS (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_addi (by decide) (by decide) fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ => ?_
  refine wp_addi (by decide) (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_nil ?_
  have mem₉ : s₉.mem = storeMem s₂ S nk i := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr,
      u₃.other _ (by decide), storeMem]
  have r12₈ : s₈.gpr .r12 = BitVec.ofNat 64 (4 * (i % nk) + 4) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), r12₂]
    exact (BitVec.ofNat_add _ _).symm
  have t₉ : s₉.gpr t0 = BitVec.ofNat 64 (4 * (i % nk) + 4) - BitVec.ofNat 64 (4 * nk) := by
    rw [u₉.gpr, r12₈, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), r7₂]
  have g₉ : ∀ r ∈ [Reg.r2, .r4, .r7, .r8], s₉.gpr r = s.gpr r := fun r hr => by
    rw [u₉.other r (by revert hr; revert r; decide), u₈.other r (by revert hr; revert r; decide),
      u₇.other r (by revert hr; revert r; decide), u₆.other r (by revert hr; revert r; decide), u₅.gpr,
      u₄.other r (by revert hr; revert r; decide), u₃.other r (by revert hr; revert r; decide),
      k₂ r (by revert hr; revert r; decide)]
  have r11₉ : s₉.gpr .r11 = S + BitVec.ofNat 64 (4 * (i + 1 - 1)) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      r11₄, add4, show 4 * (i - 1) + 4 = 4 * (i + 1 - 1) by omega]
  have r10₉ : s₉.gpr .r10 = S + BitVec.ofNat 64 (4 * (i + 1 - nk)) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), r10₂, add4,
      show 4 * (i - nk) + 4 = 4 * (i + 1 - nk) by omega]
  -- `r12 := 4 ((i + 1) mod Nk)`.
  refine WP.seq (WP.mono (Q := fun (s₁₀ : State) =>
      s₁₀.gpr .r12 = BitVec.ofNat 64 (4 * ((i + 1) % nk)) ∧
      (∀ r, r ≠ .r12 → s₁₀.gpr r = s₉.gpr r) ∧ s₁₀.mem = s₉.mem ∧ s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr) ?_
    fun s₁₀ ⟨r12₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ => ?_)
  · have e₉ : isa.eval (.zero .d t0) s₉ = some (decide (4 * (i % nk) + 4 = 4 * nk)) := by
      rw [eval_zero, t₉, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    refine WP.ite (decide (4 * (i % nk) + 4 = 4 * nk)) e₉ (fun hb => ?_) (fun hb => ?_)
    · refine wp_li (by decide) fun s' u' => wp_nil ⟨?_, u'.other, u'.mem, u'.rd, u'.wr⟩
      have h1 : (i + 1) % nk = 0 := by
        have : i % nk + 1 = nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), this, Nat.mod_self]
      rw [u'.gpr, h1]
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      have h1 : (i + 1) % nk = i % nk + 1 := by
        have : i % nk + 1 < nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), Nat.mod_eq_of_lt this]
      rw [u₉.other _ (by decide), r12₈, h1, Nat.mul_add, Nat.mul_one]
  -- `r4 := r4 − 1`.
  refine wp_subi (by decide) (by decide) fun s₁₁ u₁₁ => wp_nil ?_
  have r4₁₁ : s₁₁.gpr .r4 = BitVec.ofNat 64 (4 * (nk + 7) - i - 1) := by
    rw [u₁₁.gpr, o₁₀ _ (by decide), g₉ .r4 (by simp), hi.r4, ofNat_sub_one (by omega)]
  have ev := eval_nonzero_ofNat' s₁₁ .r4 (by omega) r4₁₁
  have gk : ∀ r ∈ [Reg.r2, .r7, .r8], s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [u₁₁.other r (by revert hr; revert r; decide), o₁₀ r (by revert hr; revert r; decide),
      g₉ r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
  have mem₁₁ : s₁₁.mem = storeMem s₂ S nk i := by rw [u₁₁.mem, m₁₀, mem₉]
  -- The scratch buffer's changes are outside the schedule.
  obtain ⟨sched', fr, sv, rc⟩ := store_facts hs hi hm
  rw [← mem₁₁] at sched' fr sv rc
  have r2₁₁ : s₁₁.gpr .r2 = s₀.gpr .r2 := (gk .r2 (by simp)).trans hi.r2
  have r8₁₁ : s₁₁.gpr .r8 = B := (gk .r8 (by simp)).trans hi.r8
  have rd : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, rd₁₀, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
    hm.rd, hi.rd]
  have wr : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, wr₁₀, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr,
    hm.wr, hi.wr]
  by_cases hl : 4 * (nk + 7) - i - 1 = 0
  · refine .inr ⟨by rw [ev, hl]; rfl, r8₁₁, r2₁₁, rd, wr, fun k hk => sched' k (by omega), sv, fr⟩
  · refine .inl ⟨by rw [ev]; simp [hl], ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, r8₁₁, r2₁₁, rd, wr,
      sched', by rw [Nat.add_sub_cancel]; exact rc, sv, fr⟩⟩
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), r11₉]
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), r10₉]
    · rw [u₁₁.other _ (by decide), r12₁₀]
    · rw [gk .r7 (by simp), hi.r7]
    · rw [r4₁₁, Nat.sub_sub]

/-! ## The loop over the words -/

theorem words_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk nk s) :
    WP isa (.loop wordBody (.nonzero .d .r4)) s (WDone s₀ S B kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₀ S B kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hi.hn; omega, i + 1, rfl, d⟩
  · exact .inl ⟨z, d⟩

/-! ## Copying the key -/

theorem st64_byte (m : Mem) (a : Addr) (v : BitVec 64) {t : Nat} (ht : t < 8) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show t < 2 ^ 64 by omega),
    show t < 64 / 8 by omega, ite_true, BitVec.setWidth_eq]

theorem ld64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [← Mem.extractLsb'_read m a (n := 8) ht]
  rfl

theorem writeW64_other {m : Mem} {a x : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 8⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- The key's bytes. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- During the copy, after `c` doublewords. -/
structure CInv (s₀ : State) (S B P : Addr) (K c : Nat) (s : State) : Prop where
  hc : 8 * c < K
  r3 : s.gpr .r3 = P + BitVec.ofNat 64 (8 * c)
  r5 : s.gpr .r5 = S + BitVec.ofNat 64 (8 * c)
  r4 : s.gpr .r4 = BitVec.ofNat 64 (K - 8 * c)
  r7 : s.gpr .r7 = BitVec.ofNat 64 K
  r8 : s.gpr .r8 = B
  r2 : s.gpr .r2 = s₀.gpr .r2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < 8 * c, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the copy. -/
structure CDone (s₀ : State) (S B P : Addr) (K : Nat) (s : State) : Prop where
  r5 : s.gpr .r5 = S + BitVec.ofNat 64 K
  r7 : s.gpr .r7 = BitVec.ofNat 64 K
  r8 : s.gpr .r8 = B
  r2 : s.gpr .r2 = s₀.gpr .r2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < K, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- The setting of the copy: the key (`K` bytes at `P`) is outside what is written. -/
structure CSetup (s₀ : State) (S B P : Addr) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨P, K⟩ : Region) ∈ s₀.rd
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  dS : Region.Disjoint ⟨P, K⟩ ⟨S, 240⟩
  dB : Region.Disjoint ⟨P, K⟩ ⟨B, 512⟩
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

theorem add8 (S : Addr) (c : Nat) :
    S + BitVec.ofNat 64 (8 * c) + BitVec.ofNat 64 8 = S + BitVec.ofNat 64 (8 * (c + 1)) := by
  rw [Offset.add_add, Nat.mul_succ]

theorem copy_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {c : Nat} {s : State}
    (hi : CInv s₀ S B P K c s) :
    WP isa (.block copyBody) s fun s' =>
      (isa.eval (.nonzero .d .r4) s' = some true ∧ CInv s₀ S B P K (c + 1) s') ∨
      (isa.eval (.nonzero .d .r4) s' = some false ∧ CDone s₀ S B P K s') := by
  have hK := hs.hK
  have hc := hi.hc
  have hc8 : 8 * c + 8 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega
  unfold copyBody
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hi.r3, BitVec.add_zero])
    (in_off (List.mem_append_left _ (by rw [hi.rd]; exact hs.key)) hc8 (by omega)) fun s₁ u₁ => ?_
  refine wp_std (by decide) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), hi.r5, BitVec.add_zero])
    (by rw [u₁.wr, hi.wr]; exact in_off hs.sch (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => ?_
  refine wp_subi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
  have m₅ : s₅.mem = s.mem.writeW (S + BitVec.ofNat 64 (8 * c))
      (s.mem.readW (P + BitVec.ofNat 64 (8 * c)) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  have r4₅ : s₅.gpr .r4 = BitVec.ofNat 64 (K - 8 * (c + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.r4,
      Offset.ofNat_sub_ofNat (show 8 ≤ K - 8 * c by omega), show K - 8 * c - 8 = K - 8 * (c + 1) by omega]
  have ev := eval_nonzero_ofNat' s₅ .r4 (by omega) r4₅
  have copied : ∀ k < 8 * (c + 1), s₅.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₅]
    by_cases hkc : k < 8 * c
    · rw [writeW64_other _ (Offset.disjoint S (Or.inl (by omega)) (by omega) (by omega)), hi.copied k hkc]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 8 ∧ k = 8 * c + t := ⟨k - 8 * c, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st64_byte _ _ _ ht, ld64_byte _ _ ht, BitVec.add_assoc,
        ← BitVec.ofNat_add]
      exact hi.frame.bytes (R := ⟨P, K⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.dS
        · exact hs.dB) (by simp only; omega) (show 8 * c + t < K by omega)
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s₅.mem := by
    rw [m₅]
    exact Frame.writeW hi.frame (r := ⟨S, 240⟩) (by simp) _ (c_off S (by omega) (by omega))
  have sv : Saved s₀ B s₅.mem := by
    rw [m₅]
    refine saved_frame hi.saved (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (8 * c), 8⟩] _) (by simp) _
      (Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 320, 144⟩ :=
      hs.sep.sub_right (Offset.sub_base B (d := 320) (n := 144) (k := 512) (by decide))
    exact (d1.sub_left (Offset.sub_base S (d := 8 * c) (n := 8) (k := 240) (by omega))).symm
  have g : ∀ r ∈ [Reg.r2, .r7, .r8], s₅.gpr r = s.gpr r := fun r hr => by
    rw [u₅.other r (by revert hr; revert r; decide), u₄.other r (by revert hr; revert r; decide),
      u₃.other r (by revert hr; revert r; decide), u₂.gpr, u₁.other r (by revert hr; revert r; decide)]
  have r5₅ : s₅.gpr .r5 = S + BitVec.ofNat 64 (8 * (c + 1)) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.r5,
      add8]
  have rd : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  by_cases hl : K - 8 * (c + 1) = 0
  · refine .inr ⟨by rw [ev]; simp [hl], ?_, by rw [g .r7 (by simp), hi.r7], by rw [g .r8 (by simp), hi.r8],
      by rw [g .r2 (by simp), hi.r2], rd, wr, fun k hk => copied k (by omega), sv, fr⟩
    rw [r5₅, show 8 * (c + 1) = K by omega]
  · refine .inl ⟨by rw [ev]; simp [hl], ⟨by omega, ?_, r5₅, r4₅, by rw [g .r7 (by simp), hi.r7],
      by rw [g .r8 (by simp), hi.r8], by rw [g .r2 (by simp), hi.r2], rd, wr, copied, sv, fr⟩⟩
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hi.r3,
      add8]

theorem copyLoop_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {s : State}
    (hi : CInv s₀ S B P K 0 s) :
    WP isa (.loop (.block copyBody) (.nonzero .d .r4)) s (CDone s₀ S B P K) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 8 * c ∧ CInv s₀ S B P K c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hc.hc; omega, c + 1, rfl, d⟩
  · exact .inl ⟨z, d⟩

/-! ## Setting up the word loop -/

theorem kw_getD_key (kl : List Byte) {nk k : Nat} (hk : k < 4 * nk) :
    (kw kl nk (k / 4)).getD (k % 4) 0 = kl.getD k 0 := by
  rw [kw_key kl (show k / 4 < nk by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp [show k % 4 < 4 by omega, Nat.div_add_mod]

theorem r4_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    (BitVec.ofNat 64 K >>> 2) + ((BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2)) +
      BitVec.ofNat 64 28 = BitVec.ofNat 64 (4 * (K / 4 + 7) - K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

theorem wordSetup_wp {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {s : State}
    (h : CDone s₀ S B P K s) :
    WP isa (.block wordSetup) s fun s' =>
      WInv s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) (K / 4) s' := by
  have hK := hs.hK
  have hK4 : K = 4 * (K / 4) := by omega
  unfold wordSetup
  simp only [stS, rconSlot]
  refine wp_sub fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_li (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  refine wp_add fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ => ?_
  refine wp_li (by decide) fun s₈ u₈ => ?_
  have hb₈ : s₈.gpr sb = B := by
    show s₈.gpr .r8 = B
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8]
  have wr₈ : s₈.wr = s₀.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  refine wp_std (by decide) ⟨by decide, by decide⟩ (by rw [hb₈])
    (by rw [wr₈]; exact in_off hs.scr (by omega) (by omega)) fun s₉ u₉ => wp_nil ?_
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hm : s₉.mem = s.mem.writeW (rcAddr B) (BitVec.ofNat 64 1) := by
    rw [u₉.mem, m₈, u₈.gpr]
  have r7 : s.gpr .r7 = BitVec.ofNat 64 K := h.r7
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  have d61 : Region.Disjoint ⟨S, 240⟩ ⟨rcAddr B, 8⟩ :=
    hs.sep.sub_right (Offset.sub_base B (by decide))
  refine ⟨Nat.le_refl _, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₉.wr, wr₈], ?_, ?_, ?_, ?_⟩
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.r5, Offset.add_ofNat_sub S (show 4 ≤ K by omega),
      show K - 4 = 4 * (K / 4 - 1) by omega]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h.r5, r7, Nat.sub_self, BitVec.add_sub_cancel]
    simp
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, Nat.mod_self]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), r7, ← hK4]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r7, r4_setup hK]
  · rw [u₉.gpr]; exact hb₈
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r2]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · intro k hk
    rw [hm, writeW64_other _ (d61.sub_left (Offset.sub_base S (by omega))),
      h.copied k (by omega), ← bytesAt_getD s₀.mem P (show k < K by omega),
      kw_getD_key _ (by omega)]
  · rw [hm, Mem.readW_writeW_self64, Nat.div_eq_of_lt (by omega)]
    rfl
  · rw [hm]
    refine saved_frame h.saved (Frame.writeW (Frame.refl [⟨rcAddr B, 8⟩] _)
      (by simp) _ (Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide)
  · rw [hm]
    exact Frame.writeW h.frame (r := ⟨B, 512⟩) (by simp) _ (c_off B (by omega) (by omega))

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K)
    (hS : s₀.gpr .r5 = S) (hB : s₀.gpr .r6 = B) (hP : s₀.gpr .r3 = P)
    (hKr : s₀.gpr .r4 = BitVec.ofNat 64 K) :
    WP isa (.block ([movR sb .r6] ++ saveRegs ++ [movR .r7 .r4])) s₀ (CInv s₀ S B P K 0) := by
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine wp_mr fun s₁ u₁ => wp_nil ?_
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (s := s₁) (b := B) (n := 512)
    (by rw [u₁.wr]; exact hs.scr) (by rw [u₁.gpr, hB])
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine wp_mr fun s₃ u₃ => wp_nil ?_
  have g : ∀ r, r ≠ .r7 → r ≠ .r8 → s₃.gpr r = s₀.gpr r := fun r h7 h8 => by
    rw [u₃.other r h7, g₂, u₁.other r h8]
  have hK := hs.hK
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr],
    fun k hk => by omega, ?_, ?_⟩
  · rw [g _ (by decide) (by decide), hP]; simp
  · rw [g _ (by decide) (by decide), hS]; simp
  · rw [g _ (by decide) (by decide), hKr]; simp
  · rw [u₃.gpr, g₂, u₁.other _ (by decide), hKr]
  · rw [u₃.other _ (by decide), g₂]; exact u₁.gpr.trans hB
  · rw [g _ (by decide) (by decide)]
  · intro i hi
    obtain ⟨-, -, n8⟩ := sreg_ne_args i hi
    rw [u₃.mem, sv₂ i hi, u₁.other _ n8]
  · rw [u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => ⟨⟨B, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyPPC64LE.pre s₀) :
    WP isa Impl.Aes.PPC64LE.expandKey s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Aes.expandKeyPPC64LE.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, hK⟩ := hp
  have hs : CSetup s₀ (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r3) (s₀.gpr .r4).toNat :=
    ⟨hK, by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, dKS, dKB, dSB⟩
  generalize hS : s₀.gpr .r5 = S at hs dSB
  generalize hB : s₀.gpr .r6 = B at hs dSB
  generalize hP : s₀.gpr .r3 = P at hs dKS dKB
  generalize hK' : (s₀.gpr .r4).toNat = K at hs hK dKS dKB
  have hKr : s₀.gpr .r4 = BitVec.ofNat 64 K := by rw [← hK']; simp
  have hK4 : K = 4 * (K / 4) := by omega
  unfold Impl.Aes.PPC64LE.expandKey
  refine WP.seq (WP.mono (prologue_wp hs hS hB hP hKr) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hs h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (wordSetup_wp hs h₂) fun s₃ wi => ?_)
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  have ws : WSetup s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) :=
    ⟨by omega, by rw [hlen]; exact hK4, hs.sch, hs.scr, dSB⟩
  refine WP.seq (WP.mono (words_ok ws wi) fun s₄ h₄ => ?_)
  obtain ⟨s₅, hs₅, rg₅, o₅, -, -, f₅⟩ := restore_ok (s := s₄) (b := B) (n := 512)
    (by rw [h₄.wr]; exact hs.scr) (by rw [show sb = .r8 from rfl, h₄.r8]) h₄.saved
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases preserved_saved r hr with rfl | ⟨i, hi, rfl⟩
    · rw [o₅ _ (fun i hi => (sreg_ne_r2 i hi).symm), h₄.r2]
    · exact rg₅ i hi
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .r5) (16 * (Spec.Aes.rounds ((s₀.gpr .r4).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)
    rw [hS, hP, hK']
    have lhs : ∀ n, Spec.Aes.bytesAt s₅.mem S n = (List.range n).map fun k => s₅.mem (S + BitVec.ofNat 64 k) :=
      fun _ => rfl
    rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
      show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega]
    refine flatten_expandWords ws.len (by omega) _ _ fun k hk => ?_
    exact (f₅.bytes (R := ⟨S, 240⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dSB.sub_right (Region.sub_prefix (by decide))) (by simp) (show k < 240 by omega)).trans
      (h₄.sched k (by omega))

/-- A state satisfying the precondition. -/
def ekSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyPPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ek_correct hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, h₂⟩

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyPPC64LE.pre Proof.Aes.expandKeyPPC64LE.pub
    Impl.Aes.PPC64LE.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.expandKey
      (Spec.Aes.expandKeyScratchContract PPC64LE.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyScratchContract, Spec.Aes.expandKeyScratchSig,
      Proof.Aes.expandKeyPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [ekSatState] using ekSatState)

end VG.Proof.Aes.PPC64LE
