module

public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.Artifact

/-!
# The AES key expansion on RISC-V

As on PPC64LE (`Proof/Aes/PPC64LE/ExpandKey.lean`): `subAll` (`toBs`, the
S-box, `fromBs`) applies the S-box to every byte of the eight words
(`subAll_wp`); each word of the schedule is a few scalar instructions around
it (`word_ok`), and the loop over the words keeps the schedule's bytes so far
equal to the specification's (`WInv`). The key is copied a byte at a time
(`Bytes.copyBytes_ok`), and the words of the schedule are loaded and stored a
byte at a time (`ByteLoad.loadLE32_ok`, `ByteLoad.storeLE32_ok`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.RISCV64 in
/-- RISC-V contract for `vg_aes_expand_key_scratch(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32. The
pointers and `key_len` are public; the key is secret. -/
def expandKeyRISCV64 : Contract RISCV64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sched : Region := ⟨s.gpr .a2, 240⟩
    let scratch : Region := ⟨s.gpr .a3, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .a1).toNat = 16 ∨ (s.gpr .a1).toNat = 24 ∨ (s.gpr .a1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) (16 * (Spec.Aes.rounds ((s.gpr .a1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)

/-! ## The scratch buffer -/

/-- Bytes `d … d + n` from the rounded base are a part of the 512-byte buffer. -/
theorem scr512 (X : Addr) {d n : Nat} (h : d + n + 7 ≤ 512) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X) + BitVec.ofNat 64 d, n⟩ ⟨X, 512⟩ := by
  rw [Offset.add_add]
  have := pad_lt X
  exact Offset.sub_base X (by omega)

theorem scr512_base (X : Addr) {n : Nat} (h : n + 7 ≤ 512) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X), n⟩ ⟨X, 512⟩ := by
  have := pad_lt X
  exact Offset.sub_base X (by omega)

theorem bsKs_slots : ∀ p ∈ bsKs, 52 ≤ p.1 ∧ p.1 < 58 := by decide

/-- The masks of the transposes, outside the first 320 bytes. -/
theorem ctx_bsKs {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) bsKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) bsKs := by
  intro k v hk
  have := bsKs_slots _ hk
  rw [hc.base, slot_kept hc.frame (by omega) (by omega)]
  exact hm k v hk

/-! ## The S-box on every byte -/

/-- The four states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 64) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (b + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_stOf (Q : Nat → BitVec 64) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem subAll_wp {s : State} {X : Addr} (hs : Scr s X 512) (hm : MasksAt s.mem (s.gpr sb) bsKs)
    {P : State → Prop}
    (h : ∀ s', (∀ k < 8, ∀ t < 8, (Q s' k).extractLsb' (8 * t) 8 = sbox ((Q s k).extractLsb' (8 * t) 8)) →
      Ctx s s' → s'.gpr kp = s.gpr kp → P s') :
    WP isa (.block subAll) s P := by
  simp only [subAll]
  repeat rw [WP.block_append_iff (M := isa)]
  refine layer_wp (toBs_ok (hs.okExts rfl rfl rfl (by decide) (by decide)) hm) rfl (by decide)
    (Ctx.refl s) fun s₁ c₁ h₁ k₁ => ?_
  refine layer_wp (sbox_ok ((c₁.scr hs).okSlots rfl rfl rfl (by decide) (by decide))) rfl
    (by decide) c₁ fun s₂ c₂ h₂ k₂ => ?_
  refine layer_wp (fromBs_ok ((c₂.scr hs).okExts rfl rfl rfl (by decide) (by decide))
    (ctx_bsKs hm c₂)) rfl (by decide) c₂ fun s₃ c₃ h₃ k₃ => ?_
  have hin := in_of_bs h₃ (bs_subBytes h₂ (bs_of_in h₁ (inRel_stOf (Q s))))
  refine h s₃ (fun k hk t ht => ?_) c₃ (k₃.trans (k₂.trans k₁))
  refine byte_ext fun j hj => ?_
  have := hin (k % 4) (by omega_arith) (t + 8 * (k / 4)) (by omega_arith) j hj
  rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega_arith,
    show 8 * ((t + 8 * (k / 4)) % 8) + j = 8 * t + j by omega_arith] at this
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, this, getD_eq _ (by omega_arith)]
  simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
  rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega_arith,
    show (t + 8 * (k / 4)) % 8 = t by omega_arith]

/-! ## Bytes -/

theorem wp_srlw {is : List Instr} {s : State} {Q' : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 32)
    (k : ∀ s', Upd s s' d (sext32 ((s.gpr n).setWidth 32 >>> sh)) → WP isa (.block is) s' Q') :
    WP isa (.block (.shift .srl .w d n sh :: is)) s Q' :=
  WP.cons (exec_shift_w h) (k _ (Upd.write _ _ _))

theorem wp_sllw {is : List Instr} {s : State} {Q' : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 32)
    (k : ∀ s', Upd s s' d (sext32 ((s.gpr n).setWidth 32 <<< sh)) → WP isa (.block is) s' Q') :
    WP isa (.block (.shift .sll .w d n sh :: is)) s Q' :=
  WP.cons (exec_shift_w h) (k _ (Upd.write _ _ _))

/-- The round constant after one more round. -/
def rcNext (v : BitVec 64) : BitVec 64 :=
  ((v + v) ^^^ ((BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofInt 64 0x1b)) &&& BitVec.ofInt 64 0xff

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 64 := (Nat.repeat xtimes k (1 : Byte)).setWidth 64

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega_arith
  · rw [BitVec.getLsbD_of_ge _ _ (by omega_arith)]; simp

theorem xor32_byte (x : BitVec 64) (y : BitVec 32) {t : Nat} (ht : t < 4) :
    ((x ^^^ y.setWidth 64).setWidth 32).extractLsb' (8 * t) 8 =
      x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega_arith]
  intro; omega_arith

theorem sext32_low (v : BitVec 32) {i : Nat} (hi : i < 32) : (sext32 v).getLsbD i = v.getLsbD i := by
  rw [sext32, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

theorem rot_byte' (x c : BitVec 64) {t : Nat} (ht : t < 4) :
    ((sext32 (x.setWidth 32 <<< 24) ^^^ sext32 (x.setWidth 32 >>> 8)) ^^^ c).extractLsb' (8 * t) 8 =
      ((((x.setWidth 32).rotateRight 8).setWidth 64) ^^^ c).extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h32 : 8 * t + j < 32 := by omega
  have hr : (x.setWidth 32 >>> 8 ^^^ x.setWidth 32 <<< 24) = (x.setWidth 32).rotateRight 8 :=
    ByteLoad.rotr_shifts _ (by decide)
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, sext32_low _ h32, BitVec.getLsbD_setWidth,
    ← hr]
  simp only [hj, show 8 * t + j < 64 by omega, decide_true, Bool.true_and]
  cases (x.setWidth 32 >>> 8).getLsbD (8 * t + j) <;> cases (x.setWidth 32 <<< 24).getLsbD (8 * t + j) <;> rfl

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
  · rw [ite_eq_left h, Td h]
    simp [Tc]
  · rw [ite_eq_right h, Te h]
    simp [Tc]
    intro; omega_arith

theorem ld_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 4) :
    ((m.readW a 32).setWidth 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [Mem.readW_byte m a ht]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega_arith]
  intro; omega_arith

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega_arith

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega_arith

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega_arith

/-! ## The rotation and the round constant -/

/-- The slot of the round constant. -/
abbrev rcAddr (b : Addr) : Addr := wordAddr b rconSlot

theorem rc_contains {s : State} {X : Addr} (hs : Scr s X 512) :
    (⟨X, 512⟩ : Region).Contains (rcAddr (s.gpr sb)) 8 := hs.contains (by decide) (by decide)

theorem rotTail_wp {s : State} {X : Addr} (hs : Scr s X 512) {P : State → Prop}
    (h : ∀ s', s'.gpr (q 0) = (sext32 ((s.gpr (q 0)).setWidth 32 <<< 24) ^^^
        sext32 ((s.gpr (q 0)).setWidth 32 >>> 8)) ^^^ s.mem.readW (rcAddr (s.gpr sb)) 64 →
      s'.mem = s.mem.writeW (rcAddr (s.gpr sb)) (rcNext (s.mem.readW (rcAddr (s.gpr sb)) 64)) →
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      P s') :
    WP isa (.block rotTail) s P := by
  have hw' : InRegions (s.rd ++ s.wr) (rcAddr (s.gpr sb)) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, rc_contains hs⟩
  have hal : (rcAddr (s.gpr sb)).toNat % 8 = 0 := wordAddr_al hs.al _ (by decide)
  unfold rotTail
  simp only [ldS, stS, xorR, shrI]
  refine wp_srlw (by decide) fun s₁ u₁ => wp_sllw (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := rcAddr (s.gpr sb)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]) hal
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hw') fun s₄ u₄ => ?_
  refine wp_xor fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => ?_
  refine wp_sub fun s₈ u₈ => wp_andi (by decide) fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => ?_
  refine wp_xor fun s₁₁ u₁₁ => wp_andi (by decide) fun s₁₂ u₁₂ => ?_
  have hb₁₂ : s₁₂.gpr sb = s.gpr sb := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  refine wp_sd (a := rcAddr (s.gpr sb)) (by decide) (by rw [hb₁₂]) hal
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact ⟨_, hs.wr, rc_contains hs⟩) fun s₁₃ u₁₃ => WP.block_nil ?_
  have hne : q 0 ≠ q 1 ∧ q 0 ≠ q 2 ∧ q 0 ≠ q 3 ∧ q 1 ≠ q 2 ∧ q 1 ≠ q 3 ∧ q 2 ≠ q 3 ∧ q 1 ≠ t0 ∧
      q 2 ≠ t0 ∧ q 3 ≠ t0 ∧ q 0 ≠ t0 := by decide
  obtain ⟨n01, n02, n03, n12, n13, n23, n1t, n2t, n3t, n0t⟩ := hne
  let v := s.mem.readW (rcAddr (s.gpr sb)) 64
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rc₄ : s₄.gpr (q 1) = v := by rw [u₄.gpr, m₃]
  have q2₆ : s₆.gpr (q 2) = v >>> 7 := by rw [u₆.gpr, u₅.other _ (Ne.symm n01), rc₄]
  have q3₈ : s₈.gpr (q 3) = BitVec.ofNat 64 0 - (v >>> 7) := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ n23, q2₆]
  have q3₉ : s₉.gpr (q 3) = (BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofInt 64 0x1b := by
    rw [u₉.gpr, q3₈]
  have q1₉ : s₉.gpr (q 1) = v := by
    rw [u₉.other _ n13, u₈.other _ n13, u₇.other _ n13, u₆.other _ n12,
      u₅.other _ (Ne.symm n01), rc₄]
  have q1₁₁ : s₁₁.gpr (q 1) = (v + v) ^^^ ((BitVec.ofNat 64 0 - (v >>> 7)) &&& BitVec.ofInt 64 0x1b) := by
    rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (Ne.symm n13), q1₉, q3₉]
  have q1₁₂ : s₁₂.gpr (q 1) = rcNext v := by
    rw [u₁₂.gpr, q1₁₁]; rfl
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]
  refine h s₁₃ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · rw [u₁₃.gpr, u₁₂.other _ n01, u₁₁.other _ n01, u₁₀.other _ n01, u₉.other _ n03,
      u₈.other _ n03, u₇.other _ n03, u₆.other _ n02, u₅.gpr, u₄.other _ n01, u₃.gpr, u₂.gpr,
      u₂.other _ n0t.symm, u₁.gpr, u₁.other _ n0t, rc₄]
  · rw [u₁₃.mem, m₁₂, q1₁₂]
  · have hq : r ≠ q 0 ∧ r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 ∧ r ≠ t0 := by
      revert hr; cases r <;> decide
    obtain ⟨a0, a1, a2, a3, a4⟩ := hq
    rw [u₁₃.gpr, u₁₂.other _ a1, u₁₁.other _ a1, u₁₀.other _ a1, u₉.other _ a3, u₈.other _ a3,
      u₇.other _ a3, u₆.other _ a2, u₅.other _ a0, u₄.other _ a1, u₃.other _ a0, u₂.other _ a0,
      u₁.other _ a4]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
      u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr,
      u₁.wr]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp,
      u₁.sp]

/-! ## Words of the schedule, a byte at a time -/

theorem ld32_wp {s : State} {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 3 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4)
    {P : State → Prop}
    (k : ∀ s', s'.gpr d = (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64 →
      (∀ r, r ≠ d → r ≠ tmp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block (Impl.Words.RISCV64.loadLE32 d tmp n off)) s P := by
  refine WP.mono (ByteLoad.loadLE32_ok hdn htn hdt ho h) fun s' e => ?_
  subst e
  exact k _ (RegUpd.gpr_write_self _ _ _) (fun r h1 h2 => by
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]) rfl rfl rfl rfl

theorem st32_wp {s : State} {v tmp n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (ho : off + 3 < 2048) (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) {P : State → Prop}
    (k : ∀ s', s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32) →
      (∀ r, r ≠ tmp → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (Impl.Words.RISCV64.storeLE32 v tmp n off)) s P := by
  refine WP.mono (ByteLoad.storeLE32_ok htv htn ho h) fun s' e => ?_
  subst e
  exact k _ rfl (fun r h1 => RegUpd.gpr_write_of_ne _ _ h1) rfl rfl rfl

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

/-! ## One word -/

/-- The scratch buffer's base, rounded up. -/
abbrev rb (X : Addr) : Addr := X + BitVec.ofNat 64 (pad X)

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `X`, and the key `kl` of `nk` words. -/
structure WSetup (s₀ : State) (S X : Addr) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨X, 512⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 240⟩ ⟨X, 512⟩

/-- Before word `i`; `g` is what the callee-saved registers held. -/
structure WInv (s₀ : State) (S X : Addr) (g : Reg → BitVec 64) (kl : List Byte) (nk i : Nat)
    (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  a2 : s.gpr .a2 = S + BitVec.ofNat 64 (4 * (i - 1))
  a0 : s.gpr .a0 = S + BitVec.ofNat 64 (4 * (i - nk))
  a3 : s.gpr .a3 = BitVec.ofNat 64 (4 * (i % nk))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (4 * nk)
  a1 : s.gpr .a1 = BitVec.ofNat 64 (4 * (nk + 7) - i)
  a5 : s.gpr sb = rb X
  ra : s.gpr .ra = s₀.gpr .ra
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 4 * i, s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  rc : s.mem.readW (rcAddr (rb X)) 64 = rcW ((i - 1) / nk)
  masks : MasksAt s.mem (rb X) bsKs
  saved : Spill.Saved (rb X) g savedOffs s.mem
  frame : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s.mem

/-- After the last word. -/
structure WDone (s₀ : State) (S X : Addr) (g : Reg → BitVec 64) (kl : List Byte) (nk : Nat)
    (s : State) : Prop where
  a5 : s.gpr sb = rb X
  ra : s.gpr .ra = s₀.gpr .ra
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 16 * (nk + 7), s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  saved : Spill.Saved (rb X) g savedOffs s.mem
  frame : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s.mem

/-- `temp` computed (in the low 32 bits of `q 0`), from `s`. -/
structure Mid (b : Addr) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr (q 0)).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b, 320⟩, ⟨rcAddr b, 8⟩] s.mem s'.mem
  rc : s'.mem.readW (rcAddr b) 64 = rcW (i / nk)

theorem slot_disj (b : Addr) : Region.Disjoint ⟨rcAddr b, 8⟩ ⟨b, 320⟩ :=
  Offset.disjoint_base (d := 8 * 58) b (by decide) (by decide)

/-- A slot from 40 on, but the round constant's, is outside what `Mid` writes. -/
theorem slot_mid (b : Addr) {k : Nat} (h1 : 40 ≤ k) (h2 : k < 58) :
    ∀ r ∈ [(⟨b, 320⟩ : Region), ⟨rcAddr b, 8⟩], Region.Disjoint ⟨wordAddr b k, 8⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base (d := 8 * k) b (by omega) (by omega)
  · exact Offset.disjoint (d := 8 * k) (e := 8 * 58) b (by omega) (by omega) (by omega)

theorem masks_mid {m m' : Mem} {b : Addr} (hf : Frame [⟨b, 320⟩, ⟨rcAddr b, 8⟩] m m')
    (h : MasksAt m b bsKs) : MasksAt m' b bsKs := by
  intro k v hk
  have := bsKs_slots _ hk
  rw [← h k v hk]
  exact hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains]) (slot_mid b (by omega) (by omega))
    (by decide)

theorem saved_mid {m m' : Mem} {b : Addr} {g : Reg → BitVec 64}
    (hf : Frame [⟨b, 320⟩, ⟨rcAddr b, 8⟩] m m') (h : Spill.Saved b g savedOffs m) :
    Spill.Saved b g savedOffs m' := by
  refine h.frame_in savedOffs_range hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base b (by omega) (by omega)
  · exact Offset.disjoint (e := 8 * 58) b (by omega) (by omega) (by omega)

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`, and the next round constant. -/
theorem rot_wp {s₀ : State} {S X : Addr} {g : Reg → BitVec 64} {kl : List Byte} {nk i : Nat}
    (hs : WSetup s₀ S X kl nk) {s : State} (hi : WInv s₀ S X g kl nk i s) {s₁ : State}
    (hw : ∀ t < 4, (s₁.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0)
    (hsc : Scr s₁ X 512) (o₁ : ∀ r, r ≠ q 0 → r ≠ t0 → s₁.gpr r = s.gpr r) (m₁ : s₁.mem = s.mem)
    (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) (h0 : i % nk = 0) :
    WP isa (.block rotWordStep) s₁ (Mid (rb X) kl nk i s) := by
  have h3 := hs.nk3
  have hi1 := hi.hi
  have hn := hi.hn
  have hlen := kw_length hs.len (by omega_arith) (i - 1)
  simp only [rotWordStep]
  rw [WP.block_append_iff (M := isa)]
  have hm₁ : MasksAt s₁.mem (s₁.gpr sb) bsKs := by rw [m₁, hsc.base]; exact hi.masks
  refine subAll_wp hsc hm₁ fun s₂ h₂ c₂ k₂ => ?_
  refine rotTail_wp (hsc.congr c₂.wr c₂.base) fun s₃ q₃ m₃ o₃ rd₃ wr₃ _ => ?_
  have hb₂ : s₂.gpr sb = rb X := c₂.base.trans hsc.base
  rw [hb₂] at q₃ m₃
  have f₂ : Frame [⟨rb X, 320⟩] s₁.mem s₂.mem := by have := c₂.frame; rwa [hsc.base] at this
  have rc₂ : s₂.mem.readW (rcAddr (rb X)) 64 = rcW ((i - 1) / nk) := by
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_disj _) (by decide), m₁, hi.rc]
  refine ⟨fun t ht => ?_, fun r hr => ?_, rd₃.trans (c₂.rd.trans rd₁), wr₃.trans (c₂.wr.trans wr₁),
    ?_, ?_⟩
  · rw [q₃, rot_byte' _ _ ht, rot_byte _ _ ht, show s₂.gpr (q 0) = Q s₂ 0 from rfl,
      h₂ 0 (by omega_arith) _ (by omega_arith), show Q s₁ 0 = s₁.gpr (q 0) from rfl,
      hw _ (by omega_arith), rc₂, rcW_byte _ ht]
    simp only [kTemp, h0, ite_true]
    rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
      subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
      ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
  · have n0 : r ≠ q 0 := fun e => hr (e ▸ by decide)
    have nt : r ≠ t0 := fun e => hr (e ▸ by decide)
    by_cases hkp : r = kp
    · subst hkp; rw [o₃ _ hr, k₂, o₁ _ n0 nt]
    · rw [o₃ r hr, c₂.keep r hr hkp, o₁ r n0 nt]
  · rw [m₃, ← m₁]
    refine Frame.writeW (r := ⟨rcAddr (rb X), 8⟩) ?_ (by simp) _ (Region.contains_self _ _)
    exact f₂.mono (by simp)
  · rw [m₃, Mem.readW_writeW_self64, rc₂, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]

theorem temp_wp {s₀ : State} {S X : Addr} {g : Reg → BitVec 64} {kl : List Byte} {nk i : Nat}
    (hs : WSetup s₀ S X kl nk) {s : State} (hi : WInv s₀ S X g kl nk i s) {s₁ : State}
    (q0₁ : s₁.gpr (q 0) = (s.mem.readW (S + BitVec.ofNat 64 (4 * (i - 1))) 32).setWidth 64)
    (o₁ : ∀ r, r ≠ q 0 → r ≠ t0 → s₁.gpr r = s.gpr r)
    (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) :
    WP isa (.ite (.zero .a3) (.block rotWordStep)
        (.seq (.block [.addi t0 .a3 (-16)])
          (.ite (.zero t0) (.seq (.block [.addi t0 .a4 (-32)])
              (.ite (.zero t0) (.block subAll) (.block [])))
            (.block [])))) s₁ (Mid (rb X) kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega_arith
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have hsc : Scr s₁ X 512 :=
    ⟨by rw [wr₁, hi.wr]; exact hs.scr, by rw [o₁ sb (by decide) (by decide), hi.a5]⟩
  -- The bytes of `w[i − 1]`.
  have hw : ∀ t < 4, (s₁.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0 := by
    intro t ht
    rw [q0₁, ld_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, hi.sched _ (by omega_arith),
      show (4 * (i - 1) + t) / 4 = i - 1 by omega_arith, show (4 * (i - 1) + t) % 4 = t by omega_arith]
  have hlen := kw_length hs.len hnk (i - 1)
  have mid_of : ∀ s', s'.gpr (q 0) = s₁.gpr (q 0) → (∀ r, r ∉ sboxWrites → s'.gpr r = s₁.gpr r) →
      s'.mem = s.mem → s'.rd = s₁.rd → s'.wr = s₁.wr → i % nk ≠ 0 →
      kTemp nk i (kw kl nk (i - 1)) = kw kl nk (i - 1) → Mid (rb X) kl nk i s s' := by
    intro s' hq hk hm hrd hwr hne ht
    refine ⟨fun t htt => by rw [hq, hw t htt, ht], fun r hr => (hk r hr).trans (o₁ r ?_ ?_),
      hrd.trans rd₁, hwr.trans wr₁, by rw [hm]; exact Frame.refl _ _, ?_⟩
    · intro h; subst h; exact hr (by decide)
    · intro h; subst h; exact hr (by decide)
    · rw [hm, hi.rc, div_pred_ne h3 hne]
  have a3₁ : s₁.gpr .a3 = BitVec.ofNat 64 (4 * (i % nk)) := by
    rw [o₁ _ (by decide) (by decide), hi.a3]
  refine WP.ite (decide (4 * (i % nk) = 0)) (eval_zero_ofNat _ _ (by omega_arith) a3₁)
    (fun hb => ?_) (fun hb => ?_)
  · exact rot_wp hs hi hw hsc o₁ m₁ rd₁ wr₁ (by simp at hb; omega_arith)
  · have h0 : i % nk ≠ 0 := by simp at hb; omega_arith
    refine WP.seq (wp_subi (imm := 16) (by decide) fun s₄ u₄ => WP.block_nil ?_)
    have t₄ : isa.eval (.zero t0) s₄ = some (decide (4 * (i % nk) = 16)) := by
      rw [eval_zero, u₄.gpr, a3₁, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    refine WP.ite (decide (4 * (i % nk) = 16)) t₄ (fun hb₄ => ?_) (fun hb₄ => ?_)
    · have h4 : 4 * (i % nk) = 16 := by simpa using hb₄
      refine WP.seq (wp_subi (imm := 32) (by decide) fun s₅ u₅ => WP.block_nil ?_)
      have t₅ : isa.eval (.zero t0) s₅ = some (decide (4 * nk = 32)) := by
        rw [eval_zero, u₅.gpr, u₄.other _ (by decide), o₁ _ (by decide) (by decide), hi.a4,
          Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
      have g₅ : ∀ r, r ≠ t0 → s₅.gpr r = s₁.gpr r := fun r h => by
        rw [u₅.other _ h, u₄.other _ h]
      refine WP.ite (decide (4 * nk = 32)) t₅ (fun hb₅ => ?_) (fun hb₅ => ?_)
      · -- `SUBWORD(temp)`.
        have h8 : nk = 8 := by simp at hb₅; omega_arith
        have sc₅ : Scr s₅ X 512 := hsc.congr (u₅.wr.trans u₄.wr) (g₅ _ (by decide))
        have hm₅ : MasksAt s₅.mem (s₅.gpr sb) bsKs := by
          rw [u₅.mem, u₄.mem, m₁, sc₅.base]; exact hi.masks
        refine subAll_wp sc₅ hm₅ fun s₆ h₆ c₆ k₆ => ?_
        have f₆ : Frame [⟨rb X, 320⟩] s₅.mem s₆.mem := by have := c₆.frame; rwa [sc₅.base] at this
        rw [u₅.mem, u₄.mem, m₁] at f₆
        refine ⟨fun t ht => ?_, fun r hr => ?_, by rw [c₆.rd, u₅.rd, u₄.rd, rd₁],
          by rw [c₆.wr, u₅.wr, u₄.wr, wr₁], f₆.mono (by simp), ?_⟩
        · rw [show s₆.gpr (q 0) = Q s₆ 0 from rfl, h₆ 0 (by omega_arith) _ (by omega_arith),
            show Q s₅ 0 = s₁.gpr (q 0) by simp only [Q]; rw [g₅ _ (by decide)], hw _ ht]
          rw [kTemp, ite_eq_right h0, ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega_arith),
            subWord_getD (by rw [hlen]; exact ht)]
        · have n0 : r ≠ q 0 := fun e => hr (e ▸ by decide)
          have nt : r ≠ t0 := fun e => hr (e ▸ by decide)
          have e : s₆.gpr r = s₅.gpr r := by
            by_cases hkp : r = kp
            · subst hkp; exact k₆
            · exact c₆.keep r hr hkp
          rw [e, g₅ r nt, o₁ r n0 nt]
        · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact slot_disj _) (by decide), hi.rc,
            div_pred_ne h3 h0]
      · have h8 : nk ≠ 8 := by simp at hb₅; omega_arith
        refine WP.block_nil (mid_of s₅ (g₅ _ (by decide))
          (fun r hr => g₅ r (fun h => by subst h; exact hr (by decide)))
          (by rw [u₅.mem, u₄.mem, m₁]) (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]) h0 ?_)
        rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega_arith)]
    · have h4 : 4 * (i % nk) ≠ 16 := by simpa using hb₄
      refine WP.block_nil (mid_of s₄ (u₄.other _ (by decide))
        (fun r hr => u₄.other r (fun h => by subst h; exact hr (by decide))) (by rw [u₄.mem, m₁])
        u₄.rd u₄.wr h0 ?_)
      rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega_arith)]

/-! ## Storing a word -/

/-- A part of the scratch buffer is outside a part of the schedule. -/
theorem slot_sched {S X : Addr} (sep : Region.Disjoint ⟨S, 240⟩ ⟨X, 512⟩) {d n e l : Nat}
    (hd : d + n ≤ 240) (he : e + l + 7 ≤ 512) :
    Region.Disjoint ⟨rb X + BitVec.ofNat 64 e, l⟩ ⟨S + BitVec.ofNat 64 d, n⟩ :=
  ((sep.sub_left (Offset.sub_base S hd)).sub_right (scr512 X he)).symm

/-- A write to the schedule keeps the masks, the saved registers and the round constant. -/
theorem sched_write {S X : Addr} (sep : Region.Disjoint ⟨S, 240⟩ ⟨X, 512⟩) {d n : Nat}
    (hd : d + n ≤ 240) {m m' : Mem} (hf : Frame [⟨S + BitVec.ofNat 64 d, n⟩] m m')
    {g : Reg → BitVec 64} :
    (MasksAt m (rb X) bsKs → MasksAt m' (rb X) bsKs) ∧
      (Spill.Saved (rb X) g savedOffs m → Spill.Saved (rb X) g savedOffs m') ∧
      m'.readW (rcAddr (rb X)) 64 = m.readW (rcAddr (rb X)) 64 := by
  refine ⟨fun h k v hk => ?_, fun h => h.frame_in savedOffs_range hf fun r hr => ?_, ?_⟩
  · have := bsKs_slots _ hk
    rw [← h k v hk]
    exact hf.readW (r := ⟨wordAddr (rb X) k, 8⟩) (by simp [Region.Contains]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact slot_sched sep (e := 8 * k) hd (by omega)) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact slot_sched sep hd (by decide)
  · exact hf.readW (r := ⟨rcAddr (rb X), 8⟩) (by simp [Region.Contains]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact slot_sched sep (e := 8 * 58) hd (by decide)) (by decide)

/-- The memory after word `i` is stored. -/
def storeMem (s₂ : State) (S : Addr) (nk i : Nat) : Mem :=
  s₂.mem.writeW (S + BitVec.ofNat 64 (4 * i))
    ((s₂.gpr (q 0) ^^^ (s₂.mem.readW (S + BitVec.ofNat 64 (4 * (i - nk))) 32).setWidth 64).setWidth 32)

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Frame.writeW (Frame.refl [⟨a, 4⟩] m) (List.mem_singleton_self _) v (Region.contains_self _ _) x
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x (Region.contains_self _ _)

theorem store_facts {s₀ : State} {S X : Addr} {g : Reg → BitVec 64} {kl : List Byte} {nk i : Nat}
    (hs : WSetup s₀ S X kl nk) {s s₂ : State} (hi : WInv s₀ S X g kl nk i s)
    (hm : Mid (rb X) kl nk i s s₂) :
    (∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0) ∧
    Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem (storeMem s₂ S nk i) ∧
    Spill.Saved (rb X) g savedOffs (storeMem s₂ S nk i) ∧ MasksAt (storeMem s₂ S nk i) (rb X) bsKs ∧
    (storeMem s₂ S nk i).readW (rcAddr (rb X)) 64 = rcW (i / nk) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega_arith
  have hi1 := hi.hi
  have hn := hi.hn
  have h4i : 4 * i + 4 ≤ 240 := by rcases h3 with rfl | rfl | rfl <;> omega_arith
  have dM : ∀ r ∈ [(⟨rb X, 320⟩ : Region), ⟨rcAddr (rb X), 8⟩], Region.Disjoint ⟨S, 240⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.sep.sub_right (scr512_base X (by decide))
    · exact hs.sep.sub_right (scr512 X (d := 8 * 58) (by decide))
  have fS : ∀ k < 240, s₂.mem (S + BitVec.ofNat 64 k) = s.mem (S + BitVec.ofNat 64 k) := fun k hk =>
    hm.frame.bytes (R := ⟨S, 240⟩) dM (by simp) hk
  have fw : Frame [⟨S + BitVec.ofNat 64 (4 * i), 4⟩] s₂.mem (storeMem s₂ S nk i) :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨wm, ws, wr⟩ := sched_write (g := g) hs.sep h4i fw
  refine ⟨fun k hk => ?_, ?_, ws (saved_mid hm.frame hi.saved), wm (masks_mid hm.frame hi.masks),
    by rw [wr, hm.rc]⟩
  · unfold storeMem
    by_cases hki : k < 4 * i
    · rw [writeW32_other _ (Offset.disjoint S (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        fS k (by omega_arith), hi.sched k hki]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * i + t := ⟨k - 4 * i, by omega_arith, by omega_arith⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, xor32_byte _ _ ht, hm.temp t ht,
        ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, fS _ (by omega_arith),
        hi.sched _ (by omega_arith), show (4 * (i - nk) + t) / 4 = i - nk by omega_arith,
        show (4 * (i - nk) + t) % 4 = t by omega_arith, show (4 * i + t) / 4 = i by omega_arith,
        show (4 * i + t) % 4 = t by omega_arith, kw_step kl hnk hi1,
        xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  · refine (hi.frame.trans (hm.frame.sub fun r hr => ?_)).trans
      (fw.sub fun r hr => ⟨⟨S, 240⟩, by simp, ?_⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨X, 512⟩, by simp, scr512_base X (by decide)⟩
      · exact ⟨⟨X, 512⟩, by simp, scr512 X (d := 8 * 58) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base S h4i

theorem ofNat_sub_one {j : Nat} (h : 0 < j) :
    BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega_arith, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem add4 (S : Addr) (x : Nat) :
    S + BitVec.ofNat 64 x + BitVec.ofNat 64 4 = S + BitVec.ofNat 64 (x + 4) := Offset.add_add S x 4

theorem word_ok {s₀ : State} {S X : Addr} {g : Reg → BitVec 64} {kl : List Byte} {nk i : Nat}
    (hs : WSetup s₀ S X kl nk) {s : State} (hi : WInv s₀ S X g kl nk i s) :
    WP isa wordBody s fun s' =>
      (isa.eval (.nonzero .a1) s' = some true ∧ WInv s₀ S X g kl nk (i + 1) s') ∨
      (isa.eval (.nonzero .a1) s' = some false ∧ WDone s₀ S X g kl nk s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega_arith
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have h4i : 4 * i + 4 ≤ 240 := by rcases h3 with rfl | rfl | rfl <;> omega_arith
  have hrS : (⟨S, 240⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ (by rw [hi.wr]; exact hs.sch)
  unfold wordBody
  refine WP.seq ?_
  refine ld32_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [hi.a2, add_ofNat_zero]; exact in_off hrS (by omega_arith) (by omega_arith))
    fun s₁ q0₁ o₁ m₁ rd₁ wr₁ _ => ?_
  rw [hi.a2, add_ofNat_zero] at q0₁
  refine WP.seq (WP.mono (temp_wp hs hi q0₁ o₁ m₁ rd₁ wr₁) fun s₂ hm => ?_)
  have k₂ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a4, sb], s₂.gpr r = s.gpr r := fun r hr =>
    hm.keep r (by revert hr; revert r; decide)
  have hwS : (⟨S, 240⟩ : Region) ∈ s₂.wr := by rw [hm.wr, hi.wr]; exact hs.sch
  -- `w[i] := w[i − Nk] ⊕ temp`.
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  have a0₂ : s₂.gpr .a0 = S + BitVec.ofNat 64 (4 * (i - nk)) := (k₂ .a0 (by simp)).trans hi.a0
  refine ld32_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [a0₂, add_ofNat_zero]; exact in_off (List.mem_append_right _ hwS) (by omega_arith) (by omega_arith))
    fun s₃ t0₃ o₃ m₃ rd₃ wr₃ _ => ?_
  rw [a0₂, add_ofNat_zero] at t0₃
  refine wp_xor fun s₄ u₄ => WP.block_nil ?_
  have a2₄ : s₄.gpr .a2 = S + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [u₄.other _ (by decide), o₃ _ (by decide) (by decide), k₂ .a2 (by simp), hi.a2]
  have ad₄ : s₄.gpr .a2 + BitVec.ofNat 64 4 = S + BitVec.ofNat 64 (4 * i) := by
    rw [a2₄, add4, show 4 * (i - 1) + 4 = 4 * i by omega_arith]
  refine st32_wp (by decide) (by decide) (by decide)
    (by rw [ad₄, u₄.wr, wr₃]; exact in_off hwS (by omega_arith) (by omega_arith)) fun s₅ m₅ o₅ rd₅ wr₅ _ => ?_
  refine wp_addi (imm := 4) (by decide) fun s₆ u₆ => wp_addi (imm := 4) (by decide) fun s₇ u₇ => ?_
  refine wp_addi (imm := 4) (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_
  have mem₉ : s₉.mem = storeMem s₂ S nk i := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, ad₄, u₄.gpr, u₄.mem, t0₃, m₃,
      o₃ _ (by decide) (by decide), storeMem]
  have g₅ : ∀ r, r ≠ q 0 → r ≠ t0 → r ≠ t1 → s₅.gpr r = s₂.gpr r := fun r h0 ht h1 => by
    rw [o₅ r ht, u₄.other r h0, o₃ r ht h1]
  have a3₈ : s₈.gpr .a3 = BitVec.ofNat 64 (4 * (i % nk) + 4) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide),
      k₂ .a3 (by simp), hi.a3]
    exact (BitVec.ofNat_add _ _).symm
  have a4₉ : s₉.gpr .a4 = BitVec.ofNat 64 (4 * nk) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide) (by decide) (by decide), k₂ .a4 (by simp), hi.a4]
  have t₉ : s₉.gpr t0 = BitVec.ofNat 64 (4 * (i % nk) + 4) - BitVec.ofNat 64 (4 * nk) := by
    rw [u₉.gpr, a3₈, ← a4₉, u₉.other _ (by decide)]
  have g₉ : ∀ r ∈ [Reg.ra, .a1, .a4, sb], s₉.gpr r = s.gpr r := fun r hr => by
    rw [u₉.other r (by revert hr; revert r; decide), u₈.other r (by revert hr; revert r; decide),
      u₇.other r (by revert hr; revert r; decide), u₆.other r (by revert hr; revert r; decide),
      g₅ r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      k₂ r (by revert hr; revert r; decide)]
  have a2₉ : s₉.gpr .a2 = S + BitVec.ofNat 64 (4 * (i + 1 - 1)) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      g₅ _ (by decide) (by decide) (by decide), k₂ .a2 (by simp), hi.a2, add4,
      show 4 * (i - 1) + 4 = 4 * (i + 1 - 1) by omega_arith]
  have a0₉ : s₉.gpr .a0 = S + BitVec.ofNat 64 (4 * (i + 1 - nk)) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅ _ (by decide) (by decide) (by decide), a0₂, add4,
      show 4 * (i - nk) + 4 = 4 * (i + 1 - nk) by omega_arith]
  -- `a3 := 4 ((i + 1) mod Nk)`.
  refine WP.seq (WP.mono (Q := fun (s₁₀ : State) =>
      s₁₀.gpr .a3 = BitVec.ofNat 64 (4 * ((i + 1) % nk)) ∧
      (∀ r, r ≠ .a3 → s₁₀.gpr r = s₉.gpr r) ∧ s₁₀.mem = s₉.mem ∧ s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr) ?_
    fun s₁₀ ⟨a3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ => ?_)
  · have e₉ : isa.eval (.zero t0) s₉ = some (decide (4 * (i % nk) + 4 = 4 * nk)) := by
      rw [eval_zero, t₉, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    refine WP.ite (decide (4 * (i % nk) + 4 = 4 * nk)) e₉ (fun hb => ?_) (fun hb => ?_)
    · refine wp_li (imm := 0) (by decide) fun s' u' => WP.block_nil ⟨?_, u'.other, u'.mem, u'.rd, u'.wr⟩
      have h1 : (i + 1) % nk = 0 := by
        have : i % nk + 1 = nk := by simp at hb; omega_arith
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega_arith), this, Nat.mod_self]
      rw [u'.gpr, h1]
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      have h1 : (i + 1) % nk = i % nk + 1 := by
        have : i % nk + 1 < nk := by simp at hb; omega_arith
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega_arith), Nat.mod_eq_of_lt this]
      rw [u₉.other _ (by decide), a3₈, h1, Nat.mul_add, Nat.mul_one]
  -- `a1 := a1 − 1`.
  refine wp_subi (imm := 1) (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
  have a1₁₁ : s₁₁.gpr .a1 = BitVec.ofNat 64 (4 * (nk + 7) - i - 1) := by
    rw [u₁₁.gpr, o₁₀ _ (by decide), g₉ .a1 (by simp), hi.a1, ofNat_sub_one (by omega_arith)]
  have ev := Steps.eval_nonzero_ofNat s₁₁ .a1 (by omega_arith) a1₁₁
  have gk : ∀ r ∈ [Reg.ra, .a4, sb], s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [u₁₁.other r (by revert hr; revert r; decide), o₁₀ r (by revert hr; revert r; decide),
      g₉ r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
  have mem₁₁ : s₁₁.mem = storeMem s₂ S nk i := by rw [u₁₁.mem, m₁₀, mem₉]
  obtain ⟨sched', fr, sv, mk, rc⟩ := store_facts hs hi hm
  rw [← mem₁₁] at sched' fr sv mk rc
  have ra₁₁ : s₁₁.gpr .ra = s₀.gpr .ra := (gk .ra (by simp)).trans hi.ra
  have a5₁₁ : s₁₁.gpr sb = rb X := (gk sb (by simp)).trans hi.a5
  have rd : s₁₁.rd = s₀.rd := by
    rw [u₁₁.rd, rd₁₀, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, u₄.rd, rd₃, hm.rd, hi.rd]
  have wr : s₁₁.wr = s₀.wr := by
    rw [u₁₁.wr, wr₁₀, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, u₄.wr, wr₃, hm.wr, hi.wr]
  by_cases hl : 4 * (nk + 7) - i - 1 = 0
  · refine .inr ⟨by rw [ev, hl]; rfl, a5₁₁, ra₁₁, rd, wr, fun k hk => sched' k (by omega_arith), sv, fr⟩
  · refine .inl ⟨by rw [ev]; simp [hl], ⟨by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, a5₁₁, ra₁₁,
      rd, wr, sched', by rw [Nat.add_sub_cancel]; exact rc, mk, sv, fr⟩⟩
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), a2₉]
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), a0₉]
    · rw [u₁₁.other _ (by decide), a3₁₀]
    · rw [gk .a4 (by simp), hi.a4]
    · rw [a1₁₁, Nat.sub_sub]

/-! ## The loop over the words -/

theorem words_ok {s₀ : State} {S X : Addr} {g : Reg → BitVec 64} {kl : List Byte} {nk : Nat}
    (hs : WSetup s₀ S X kl nk) {s : State} (hi : WInv s₀ S X g kl nk nk s) :
    WP isa (.loop wordBody (.nonzero .a1)) s (WDone s₀ S X g kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₀ S X g kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hi.hn; omega_arith, i + 1, rfl, d⟩
  · exact .inl ⟨z, d⟩

/-! ## Copying the key -/

/-- The key's bytes. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- The setting of the copy: the key (`K` bytes at `P`) is outside what is written. -/
structure CSetup (s₀ : State) (S X P : Addr) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨P, K⟩ : Region) ∈ s₀.rd
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨X, 512⟩ : Region) ∈ s₀.wr
  dS : Region.Disjoint ⟨P, K⟩ ⟨S, 240⟩
  dB : Region.Disjoint ⟨P, K⟩ ⟨X, 512⟩
  sep : Region.Disjoint ⟨S, 240⟩ ⟨X, 512⟩

/-- During the copy, after `c` doublewords. -/
structure CInv (s₀ : State) (S X P : Addr) (K : Nat) (g : Reg → BitVec 64) (c : Nat) (s : State) :
    Prop where
  hc : 8 * c < K
  a0 : s.gpr .a0 = P + BitVec.ofNat 64 (8 * c)
  a2 : s.gpr .a2 = S + BitVec.ofNat 64 (8 * c)
  a1 : s.gpr .a1 = BitVec.ofNat 64 (K - 8 * c)
  a4 : s.gpr .a4 = BitVec.ofNat 64 K
  a5 : s.gpr sb = rb X
  ra : s.gpr .ra = s₀.gpr .ra
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < 8 * c, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  masks : MasksAt s.mem (rb X) bsKs
  saved : Spill.Saved (rb X) g savedOffs s.mem
  frame : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s.mem

/-- After the copy. -/
structure CDone (s₀ : State) (S X P : Addr) (K : Nat) (g : Reg → BitVec 64) (s : State) : Prop where
  a2 : s.gpr .a2 = S + BitVec.ofNat 64 K
  a4 : s.gpr .a4 = BitVec.ofNat 64 K
  a5 : s.gpr sb = rb X
  ra : s.gpr .ra = s₀.gpr .ra
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < K, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  masks : MasksAt s.mem (rb X) bsKs
  saved : Spill.Saved (rb X) g savedOffs s.mem
  frame : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s.mem

theorem add8 (S : Addr) (c : Nat) :
    S + BitVec.ofNat 64 (8 * c) + BitVec.ofNat 64 8 = S + BitVec.ofNat 64 (8 * (c + 1)) := by
  rw [Offset.add_add, Nat.mul_succ]

theorem copy_ok {s₀ : State} {S X P : Addr} {K : Nat} {g : Reg → BitVec 64} (hs : CSetup s₀ S X P K)
    {c : Nat} {s : State} (hi : CInv s₀ S X P K g c s) :
    WP isa (.block copyBody) s fun s' =>
      (isa.eval (.nonzero .a1) s' = some true ∧ CInv s₀ S X P K g (c + 1) s') ∨
      (isa.eval (.nonzero .a1) s' = some false ∧ CDone s₀ S X P K g s') := by
  have hK := hs.hK
  have hc := hi.hc
  have hc8 : 8 * c + 8 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega_arith
  unfold copyBody
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Bytes.copyBytes_ok (tmp := t0) (src := .a0) (dst := .a2) (soff := 0) (doff := 0)
    (n := 8) (by decide) (by decide) (by decide) (by decide) (fun j hj => ?_) (fun j hj => ?_)
    (fun j hj hc' => ?_)) fun s₁ h₁ => ?_
  · rw [hi.a0, Offset.add_add]
    exact in_off (List.mem_append_left _ (by rw [hi.rd]; exact hs.key)) (by omega_arith) (by omega_arith)
  · rw [hi.a2, Offset.add_add]
    exact in_off (by rw [hi.wr]; exact hs.sch) (by omega_arith) (by omega_arith)
  · simp only [hi.a2, hi.a0, Offset.add_add] at hc'
    exact hs.dS _ (Offset.contains_base P (by omega_arith) (by omega_arith))
      (Offset.sub_base S (d := 8 * c + 0) (n := 8) (k := 240) (by omega_arith) _ hc')
  refine wp_addi (imm := 8) (by decide) fun s₂ u₂ => wp_addi (imm := 8) (by decide) fun s₃ u₃ => ?_
  refine wp_subi (imm := 8) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have g₄ : ∀ r, r ≠ t0 → r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, h₁.gpr r h1]
  have a1₄ : s₄.gpr .a1 = BitVec.ofNat 64 (K - 8 * (c + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr _ (by decide), hi.a1,
      Offset.ofNat_sub_ofNat (show 8 ≤ K - 8 * c by omega_arith),
      show K - 8 * c - 8 = K - 8 * (c + 1) by omega_arith]
  have ev := Steps.eval_nonzero_ofNat s₄ .a1 (by omega_arith) a1₄
  have fW : Frame [⟨S + BitVec.ofNat 64 (8 * c), 8⟩] s.mem s₄.mem := by
    rw [m₄]; have := h₁.frame; rwa [hi.a2, add_ofNat_zero] at this
  have h8 : 8 * c + 8 ≤ 240 := by rcases hK with rfl | rfl | rfl <;> omega_arith
  obtain ⟨wm, ws, -⟩ := sched_write (g := g) hs.sep h8 fW
  have copied : ∀ k < 8 * (c + 1), s₄.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
    intro k hk
    by_cases hkc : k < 8 * c
    · rw [fW _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (d := k) (n := 1) (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
          _ (Region.contains_self _ _), hi.copied k hkc]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 8 ∧ k = 8 * c + t := ⟨k - 8 * c, by omega_arith, by omega_arith⟩
      have := h₁.copied t ht
      rw [hi.a2, hi.a0, Offset.add_add, Offset.add_add, Nat.zero_add] at this
      rw [m₄, this]
      exact hi.frame.bytes (R := ⟨P, K⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.dS
        · exact hs.dB) (by simp only; omega_arith) (show 8 * c + t < K by omega_arith)
  have fr : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s₄.mem :=
    hi.frame.trans (fW.sub fun r hr => ⟨⟨S, 240⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base S h8⟩)
  have a2₄ : s₄.gpr .a2 = S + BitVec.ofNat 64 (8 * (c + 1)) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₁.gpr _ (by decide), hi.a2, add8]
  have rd : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd, hi.rd]
  have wr : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr, hi.wr]
  have a4₄ : s₄.gpr .a4 = BitVec.ofNat 64 K := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), hi.a4]
  have a5₄ : s₄.gpr sb = rb X := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), hi.a5]
  have ra₄ : s₄.gpr .ra = s₀.gpr .ra := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), hi.ra]
  by_cases hl : K - 8 * (c + 1) = 0
  · refine .inr ⟨by rw [ev]; simp [hl], ?_, a4₄, a5₄, ra₄, rd, wr,
      fun k hk => copied k (by omega_arith), wm hi.masks, ws hi.saved, fr⟩
    rw [a2₄, show 8 * (c + 1) = K by omega_arith]
  · refine .inl ⟨by rw [ev]; simp [hl], ⟨by omega_arith, ?_, a2₄, a1₄, a4₄, a5₄, ra₄, rd, wr, copied,
      wm hi.masks, ws hi.saved, fr⟩⟩
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h₁.gpr _ (by decide), hi.a0, add8]

theorem copyLoop_ok {s₀ : State} {S X P : Addr} {K : Nat} {g : Reg → BitVec 64}
    (hs : CSetup s₀ S X P K) {s : State} (hi : CInv s₀ S X P K g 0 s) :
    WP isa (.loop (.block copyBody) (.nonzero .a1)) s (CDone s₀ S X P K g) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 8 * c ∧ CInv s₀ S X P K g c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hc.hc; omega_arith, c + 1, rfl, d⟩
  · exact .inl ⟨z, d⟩

/-! ## Setting up the word loop -/

theorem kw_getD_key (kl : List Byte) {nk k : Nat} (hk : k < 4 * nk) :
    (kw kl nk (k / 4)).getD (k % 4) 0 = kl.getD k 0 := by
  rw [kw_key kl (show k / 4 < nk by omega_arith)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp [show k % 4 < 4 by omega_arith, Nat.div_add_mod]

theorem a1_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    (BitVec.ofNat 64 K >>> 2) + ((BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2)) +
      BitVec.ofNat 64 28 = BitVec.ofNat 64 (4 * (K / 4 + 7) - K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

/-- What the round constant's store keeps. -/
theorem rc_write {m m' : Mem} {b : Addr} {g : Reg → BitVec 64} (hf : Frame [⟨rcAddr b, 8⟩] m m') :
    (MasksAt m b bsKs → MasksAt m' b bsKs) ∧
      (Spill.Saved b g savedOffs m → Spill.Saved b g savedOffs m') :=
  have hf' := hf.mono (rs' := [⟨b, 320⟩, ⟨rcAddr b, 8⟩]) (by simp)
  ⟨masks_mid hf', saved_mid hf'⟩

theorem wordSetup_wp {s₀ : State} {S X P : Addr} {K : Nat} {g : Reg → BitVec 64}
    (hs : CSetup s₀ S X P K) {s : State} (h : CDone s₀ S X P K g s) :
    WP isa (.block wordSetup) s fun s' =>
      WInv s₀ S X g (Spec.Aes.bytesAt s₀.mem P K) (K / 4) (K / 4) s' := by
  have hK := hs.hK
  have hK4 : K = 4 * (K / 4) := by omega_arith
  unfold wordSetup
  simp only [stS, shrI, rconSlot]
  refine wp_sub fun s₁ u₁ => wp_subi (imm := 4) (by decide) fun s₂ u₂ => ?_
  refine wp_li (imm := 0) (by decide) fun s₃ u₃ => wp_srl (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  refine wp_add fun s₆ u₆ => wp_addi (imm := 28) (by decide) fun s₇ u₇ => ?_
  refine wp_li (imm := 1) (by decide) fun s₈ u₈ => ?_
  have hb₈ : s₈.gpr sb = rb X := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.a5]
  have wr₈ : s₈.wr = s₀.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have hsc : Scr s₈ X 512 := ⟨by rw [wr₈]; exact hs.scr, hb₈⟩
  refine wp_sd (a := rcAddr (rb X)) (by decide) (by rw [hb₈]; rfl)
    (wordAddr_al (hb₈ ▸ hsc.al) _ (by decide))
    ⟨_, hsc.wr, by rw [← hb₈]; exact rc_contains hsc⟩ fun s₉ u₉ => WP.block_nil ?_
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hm : s₉.mem = s.mem.writeW (rcAddr (rb X)) (BitVec.ofNat 64 1) := by
    rw [u₉.mem, m₈, u₈.gpr]
  have fw : Frame [⟨rcAddr (rb X), 8⟩] s.mem s₉.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (by simp) _ (Region.contains_self _ _)
  obtain ⟨wm, ws⟩ := rc_write (g := g) fw
  have a4 : s.gpr .a4 = BitVec.ofNat 64 K := h.a4
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  refine ⟨Nat.le_refl _, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₉.wr, wr₈], ?_, ?_,
    wm h.masks, ws h.saved, ?_⟩
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.a2, Offset.add_ofNat_sub S (show 4 ≤ K by omega_arith),
      show K - 4 = 4 * (K / 4 - 1) by omega_arith]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h.a2, a4, Nat.sub_self, Nat.mul_zero, add_ofNat_zero, BitVec.add_sub_cancel]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, Nat.mod_self]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), a4, ← hK4]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), a4, a1_setup hK]
  · rw [u₉.gpr]; exact hb₈
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.ra]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · intro k hk
    rw [fw.bytes (R := ⟨S, 240⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hs.sep.sub_right (scr512 X (d := 8 * 58) (by decide))) (by simp)
        (show k < 240 by rcases hK with rfl | rfl | rfl <;> omega_arith),
      h.copied k (by omega_arith), ← bytesAt_getD s₀.mem P (show k < K by omega_arith),
      kw_getD_key _ (by omega_arith)]
  · rw [hm, Mem.readW_writeW_self64, Nat.div_eq_of_lt (by omega_arith)]
    decide
  · exact h.frame.trans (fw.sub fun r hr => ⟨⟨X, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact scr512 X (d := 8 * 58) (by decide)⟩)

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} {S X P : Addr} {K : Nat} (hs : CSetup s₀ S X P K)
    (hS : s₀.gpr .a2 = S) (hB : s₀.gpr .a3 = X) (hP : s₀.gpr .a0 = P)
    (hKr : s₀.gpr .a1 = BitVec.ofNat 64 K) :
    WP isa (.block ([movR sb .a3] ++ roundSb ++ saveRegs ++ storeMasks bsSlot bsMasks ++
      [movR .a4 .a1])) s₀ fun s =>
      ∃ g, (∀ r ∈ RISCV64.preserved, g r = s₀.gpr r) ∧ CInv s₀ S X P K g 0 s := by
  have hK := hs.hK
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa), WP.block_append_iff (M := isa),
    WP.block_append_iff (M := isa)]
  simp only [movR]
  refine wp_mv fun s₁ u₁ => WP.block_nil ?_
  refine roundSb_wp fun s₂ b₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_
  have hb₂ : s₂.gpr sb = rb X := by rw [b₂, u₁.gpr, hB]
  have hscr₂ : Scr s₂ X 512 := ⟨by rw [wr₂, u₁.wr]; exact hs.scr, hb₂⟩
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₂.al savedOffs_ho (fun p hp => ⟨_, hscr₂.wr,
    hscr₂.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) (WP.block_nil ?_)
  generalize hS' : ({ s₂ with mem := Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs } : State) = s₂'
  have g₂' : s₂'.gpr = s₂.gpr := by rw [← hS']
  have mm₂ : s₂'.mem = Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs := by rw [← hS']
  have rd₂' : s₂'.rd = s₂.rd := by rw [← hS']
  have wr₂' : s₂'.wr = s₂.wr := by rw [← hS']
  have sv₂ : Spill.Saved (rb X) s₂.gpr savedOffs s₂'.mem := by
    rw [mm₂, ← hb₂]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  have f₂ : Frame [⟨rb X + BitVec.ofNat 64 320, 96⟩] s₂.mem s₂'.mem := by
    rw [mm₂, ← hb₂]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  have hscr₂' : Scr s₂' X 512 := ⟨by rw [wr₂']; exact hscr₂.wr, by rw [g₂']; exact hscr₂.base⟩
  rw [storeMasks_eq]
  refine WP.mono (storeKs_ok hscr₂' (by decide) (by decide) (by decide))
    fun s₃ ⟨mk₃, fm₃, g₃, rd₃, wr₃, _⟩ => ?_
  rw [show s₂'.gpr sb = rb X by rw [g₂']; exact hb₂] at mk₃ fm₃
  refine wp_mv fun s₄ u₄ => WP.block_nil ?_
  have G : ∀ r, r ≠ .a4 → r ≠ t0 → r ≠ t1 → r ≠ sb → s₄.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h1, g₃ r h2 h3, g₂', o₂ r h4, u₁.other r h4]
  have m₀₂ : s₂.mem = s₀.mem := by rw [m₂, u₁.mem]
  -- The frame of the slots written.
  have dK : ∀ r ∈ ksRegions (rb X) (ksOf bsSlot bsMasks), ∃ r' ∈ [(⟨S, 240⟩ : Region), ⟨X, 512⟩],
      Region.Sub r r' := fun r hr => by
    simp only [ksRegions, List.mem_map] at hr
    obtain ⟨⟨k, v⟩, hk, rfl⟩ := hr
    have := bsKs_slots _ hk
    exact ⟨⟨X, 512⟩, by simp, scr512 X (d := 8 * k) (by simp only at this ⊢; omega)⟩
  have fr : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s₄.mem := by
    rw [u₄.mem]
    have f02 : Frame [⟨S, 240⟩, ⟨X, 512⟩] s₀.mem s₂'.mem := fun x hx =>
      ((f₂.sub fun r hr => ⟨⟨X, 512⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact scr512 X (by decide)⟩) x hx).trans
        (congrFun m₀₂ x)
    exact f02.trans (fm₃.sub dK)
  refine ⟨s₂.gpr, fun r hr => ?_, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [u₄.rd, rd₃, rd₂', rd₂, u₁.rd], by rw [u₄.wr, wr₃, wr₂', wr₂, u₁.wr],
    fun k hk => absurd hk (by omega_arith), ?_, ?_, fr⟩
  · have : r ≠ sb := by revert hr; revert r; decide
    rw [o₂ r this, u₁.other r this]
  · rw [G _ (by decide) (by decide) (by decide) (by decide), hP]; simp
  · rw [G _ (by decide) (by decide) (by decide) (by decide), hS]; simp
  · rw [G _ (by decide) (by decide) (by decide) (by decide), hKr]; simp
  · rw [u₄.gpr, g₃ _ (by decide) (by decide), g₂', o₂ _ (by decide), u₁.other _ (by decide), hKr]
  · rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide), g₂']; exact hb₂
  · rw [G _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₄.mem]; exact mk₃
  · rw [u₄.mem]
    refine sv₂.frame_in savedOffs_range fm₃ fun r hr => ?_
    simp only [ksRegions, List.mem_map] at hr
    obtain ⟨⟨k, v⟩, hk, rfl⟩ := hr
    have := bsKs_slots _ hk
    simp only at this ⊢
    exact Offset.disjoint (e := 8 * k) (rb X) (by omega) (by omega) (by omega)

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyRISCV64.pre s₀) :
    WP isa expandKey s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        Proof.Aes.expandKeyRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, hK⟩ := hp
  have hs : CSetup s₀ (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a0) (s₀.gpr .a1).toNat :=
    ⟨hK, by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, dKS, dKB, dSB⟩
  generalize hS : s₀.gpr .a2 = S at hs dSB
  generalize hB : s₀.gpr .a3 = X at hs dSB
  generalize hP : s₀.gpr .a0 = P at hs dKS dKB
  generalize hK' : (s₀.gpr .a1).toNat = K at hs hK dKS dKB
  have hKr : s₀.gpr .a1 = BitVec.ofNat 64 K := by rw [← hK']; simp
  have hK4 : K = 4 * (K / 4) := by omega_arith
  unfold expandKey
  refine WP.seq (WP.mono (prologue_wp hs hS hB hP hKr) fun s₁ ⟨g, hg, h₁⟩ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hs h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (wordSetup_wp hs h₂) fun s₃ wi => ?_)
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  have ws : WSetup s₀ S X (Spec.Aes.bytesAt s₀.mem P K) (K / 4) :=
    ⟨by omega_arith, by rw [hlen]; exact hK4, hs.sch, hs.scr, dSB⟩
  refine WP.seq (WP.mono (words_ok ws wi) fun s₄ h₄ => ?_)
  have hscr₄ : Scr s₄ X 512 := ⟨by rw [h₄.wr]; exact hs.scr, h₄.a5⟩
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := rb X) (align_al X) h₄.a5 savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₄.wr, by
      rw [← h₄.a5]
      exact hscr₄.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) h₄.saved)
    fun s₅ rs₅ => ?_
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    rw [rs₅.gpr_of (.inl hr')]; exact hg r hr
  · rw [rs₅.other _ not_saved_ra, h₄.ra]
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .a2) (16 * (Spec.Aes.rounds ((s₀.gpr .a1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    rw [hS, hP, hK']
    have lhs : ∀ n, Spec.Aes.bytesAt s₅.mem S n =
        (List.range n).map fun k => s₅.mem (S + BitVec.ofNat 64 k) := fun _ => rfl
    rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
      show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega_arith]
    refine flatten_expandWords ws.len (by omega_arith) _ _ fun k hk => ?_
    rw [rs₅.mem]
    exact h₄.sched k (by omega_arith)

end VG.Proof.Aes.RISCV64
