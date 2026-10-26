module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Calls
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`

`absorb_wp`: `absorb` appends the data to the message the state represents.
With `h = held count` bytes held back, if the data fit after them
(`len ≤ 8 - h`, which `absorbFlag` tests), it copies them there
(`repr_fill`); otherwise it completes the block held back with the data's
first `8 - h` bytes, chains it and the data's whole blocks but its last 1 to
8 bytes through the block function's calls, and holds those back
(`repr_chain`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)
open VG.Proof.CmacTripleDes.Stream (held nblocks)

/-- `absorb`'s precondition, with the working space of 688 bytes at `r7`. -/
structure AbsorbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r7, 688⟩]
  dataState : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r3, 416⟩
  dataScr : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r7, 688⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r7, 688⟩
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  dataFit : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  scrFit : (s.gpr .r7).toNat + 688 ≤ 2 ^ 64

/-- After `absorbSave`. -/
structure ASaved (s t : State) : Prop where
  r29 : t.gpr .r29 = s.gpr .r5
  r5 : t.gpr .r5 = s.gpr .r7
  regs : ∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = (((s.mem.writeW (s.gpr .r7 + BitVec.ofNat 64 lrOff) s.lr).writeW
    (s.gpr .r7 + BitVec.ofNat 64 r29Off) (s.gpr .r29)).writeW (s.gpr .r7 + BitVec.ofNat 64 r30Off) (s.gpr .r30)).writeW
    (s.gpr .r7 + BitVec.ofNat 64 r31Off) (s.gpr .r31)

theorem absorbSave_wp {s : State} (hp : AbsorbPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, ASaved s t → WP isa (.block is) t Q) : WP isa (.block (absorbSave ++ is)) s Q := by
  have hW : (⟨s.gpr .r7, 688⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have sl : ∀ off, off + 8 ≤ 688 → InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, hW, VG.Offset.contains_base _ h (by omega)⟩
  simp only [absorbSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact sl _ (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r29Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact sl _ (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sl _ (by decide))
    fun s₄ u₄ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sl _ (by decide)) fun s₅ u₅ => ?_
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => ?_
  have g₅ : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r h => by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  refine k s₇ ⟨?_, ?_, fun r h0 h5 h29 => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide)]
  · rw [u₇.other r h5, u₆.other r h29, g₅ r h0]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      u₁.other .r29 (by decide), u₁.other .r30 (by decide), u₁.other .r31 (by decide)]

/-- `absorbFlag`'s flag: nonzero iff the data do not fit after the bytes
held back. -/
theorem flag_eq {h len : Nat} (hh : h ≤ 8) (hl : len < 2 ^ 64) :
    ((BitVec.ofNat 64 len >>> 4 ||| (BitVec.ofNat 64 (8 - h) - BitVec.ofNat 64 len) >>> 63) != 0) =
      decide (8 - h < len) := by
  have t0 : (0 : BitVec 64).toNat = 0 := rfl
  by_cases h16 : 16 ≤ len
  · have ha : (BitVec.ofNat 64 len >>> 4).toNat ≠ 0 := by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow]
      omega
    rw [decide_eq_true (by omega)]
    simp only [bne_iff_ne, ne_eq]
    intro e
    apply ha
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, t0, Nat.or_eq_zero_iff] at this
    exact this.1
  · have lo : BitVec.ofNat 64 len >>> 4 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow]
      simp; omega
    have z : ∀ y : BitVec 64, BitVec.ofNat 64 len >>> 4 ||| y = y := fun y => by rw [lo]; ext; simp
    rw [z]
    by_cases hc : 8 - h < len
    · rw [decide_eq_true hc]
      simp only [bne_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow] at this
      simp at this
      omega
    · rw [decide_eq_false hc]
      simp only [bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp
      omega

/-- `absorbFlag`, after `heldCode`: the room left to `r9`, and the flag to
`r10`. -/
theorem flag_wp {t : State} {h len : Nat} (hh : h ≤ 8) (hl : len < 2 ^ 64)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 h) (h6 : t.gpr .r6 = BitVec.ofNat 64 len) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr .r9 = BitVec.ofNat 64 (8 - h) →
      isa.eval (.nonzero .d .r10) u = some (decide (8 - h < len)) →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → u.gpr r = t.gpr r) → u.mem = t.mem → u.rd = t.rd → u.wr = t.wr →
      WP isa (.block is) u Q) :
    WP isa (.block (absorbFlag ++ is)) t Q := by
  simp only [absorbFlag, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => wp_lsr (by decide) fun t₃ u₃ =>
    wp_sub fun t₄ u₄ => wp_lsr (by decide) fun t₅ u₅ => wp_or fun t₆ u₆ => ?_
  have r9 : t₂.gpr .r9 = BitVec.ofNat 64 (8 - h) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h8, VG.Offset.ofNat_sub_ofNat hh]
  have r6 : t₃.gpr .r6 = BitVec.ofNat 64 len := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]
  refine k t₆ (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r9])
    ?_ (fun r h9 h10 h11 => by
      rw [u₆.other r h10, u₅.other r h11, u₄.other r h11, u₃.other r h10, u₂.other r h9, u₁.other r h9])
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [eval_nonzero, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
    u₁.other _ (by decide), h6, u₅.gpr, u₄.gpr, u₃.other _ (by decide), r9, r6, flag_eq hh hl]

theorem WP.seq_seq {A B C : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq A B) s fun t => WP isa C t Q) : WP isa (.seq A (.seq B C)) s Q := by
  rw [WP.seq_iff] at h ⊢; exact WP.mono h fun _ ht => WP.seq_iff.mpr ht

/-- What the two paths (`chainPath`, `fillPath`) start from: `count`'s
bytes held back `h` in `r8`, the room left in `r9`, the data (`D`, `len`)
in `r29` and `r6`, and the working space at `W` in `r5`. -/
structure PathEnv (u : State) (S D W : Addr) (len h : Nat) : Prop where
  r3 : u.gpr .r3 = S
  r5 : u.gpr .r5 = W
  r6 : u.gpr .r6 = BitVec.ofNat 64 len
  r8 : u.gpr .r8 = BitVec.ofNat 64 h
  r9 : u.gpr .r9 = BitVec.ofNat 64 (8 - h)
  r29 : u.gpr .r29 = D
  hh : h ≤ 8
  lenLt : len < 2 ^ 64
  data : (⟨D, len⟩ : Region) ∈ u.rd
  state : (⟨S, 416⟩ : Region) ∈ u.wr
  scr : (⟨W, 688⟩ : Region) ∈ u.wr
  dataState : Region.Disjoint ⟨D, len⟩ ⟨S, 416⟩
  dataScr : Region.Disjoint ⟨D, len⟩ ⟨W, 688⟩
  stateScr : Region.Disjoint ⟨S, 416⟩ ⟨W, 688⟩
  stateFit : S.toNat + 416 ≤ 2 ^ 64
  dataFit : D.toNat + len ≤ 2 ^ 64
  scrFit : W.toNat + 688 ≤ 2 ^ 64

/-- What both paths keep. -/
structure PathOut (u : State) (S W : Addr) (v : State) : Prop where
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → v.gpr r = u.gpr r
  r5 : v.gpr .r5 = W
  rd : v.rd = u.rd
  wr : v.wr = u.wr
  frame : Frame [⟨S, 416⟩, ⟨W, 520⟩] u.mem v.mem

/-- A copy of `n` bytes from `src` to `dst`. -/
structure Copied (m : Mem) (src dst : Addr) (n : Nat) (m' : Mem) : Prop where
  copied : ∀ i < n, m' (dst + BitVec.ofNat 64 i) = m (src + BitVec.ofNat 64 i)
  rest : ∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → m' x = m x

/-- The bytes `[a, a + n)` of the state are apart from those of the data. -/
theorem state_ne_data {S D : Addr} {len : Nat} (hd : Region.Disjoint ⟨D, len⟩ ⟨S, 416⟩)
    (hD : D.toNat + len ≤ 2 ^ 64) {i j : Nat} (hi : i < len) (hj : j < 416) :
    D + BitVec.ofNat 64 i ≠ S + BitVec.ofNat 64 j := fun e =>
  hd _ (VG.Offset.contains_base _ (show i + 1 ≤ len by omega) (by omega))
    (by rw [e]; exact VG.Offset.contains_base _ (show j + 1 ≤ 416 by omega) (by omega))

/-- `toHeld n` and the copy: `count` bytes of the data at `r29` after the
`h` bytes held back. -/
theorem toHeld_copy_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) {n : Reg}
    (hn10 : n ≠ .r10) (hn11 : n ≠ .r11) {cnt : Nat} (hc : u.gpr n = BitVec.ofNat 64 cnt) (hcl : cnt ≤ len)
    (hch : h + cnt ≤ 8) {Q : State → Prop}
    (k : ∀ v, v.gpr .r10 = D + BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → v.gpr r = u.gpr r) → v.rd = u.rd → v.wr = u.wr →
      Copied u.mem D (S + BitVec.ofNat 64 (408 + h)) cnt v.mem → Q v) :
    WP isa (.seq (.block (toHeld n)) copyLoop) u Q := by
  have hh := he.hh
  have hS := he.stateFit
  have hD := he.dataFit
  refine WP.seq ?_
  simp only [toHeld, mr]
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_add fun t₂ u₂ => wp_mr fun t₃ u₃ => wp_mr fun t₄ u₄ =>
    wp_nil ?_
  have g₄ : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t₄.gpr r = u.gpr r := fun r h10 h11 h12 => by
    rw [u₄.other r h12, u₃.other r h10, u₂.other r h11, u₁.other r h11]
  have rd₄ : t₄.rd = u.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : t₄.wr = u.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₄ : t₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine copyLoop_wp (src := D) (dst := S + BitVec.ofNat 64 (408 + h)) (n := cnt) (by omega)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), he.r29])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), he.r3, he.r8,
      VG.Offset.add_add])
    (by rw [u₄.gpr, u₃.other _ hn10, u₂.other _ hn11, u₁.other _ hn11, hc])
    (fun i hi => by
      rw [rd₄, wr₄]
      exact ⟨_, List.mem_append_left _ he.data, VG.Offset.contains_base _ (show i + 1 ≤ len by omega) (by omega)⟩)
    (fun i hi => by
      rw [wr₄, VG.Offset.add_add]
      exact ⟨_, he.state, VG.Offset.contains_base _ (show 408 + h + i + 1 ≤ 416 by omega) (by omega)⟩)
    (fun i hi i' hi' => by
      rw [VG.Offset.add_add]; exact state_ne_data he.dataState hD (by omega) (by omega))
    fun v hv => ?_
  exact k v hv.r10 (fun r h0 h10 h11 h12 => by rw [hv.regs r h0 h10 h11 h12, g₄ r h10 h11 h12])
    (by rw [hv.rd, rd₄]) (by rw [hv.wr, wr₄])
    ⟨fun i hi => by rw [hv.copied i hi, m₄], fun x hx => by rw [hv.rest x hx, m₄]⟩

/-- A copy into the state keeps the rest of memory. -/
theorem Copied.frame {m m' : Mem} {src S W : Addr} {a n : Nat} (hc : Copied m src (S + BitVec.ofNat 64 a) n m')
    (ha : a + n ≤ 416) : Frame [⟨S, 416⟩, ⟨W, 520⟩] m m' := fun x hx =>
  hc.rest x fun i hi e => hx _ List.mem_cons_self (by
    rw [e, VG.Offset.add_add]; exact VG.Offset.contains_base _ (show a + i + 1 ≤ 416 by omega) (by omega))

theorem fill_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) (hf : len ≤ 8 - h) :
    WP isa fillPath u fun v => PathOut u S W v ∧ Copied u.mem D (S + BitVec.ofNat 64 (408 + h)) len v.mem := by
  have hh := he.hh
  exact toHeld_copy_wp he (by decide) (by decide) he.r6 (Nat.le_refl _) (by omega)
    fun v _ hv rd wr hc => ⟨⟨fun r hr _ _ _ => by
      obtain ⟨h0, -, -, -, -, -, -, -, h10, h11, h12⟩ := preserved_ne r hr
      exact hv r h0 h10 h11 h12, by rw [hv _ (by decide) (by decide) (by decide) (by decide), he.r5], rd, wr,
      hc.frame (by omega)⟩, hc⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE
