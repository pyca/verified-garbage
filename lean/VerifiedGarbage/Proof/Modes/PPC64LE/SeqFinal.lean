module

public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Modes.Ctr

/-!
# CFB of a message's last piece on PPC64LE, for any core

`seqFinal_wp`: `c.seqFinal M`, for a core `c` with `CoreSpec c` and a mode
`M` whose `pre` copies the chaining value to the buffer and whose
operations compute the step function `F` (`Computes`), with its arguments
in registers (`f(key = r3, iv = r4, data = r5, len = r6, scratch = r7)`),
replaces the `len / L` whole blocks of `L = 4 bw` bytes at `data` with the
outputs of `F` from the IV, XORs the `r = len % L` bytes after them with the
first bytes of `CIPH_K` of the chaining value after them, and replaces the
IV with that chaining value if `r = 0` and with its encryption otherwise; it
keeps the registers the caller expects preserved, the stack pointer and the
return address. `cfbEncFinal_wp` and `cfbDecFinal_wp` state these as CFB's
(`Spec.Cfb.EncryptFinal`, …).

The loop over segments (`seg_wp`) is `seq`'s step (`Step.lean`: `regs`,
`cont`, `cryptBuf`), with the data's area within the `len` bytes
(`FixedF`, as the whole blocks and as the partial segment, a step of `r`
bytes) and the key ready for writes within the `len` bytes and the scratch
buffer (`MidF`), the bytes left in `r30`, and the partial segment's bytes
XORed by `tailLoop_wp`.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

/-! ## The partial segment's bytes

`tailLoop_wp`: from the `r > 0` bytes at `K` (in `r8`) and `R` (in `r31`,
their count in `r30`), the loop of `tailByte` XORs each byte at `K` into the
byte at the same offset of `R`, and changes memory only there.
-/

/-- What the loop works on. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) : Prop where
  pos : 0 < r
  fitK : K.toNat + r ≤ 2 ^ 64
  fitR : R.toNat + r ≤ 2 ^ 64
  disj : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩
  rdK : ∀ q < r, InRegions (s₀.rd ++ s₀.wr) (K + BitVec.ofNat 64 q) 1
  wrR : ∀ q < r, InRegions s₀.wr (R + BitVec.ofNat 64 q) 1

/-- The loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : Addr) (r j : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = K + BitVec.ofNat 64 j
  r31 : s.gpr .r31 = R + BitVec.ofNat 64 j
  r30 : s.gpr .r30 = BitVec.ofNat 64 (r - j)
  lt : j < r
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    if q < j then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
    else s₀.mem (R + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s.gpr x = s₀.gpr x

/-- The loop, done. -/
structure XDone (s₀ : State) (K R : Addr) (r : Nat) (s : State) : Prop where
  r30 : s.gpr .r30 = 0
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s.gpr x = s₀.gpr x

theorem inRdWr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem tailByte_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) {j : Nat} {s : State}
    (hi : XInv s₀ K R r j s) :
    WP isa (.block tailByte) s fun s' => XDone s₀ K R r s' ∨
      (s'.gpr .r30 ≠ 0 ∧ XInv s₀ K R r (j + 1) s') := by
  have hj := hi.lt
  have hR := hp.fitR
  have eK : s.gpr .r8 + BitVec.ofNat 64 0 = K + BitVec.ofNat 64 j := by rw [hi.r8]; exact BitVec.add_zero _
  have eR : s.gpr .r31 + BitVec.ofNat 64 0 = R + BitVec.ofNat 64 j := by rw [hi.r31]; exact BitVec.add_zero _
  unfold tailByte
  refine wp_lbz (a := R + BitVec.ofNat 64 j) (by decide) (by decide) eR (by rw [hi.rd, hi.wr]; exact inRdWr (hp.wrR j hj)) fun s₁ u₁ => ?_
  refine wp_lbz (a := K + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact eK)
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr]; exact hp.rdK j hj) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .r31 = s.gpr .r31 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stb (a := R + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [e₃]; exact eR)
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact hp.wrR j hj) fun s₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ =>
    wp_subi (by decide) (by decide) fun s₇ u₇ => wp_nil ?_
  -- Registers.
  have g₄ : ∀ x, x ≠ .r9 → x ≠ .r10 → s₄.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₄.gpr, u₃.other x h1, u₂.other x h2, u₁.other x h1]
  have gR : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s₇.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₇.other x h4, u₆.other x h5, u₅.other x h1, g₄ x h2 h3]
  have r8₇ : s₇.gpr .r8 = K + BitVec.ofNat 64 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide), hi.r8,
      VG.Offset.add_add]
  have r31₇ : s₇.gpr .r31 = R + BitVec.ofNat 64 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.r31,
      VG.Offset.add_add]
  have r30₇ : s₇.gpr .r30 = BitVec.ofNat 64 (r - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.r30,
      ofNat_pred64 (by omega_using [hj]), Nat.sub_sub]
  -- Memory.
  have r9₃ : (s₃.gpr .r9).setWidth 8 = s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, setWidth_xor8]
  have mem₇ : s₇.mem = s.mem.writeW (R + BitVec.ofNat 64 j)
      (s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact congrArg _ r9₃
  have hRj : Region.Sub ⟨R + BitVec.ofNat 64 j, 1⟩ ⟨R, r⟩ := VG.Offset.sub_base _ (by omega_using [hj])
  have hKk : ∀ q < r, s.mem (K + BitVec.ofNat 64 q) = s₀.mem (K + BitVec.ofNat 64 q) :=
    fun q hq => hi.frame.bytes (R := ⟨K, r⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hp.disj) (by show r ≤ 2 ^ 64; omega_using [hR]) hq
  have data₇ : ∀ q < r, s₇.mem (R + BitVec.ofNat 64 q) =
      if q < j + 1 then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
      else s₀.mem (R + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₇, write1_apply]
    by_cases hqj : q = j
    · subst hqj
      rw [ite_eq_left (by rw [BitVec.sub_self]; decide), ite_eq_left (Nat.lt_succ_self _), hi.data q hq,
        ite_eq_right (Nat.lt_irrefl _), hKk q hq]
    · have hne : ¬ (R + BitVec.ofNat 64 q - (R + BitVec.ofNat 64 j)).toNat < 1 := by
        rw [VG.Offset.sub_toNat' _ (by omega_using [hR, hj]) (by omega_using [hR, hq])]
        split <;> omega_arith
      rw [ite_eq_right hne, hi.data q hq]
      by_cases h1 : q < j
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1])]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1, hqj])]
  have fr₇ : Frame [⟨R, r⟩] s₀.mem s₇.mem := by
    rw [mem₇]
    exact hi.frame.writeW List.mem_cons_self _ (hRj _ (Region.contains_self _ _) |> fun h => by
      simpa [Region.Contains] using h)
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have hz : (BitVec.ofNat 64 (r - (j + 1)) == 0) = decide (j + 1 = r) := by
    rw [ofNat_beq_zero (by omega_using [hR])]
    exact decide_eq_decide.mpr (by omega_using [hj])
  have gpr₇ : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s₇.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [gR x h1 h2 h3 h4 h5, hi.gpr x h1 h2 h3 h4 h5]
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by rw [r30₇, hdone, Nat.sub_self]; rfl, fun q hq => ?_, fr₇, rd₇, wr₇, gpr₇⟩
    rw [data₇ q hq, ite_eq_left (by omega_using [hq, hdone])]
  · refine .inr ⟨fun h => ?_, r8₇, r31₇, r30₇, by omega_using [hj, hdone], data₇, fr₇, rd₇, wr₇, gpr₇⟩
    rw [r30₇] at h
    have := congrArg (· == 0) h
    simp only [hz, decide_eq_false hdone] at this
    exact absurd this (by decide)

/-- The loop, from its first byte. -/
theorem tailLoop_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) (h0 : XInv s₀ K R r 0 s₀) :
    WP isa (.loop (.block tailByte) (.nonzero .d .r30)) s₀ (XDone s₀ K R r) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (tailByte_wp hp hj) fun s' h => ?_
  rcases h with d | ⟨z, d⟩
  · exact .inl ⟨by rw [eval_nonzero, d.r30]; rfl, d⟩
  · exact .inr ⟨by rw [eval_nonzero]; simpa using z, r - (j + 1),
      by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

/-! ## A step within the `len` bytes

`seq`'s step (`Step.lean`), with the data's area at `Dd = D + e`, `n` steps
of `st` bytes within the `len` bytes at `D` (`FixedF`: the whole blocks, and
the partial segment as one step of `r` bytes), and the key ready for writes
within the `len` bytes and the scratch buffer (`MidF`).
-/

variable {c : Core}

/-- What a run of steps keeps fixed: `Fixed`'s, with the data `n` steps of
`st` bytes at `Dd = D + e`, within the `len` bytes at `D`. -/
structure FixedF (c : Core) (s₀ : State) (B D : Addr) (len : Nat) (Dd : Addr) (n st e : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : dataRegion D 1 len ∈ s₀.wr
  dataFit : D.toNat + len ≤ 2 ^ 64
  base : Dd = D + BitVec.ofNat 64 e
  inLen : e + st * n ≤ len
  small : len < 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D 1 len) (scrRegion c B)
  step : 0 < st ∧ st ≤ 4 * c.bw
  layout : Layout c

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

/-- The data's steps, within the `len` bytes. -/
theorem FixedF.sub {s₀ : State} {B D Dd : Addr} {len n st e : Nat} (hF : FixedF c s₀ B D len Dd n st e) :
    Region.Sub (dataRegion Dd st n) (dataRegion D 1 len) := by
  have := hF.inLen
  rw [hF.base]; exact VG.Offset.sub_base _ (by omega_arith)

/-- The regions of a step, as `seq`'s (`regs`). -/
theorem FixedF.regs {s₀ : State} {B D Dd : Addr} {len n st e : Nat} (hF : FixedF c s₀ B D len Dd n st e) {j : Nat}
    (hj : j < n) : Regs c B Dd n st j := by
  have hl := hF.inLen
  have hD := hF.dataFit
  have hsm := hF.small
  have hst := hF.step
  have hn : n ≤ st * n := Nat.le_mul_of_pos_left _ hst.1
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hDd : Dd.toNat = D.toNat + e := by
    rw [hF.base, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := e) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  exact Proof.Modes.PPC64LE.regs (s₀ := { s₀ with wr := dataRegion Dd st n :: s₀.wr })
    ⟨⟨List.mem_cons_of_mem _ hF.scr.wr, hF.scr.fit⟩, List.mem_cons_self, by rw [hDd]; omega_arith,
      hF.dataScr.sub_left hF.sub, by omega_arith, hst, hF.layout⟩ hj

/-- Every byte of the areas at step `j`, as the code addresses them (`areasOk`). -/
theorem FixedF.areasOk {s₀ s : State} {B D Dd : Addr} {len n st e j : Nat} (hF : FixedF c s₀ B D len Dd n st e)
    (hj : j < n) (hb : s.gpr sb = B) (hdp : s.gpr .r31 = Dd + BitVec.ofNat 64 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st) (areas c B Dd st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  have hl := hF.inLen
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + 4 * c.bw ≤ 8 * c.slots :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hbuf
  have hW : ∀ l off w, 0 < w → off + w ≤ lens c st l →
      InRegions s.wr (areas c B Dd st j l + BitVec.ofNat 64 off) w := by
    intro l off w hw0 ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.dataW, ?_⟩
      rw [hF.base, VG.Offset.add_add, VG.Offset.add_add]
      exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by slot_omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by omega_using [hroom, hb4, ho])
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l _ off w hw0 ho => hW l off w hw0 ho,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst, hbw]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hroom, hdisp]
  · obtain ⟨r, hr, hc⟩ := hW l off w hw0 ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨Dd + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => ((hF.dataScr.sub_left hF.sub).sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_using [hdisp, hroom, hb4])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by slot_omega)
    · exact dD _ _ (by omega_using [hroom, hb4])
    · exact (dD _ _ (by slot_omega)).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hb4])).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw]

/-- The regions the function writes: the `len` bytes and the scratch buffer. -/
abbrev fws (c : Core) (B D : Addr) (len : Nat) : List Region := wrs c B D len 1

/-- A step's areas, within the regions the function writes. -/
theorem FixedF.toWs {s₀ : State} {B D Dd : Addr} {len n st e j : Nat} (hF : FixedF c s₀ B D len Dd n st e)
    (hR : Regs c B Dd n st j) :
    ∀ r ∈ areaRegions (lens c st) (areas c B Dd st j) allLocs, ∃ r' ∈ fws c B D len, Region.Sub r r' := by
  intro r hr
  obtain ⟨r', hr', hs⟩ := hR.areasW r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun x hx => hF.sub x (hs x hx)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hs⟩

/-- In the middle of a step from `s` (`Mid`, with the key ready for writes
within the `len` bytes and the scratch buffer). -/
structure MidF (cs : CoreSpec c) (s₀ : State) (B D : Addr) (len : Nat) (Dd : Addr) (st j : Nat) (k : cs.Key)
    (s : State) (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B (fws c B D len) k
  agree : Agree (lens c st) (cont (areas c B Dd st j) s'.mem) a
  frame : Frame (fine c B Dd st j) s.mem s'.mem

/-- `pre`, as `pre_wp`. -/
theorem preF_wp (cs : CoreSpec c) {M : Mode} {s₀ : State} {B D Dd : Addr} {len n st e : Nat} {k : cs.Key}
    (hF : FixedF c s₀ B D len Dd n st e) (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) {j : Nat} (hj : j < n)
    {s : State} (hb : s.gpr sb = B) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdp : s.gpr .r31 = Dd + BitVec.ofNat 64 (st * j)) (hready : cs.Ready s B (fws c B D len) k) :
    WP isa (.block (c.opsCode M.pre)) s
      (MidF cs s₀ B D len Dd st j k s (applyOps M.pre (cont (areas c B Dd st j) s.mem))) := by
  have hR := hF.regs hj
  have hA : AreasOk c s (lens c st) (areas c B Dd st j) allLocs := hF.areasOk hj hb hdp hwr
  rw [← List.append_nil (c.opsCode M.pre)]
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpre) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => wp_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact hb,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2,
    by rw [rd₂, hrd], by rw [wr₂, hwr],
    cs.ready_frame hready (fun r hr _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2) rd₂ wr₂ sy₂ f₂
      (hF.toWs hR) hR.areasCore, a₂,
    f₂.sub hR.areasFine⟩

/-- The core's `crypt`, as `crypt_step`. -/
theorem cryptF_step (cs : CoreSpec c) {s₀ : State} {B D Dd : Addr} {len n st e : Nat} {k : cs.Key}
    (hF : FixedF c s₀ B D len Dd n st e) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : MidF cs s₀ B D len Dd st j k s a s₂) :
    WP isa c.crypt s₂ (MidF cs s₀ B D len Dd st j k s (cryptBuf (4 * c.bw) (cs.cipher k) a)) := by
  have hR := hF.regs hj
  have hst := hF.step
  have hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf (4 * c.bw) (cs.cipher k) (cont (areas c B Dd st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion Dd st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst, hbw]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
  · simp only [lens] at hi
    have e := enc₃ 0 hF.layout.G_pos
    rw [blkAddr_zero] at e
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

/-- A register write that no `kept` register and no area's base sees. -/
theorem MidF.congr {cs : CoreSpec c} {s₀ s s₁ s₂ : State} {B D Dd : Addr} {len st j : Nat} {k : cs.Key}
    {a : Areas} (h : MidF cs s₀ B D len Dd st j k s a s₁) (hb : s₂.gpr sb = s₁.gpr sb)
    (hk : ∀ r ∈ Proof.Modes.PPC64LE.kept, s₂.gpr r = s₁.gpr r) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr)
    (hsy : s₂.syms = s₁.syms) : MidF cs s₀ B D len Dd st j k s a s₂ :=
  ⟨by rw [hb]; exact h.b, fun r hr => by rw [hk r hr]; exact h.kept r hr, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr,
    cs.ready_frame (rs := []) h.ready (fun r hr _ _ _ => hk r hr) hrd hwr hsy (fun x _ => by rw [hm])
      (fun _ h => nomatch h) (fun _ h => nomatch h),
    by rw [hm]; exact h.agree, by rw [hm]; exact h.frame⟩

/-! ## The segments

`seg_wp`: one segment of `seqFinal`'s loop. The whole blocks are `seq`'s
steps (with the `len / L` whole blocks as the data, `fixedW`); the partial
segment's areas are those of a step of `r = len % L` bytes at the partial
segment (`fixedT`), of which `pre` and `crypt` touch only the chaining value
and the buffer.
-/

theorem Layout.bw_pos {c : Core} (hL : Layout c) : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]

theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_ne_zero {k : Nat} (h0 : k ≠ 0) (h : k < 2 ^ 64) : BitVec.ofNat 64 k ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  exact h0 this

/-- The partial segment's address. -/
abbrev tailA (c : Core) (D : Addr) (len : Nat) : Addr := D + BitVec.ofNat 64 (4 * c.bw * (len / (4 * c.bw)))

/-- The regions a run of the loop changes. -/
abbrev fRegions (c : Core) (B D : Addr) (len : Nat) : List Region :=
  [coreRegion c B, chnRegion c B, dataRegion D 1 len]

/-- What the loop keeps fixed: the scratch buffer at `B` and the `len` bytes
at `D`. -/
structure FPre (c : Core) (s₀ : State) (B D : Addr) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : dataRegion D 1 len ∈ s₀.wr
  dataFit : D.toNat + len ≤ 2 ^ 64
  small : len < 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D 1 len) (scrRegion c B)
  layout : Layout c

/-- The whole blocks, as `seq`'s data. -/
theorem FPre.fixedW {s₀ : State} {B D : Addr} {len : Nat} (hp : FPre c s₀ B D len) :
    FixedF c s₀ B D len D (len / (4 * c.bw)) (4 * c.bw) 0 := by
  have hle : 4 * c.bw * (len / (4 * c.bw)) ≤ len := Nat.mul_div_le len _
  have hbw := hp.layout.bw_pos
  exact ⟨hp.scr, hp.dataW, hp.dataFit, (BitVec.add_zero _).symm, by omega_using [hle], hp.small, hp.dataScr,
    ⟨by omega_using [hbw], Nat.le_refl _⟩, hp.layout⟩

/-- The partial segment, as a step of `len % L` bytes. -/
theorem FPre.fixedT {s₀ : State} {B D : Addr} {len : Nat} (hp : FPre c s₀ B D len) (hr : 0 < len % (4 * c.bw)) :
    FixedF c s₀ B D len (tailA c D len) 1 (len % (4 * c.bw)) (4 * c.bw * (len / (4 * c.bw))) := by
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hmlt : len % (4 * c.bw) < 4 * c.bw := Nat.mod_lt _ (by have := hp.layout.bw_pos; omega_using [this])
  exact ⟨hp.scr, hp.dataW, hp.dataFit, rfl, by omega_using [hdm], hp.small, hp.dataScr, ⟨hr, Nat.le_of_lt hmlt⟩,
    hp.layout⟩

/-- The loop, before segment `j`, from the chaining value `c0`, the whole
blocks `xs` and the partial segment `tl` on entry, in `s₀`. -/
structure FInv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (len : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (tl : List Byte) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.gpr .r31 = D + BitVec.ofNat 64 (4 * c.bw * j)
  np : s.gpr .r30 = BitVec.ofNat 64 (len - 4 * c.bw * j)
  lt : 4 * c.bw * j < len
  ready : cs.Ready s B (fws c B D len) k
  data : chunksAt (4 * c.bw) s.mem D (len / (4 * c.bw)) = (run F c0 (xs.take j)).1 ++ xs.drop j
  tail : bytesAt s.mem (tailA c D len) (len % (4 * c.bw)) = tl
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (fRegions c B D len) s₀.mem s.mem

/-- The loop, done. -/
structure FDone (cs : CoreSpec c) (s₀ : State) (B D : Addr) (len : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (tl : List Byte) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : chunksAt (4 * c.bw) s.mem D (len / (4 * c.bw)) = (run F c0 xs).1
  tail : bytesAt s.mem (tailA c D len) (len % (4 * c.bw)) = Spec.Cbc.xor tl (cs.cipher k (run F c0 xs).2)
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) =
    if len % (4 * c.bw) = 0 then (run F c0 xs).2 else cs.cipher k (run F c0 xs).2
  frame : Frame (fRegions c B D len) s₀.mem s.mem

/-- Input block `j`, from the invariant. -/
theorem FInv.input {cs : CoreSpec c} {s₀ : State} {B D : Addr} {len : Nat} {k : cs.Key} {F : StepFn}
    {c0 tl : List Byte} {xs : List (List Byte)} {j : Nat} {s : State} (hI : FInv cs s₀ B D len k F c0 xs tl j s)
    (hxs : xs.length = len / (4 * c.bw)) (hj : j < len / (4 * c.bw)) :
    bytesAt s.mem (D + BitVec.ofNat 64 (4 * c.bw * j)) (4 * c.bw) = xs[j]'(by omega_using [hxs, hj]) := by
  have hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  have e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

/-- The partial segment is apart from what a whole segment changes. -/
theorem tail_out {s₀ : State} {B D : Addr} {len : Nat} (hp : FPre c s₀ B D len) {j : Nat}
    (hjl : 4 * c.bw * j + 4 * c.bw ≤ 4 * c.bw * (len / (4 * c.bw))) :
    ∀ r ∈ fine c B D (4 * c.bw) j, Region.Disjoint ⟨tailA c D len, len % (4 * c.bw)⟩ r := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbw := bw_le hL
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have sT : Region.Sub ⟨tailA c D len, len % (4 * c.bw)⟩ (dataRegion D 1 len) :=
    VG.Offset.sub_base _ (by omega_using [hdm])
  have dS : ∀ {r : Region}, Region.Sub r (scrRegion c B) → Region.Disjoint ⟨tailA c D len, len % (4 * c.bw)⟩ r :=
    fun h => (hp.dataScr.sub_left sT).sub_right h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Offset.disjoint D (d := 4 * c.bw * (len / (4 * c.bw))) (n := len % (4 * c.bw))
      (e := 4 * c.bw * j) (k := 4 * c.bw) (.inr hjl) (by omega_using [hD, hdm]) (by omega_using [hD, hdm, hjl])
  · exact dS (Region.sub_prefix (by omega_arith))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))

/-- What a step changes, within the loop's regions. -/
theorem fine_big {s₀ : State} {B D Dd : Addr} {len n st e : Nat} (hF : FixedF c s₀ B D len Dd n st e) {j : Nat}
    (hj : j < n) : ∀ r ∈ fine c B Dd st j, ∃ r' ∈ fRegions c B D len, Region.Sub r r' := by
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, m2, fun x hx => hF.sub x (VG.Offset.sub_base _ hjn x hx)⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, m1, fun _ h => h⟩

theorem xor_nil (y : List Byte) : Spec.Cbc.xor [] y = [] := rfl

/-- A whole segment's `post`, and on. -/
theorem whole_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len) (hM : M.step = 4 * c.bw)
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c (4 * c.bw))) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hxs : xs.length = len / (4 * c.bw)) (htl : tl.length = len % (4 * c.bw)) {j : Nat}
    (hjl : 4 * c.bw * j + 4 * c.bw ≤ len) {s s₃ : State} (hI : FInv cs s₀ B D len k F c0 xs tl j s)
    (hm : MidF cs s₀ B D len D (4 * c.bw) j k s (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps M.pre (cont (areas c B D (4 * c.bw) j) s.mem))) s₃)
    (hdp : s₃.gpr .r31 = D + BitVec.ofNat 64 (4 * c.bw * j))
    (hnp : s₃.gpr .r30 = BitVec.ofNat 64 (len - 4 * c.bw * j)) :
    WP isa (.block (c.opsCode M.post ++ c.advanceBytes)) s₃ fun s' =>
      (s'.gpr .r30 = 0 ∧ FDone cs s₀ B D len k F c0 xs tl s') ∨
        (s'.gpr .r30 ≠ 0 ∧ FInv cs s₀ B D len k F c0 xs tl (j + 1) s') := by
  have hF := hp.fixedW
  have hL := hF.layout
  have hbw := bw_le hL
  have hbw0 := hL.bw_pos
  have hDf := hp.dataFit
  have hsm := hp.small
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hj1 : 4 * c.bw * (j + 1) = 4 * c.bw * j + 4 * c.bw := Nat.mul_succ _ _
  have hjn : j < len / (4 * c.bw) :=
    (Nat.le_div_iff_mul_le (by omega_using [hbw0])).mpr (by rw [Nat.mul_comm]; omega_using [hjl, hj1])
  have hjW : 4 * c.bw * j + 4 * c.bw ≤ 4 * c.bw * (len / (4 * c.bw)) := by
    rw [← hj1]; exact Nat.mul_le_mul_left _ hjn
  have hR := hF.regs hjn
  have hA : AreasOk c s₃ (lens c (4 * c.bw)) (areas c B D (4 * c.bw) j) allLocs := hF.areasOk hjn hm.b hdp hm.wr
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpost) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_)
  unfold Core.advanceBytes
  refine wp_addi (by decide) (by omega_using [hbw]) fun s₆ u₆ =>
    wp_subi (by decide) (by omega_using [hbw]) fun s₇ u₇ => wp_nil fun sy₇ => ?_
  have g₇ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r30 → r ≠ .r31 → s₇.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other r h3, u₆.other r h4, g₅ r h1 h2]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  have r31₅ : s₅.gpr .r31 = D + BitVec.ofNat 64 (4 * c.bw * j) := by rw [g₅ _ (by decide) (by decide), hdp]
  have r30₅ : s₅.gpr .r30 = BitVec.ofNat 64 (len - 4 * c.bw * j) := by rw [g₅ _ (by decide) (by decide), hnp]
  have r31₇ : s₇.gpr .r31 = D + BitVec.ofNat 64 (4 * c.bw * (j + 1)) := by
    rw [u₇.other _ (by decide), u₆.gpr, r31₅, VG.Offset.add_add, hj1]
  have r30₇ : s₇.gpr .r30 = BitVec.ofNat 64 (len - 4 * c.bw * (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), r30₅, ofNat_sub64 (by omega_using [hjl]) (by omega_using [hsm])]
    exact congrArg _ (by omega_using [hj1])
  -- The step's outputs.
  let A := areas c B D (4 * c.bw) j
  have hstep : Agree (lens c (4 * c.bw)) (cont A s₅.mem) (stepA M (4 * c.bw) (cs.cipher k) (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  have xj : rd (cont A s.mem) .dat (4 * c.bw) = xs[j]'(by omega_using [hxs, hjn]) := hI.input hxs hjn
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  have out₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (4 * c.bw * j)) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  have chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  have all : Frame (fine c B D (4 * c.bw) j) s.mem s₅.mem := hm.frame.trans (f₅.sub hR.areasFine)
  have hrun : run F c0 (xs.take (j + 1)) =
      ((run F c0 (xs.take j)).1 ++ [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).1],
        (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hjn]), Option.toList_some, run_snoc]
  have data₇ : chunksAt (4 * c.bw) s₇.mem D (len / (4 * c.bw)) =
      (run F c0 (xs.take (j + 1))).1 ++ xs.drop (j + 1) := by
    rw [m₇, chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₅, run_set F c0 (by omega_using [hxs, hjn])]
    refine all _ fun r hr hcon => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Region.Contains] at hcon
      have e := (VG.Offset.lt_iff (D + BitVec.ofNat 64 i) D (d := 4 * c.bw * j) (n := 4 * c.bw)
        (by omega_using [hDf, hjW, hdm])).mp (by omega_using [hcon])
      rw [sub_self_add _ (by omega_using [hDf, hi, hdm])] at e
      omega_using [hout, e]
    · exact hR.dataCore _ (contains_area hi (by omega_using [hDf, hdm])) hcon
    · exact hR.dataChn _ (contains_area hi (by omega_using [hDf, hdm])) hcon
  have tail₇ : bytesAt s₇.mem (tailA c D len) (len % (4 * c.bw)) = tl := by
    rw [← hI.tail, m₇]
    exact List.map_congr_left fun i hi => all.bytes (tail_out hp hjW)
      (by show len % (4 * c.bw) ≤ 2 ^ 64; omega_using [hDf, hdm]) (List.mem_range.mp hi)
  have fr₇ : Frame (fRegions c B D len) s₀.mem s₇.mem := by
    rw [m₇]; exact hI.frame.trans (all.sub (fine_big hF hjn))
  have kp₇ : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s₇.gpr r = s₀.gpr r := fun r hr h30 h31 => by
    rw [g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31, hm.kept r hr, hI.keep r hr h30 h31]
  have b₇ : s₇.gpr sb = B := by rw [g₇ _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, rd₅, hm.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅, hm.wr]
  by_cases hdone : 4 * c.bw * (j + 1) = len
  · have hW : len / (4 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ (by omega_using [hbw0])
    have hr : len % (4 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
    have htk : xs.take (j + 1) = xs := List.take_of_length_le (by omega_using [hxs, hW])
    refine .inl ⟨by rw [r30₇, ← hdone, Nat.sub_self]; rfl, b₇, kp₇, rd₇, wr₇, ?_, ?_, ?_, fr₇⟩
    · rw [data₇, htk, List.drop_of_length_le (by omega_using [hxs, hW]), List.append_nil]
    · rw [tail₇, List.eq_nil_of_length_eq_zero (htl.trans hr), xor_nil]
    · rw [ite_eq_left hr, m₇, chn₅]
      exact (congrArg Prod.snd hrun).symm.trans (congrArg (fun t => (run F c0 t).2) htk)
  · refine .inr ⟨by rw [r30₇]; exact ofNat_ne_zero (by omega_using [hjl, hj1, hdone]) (by omega_using [hsm]),
      b₇, kp₇, rd₇, wr₇, r31₇, r30₇, by omega_using [hjl, hj1, hdone], ?_, data₇, tail₇, by rw [m₇, chn₅, hrun],
      fr₇⟩
    exact cs.ready_frame hm.ready (fun r hr _ h30 h31 => g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31)
      (by rw [u₇.rd, u₆.rd, rd₅]) (by rw [u₇.wr, u₆.wr, wr₅]) sy₇ (by rw [m₇]; exact f₅) (hF.toWs hR)
      hR.areasCore

/-! ## The partial segment -/

/-- The areas after the partial segment's `pre` (`copyBlk .buf .chn`),
`crypt` and the copy of the buffer to the chaining value. -/
theorem part_vals (bw : Nat) (ciph : Spec.Cbc.Cipher) (a : Areas) (i : Nat) :
    applyOps (copyBlk bw .chn .buf) (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a)) .dat i =
        a .dat i ∧
      applyOps (copyBlk bw .chn .buf) (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a)) .buf i =
        (ciph (rd a .chn (4 * bw))).getD i 0 ∧
      (i < 4 * bw → applyOps (copyBlk bw .chn .buf) (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a))
        .chn i = (ciph (rd a .chn (4 * bw))).getD i 0) := by
  have hb : rd (applyOps (copyBlk bw .buf .chn) a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    List.map_congr_left fun i hi => by rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, List.mem_range.mp hi⟩]
  refine ⟨?_, ?_, fun hi => ?_⟩
  · rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1)]
    simp only [cryptBuf, ite_eq_right (show Loc.dat ≠ Loc.buf by decide)]
    rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1)]
  · rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1)]
    simp only [cryptBuf, ite_true, hb]
  · rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]

theorem cont_dat0 (c : Core) (B Dt : Addr) (rr : Nat) (m : Mem) (q : Nat) :
    cont (areas c B Dt rr 0) m .dat q = m (Dt + BitVec.ofNat 64 q) := by
  simp only [cont, areas, Nat.mul_zero, BitVec.add_zero]

theorem toNat_add_ofNat64 {B : Addr} {d : Nat} (h : B.toNat + d < 2 ^ 64) :
    (B + BitVec.ofNat 64 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The partial segment's step region, at its address. -/
theorem datRegion_zero (D : Addr) (r : Nat) : datRegion D r 0 = ⟨D, r⟩ := by
  simp only [datRegion, Nat.mul_zero]
  exact congrArg (Region.mk · r) (BitVec.add_zero _)

/-- The whole blocks are apart from what the partial segment changes. -/
theorem whole_out {s₀ : State} {B D : Addr} {len : Nat} (hp : FPre c s₀ B D len) :
    ∀ r ∈ fine c B (tailA c D len) (len % (4 * c.bw)) 0,
      Region.Disjoint (dataRegion D (4 * c.bw) (len / (4 * c.bw))) r := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbw := bw_le hL
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have sW : Region.Sub (dataRegion D (4 * c.bw) (len / (4 * c.bw))) (dataRegion D 1 len) :=
    Region.sub_prefix (by omega_using [hdm])
  have dS : ∀ {r : Region}, Region.Sub r (scrRegion c B) →
      Region.Disjoint (dataRegion D (4 * c.bw) (len / (4 * c.bw))) r := fun h => (hp.dataScr.sub_left sW).sub_right h
  intro r hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · rw [datRegion_zero]
    exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hD, hdm])
  · exact dS (Region.sub_prefix (by omega_arith))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))

theorem r10_notKept : ∀ r ∈ kept, r ≠ .r10 := by decide

/-- The partial segment, after `crypt` and `segTest`: the buffer to the
chaining value, and its first bytes XORed into the data. -/
theorem part_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len)
    (hpre : M.pre = copyBlk c.bw .buf .chn) (hxs : xs.length = len / (4 * c.bw)) (htl : tl.length = len % (4 * c.bw))
    (hr : 0 < len % (4 * c.bw)) {s s₃ : State} (hI : FInv cs s₀ B D len k F c0 xs tl (len / (4 * c.bw)) s)
    (hm : MidF cs s₀ B D len (tailA c D len) (len % (4 * c.bw)) 0 k s
      (cryptBuf (4 * c.bw) (cs.cipher k) (applyOps M.pre (cont (areas c B (tailA c D len) (len % (4 * c.bw)) 0)
        s.mem))) s₃)
    (hdp : s₃.gpr .r31 = tailA c D len) (hnp : s₃.gpr .r30 = BitVec.ofNat 64 (len % (4 * c.bw))) :
    WP isa c.tailCode s₃ fun s' => s'.gpr .r30 = 0 ∧ FDone cs s₀ B D len k F c0 xs tl s' := by
  have hT := hp.fixedT hr
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hbw := bw_le hL
  have hbw0 := hL.bw_pos
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have hmlt : len % (4 * c.bw) < 4 * c.bw := Nat.mod_lt _ (by omega_using [hbw0])
  have hWO := whole_out hp
  have hFB := fine_big hT (j := 0) (by decide)
  have tDt : (tailA c D len).toNat = D.toNat + 4 * c.bw * (len / (4 * c.bw)) :=
    toNat_add_ofNat64 (by omega_using [hD, hdm, hr])
  rw [hpre] at hm
  generalize hDt : tailA c D len = Dt at hm hdp hT hWO hFB tDt
  generalize hrr : len % (4 * c.bw) = rr at hm hnp hT hr hmlt htl hWO hFB
  have hR := hT.regs (j := 0) (by decide)
  let A := areas c B Dt rr 0
  have hA : AreasOk c s₃ (lens c rr) A allLocs :=
    hT.areasOk (by decide) hm.b (by rw [hdp, Nat.mul_zero]; exact (BitVec.add_zero _).symm) hm.wr
  have hcIB : ∀ o ∈ copyBlk c.bw .chn .buf, o.InBounds (lens c rr) :=
    copyBlk_inBounds (by simp [lens]) (by simp [lens])
  unfold Core.tailCode
  refine WP.seq (opsCode_wp c (fun o ho => ⟨hcIB o ho, mem_allLocs _⟩) hA fun s₄ a₄ f₄ g₄ rd₄ wr₄ => ?_)
  refine wp_addi (by decide) (by omega_using [hdisp, hroom, hbuf]) fun s₅ u₅ => wp_nil ?_
  -- The areas after the copy.
  have hY : Agree (lens c rr) (cont A s₄.mem) (applyOps (copyBlk c.bw .chn .buf) (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps (copyBlk c.bw .buf .chn) (cont A s.mem)))) :=
    Agree.trans a₄ (applyOps_agree hcIB hm.agree)
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 xs).2 := by
    have e := hI.chn
    rw [List.take_of_length_le (Nat.le_of_eq hxs)] at e
    exact e
  have tK : (slotA B c.buf).toNat = B.toNat + 8 * c.buf := toNat_add_ofNat64 (by omega_arith)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  have g₅ : ∀ x, x ≠ .r8 → x ≠ .r9 → s₅.gpr x = s₃.gpr x := fun x h1 h2 => by
    rw [u₅.other x h1, g₄ x h1 h2]
  have b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide) (by decide)]; exact hm.b
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, rd₄, hm.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, wr₄, hm.wr]
  have eDt : Dt = D + BitVec.ofNat 64 (4 * c.bw * (len / (4 * c.bw))) := hDt.symm
  have sT : Region.Sub ⟨Dt, rr⟩ (dataRegion D 1 len) := by
    rw [eDt]; exact VG.Offset.sub_base _ (by omega_using [hdm, hrr])
  have hxp : XPre s₅ (slotA B c.buf) Dt rr :=
    { pos := hr
      fitK := by rw [tK]; omega_arith
      fitR := by rw [tDt]; omega_using [hD, hdm, hrr]
      disj := ((hp.dataScr.sub_left sT).sub_right (VG.Offset.sub_base _ (by omega_arith))).symm
      rdK := fun q hq => by
        rw [rd₅, wr₅]
        exact ⟨_, List.mem_append_right _ hp.scr.wr, by
          rw [VG.Offset.add_add]; exact slot_contains hdisp (by omega_arith)⟩
      wrR := fun q hq => by
        rw [eDt, wr₅]
        refine ⟨_, hp.dataW, ?_⟩
        rw [VG.Offset.add_add]
        exact VG.Offset.contains_base _ (by omega_using [hdm, hrr, hq]) (by omega_using [hD, hdm, hrr, hq]) }
  have hx0 : XInv s₅ (slotA B c.buf) Dt rr 0 s₅ :=
    { r8 := by rw [u₅.gpr, g₄ _ (by decide) (by decide), hm.b]; exact (BitVec.add_zero _).symm
      r31 := by rw [g₅ _ (by decide) (by decide), hdp]; exact (BitVec.add_zero _).symm
      r30 := by rw [g₅ _ (by decide) (by decide), hnp, Nat.sub_zero]
      lt := hr
      data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero _)]
      frame := Frame.refl _ _
      rd := rfl
      wr := rfl
      gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (tailLoop_wp hxp hx0) fun s₇ d₇ => ?_
  -- What the segment changed.
  have f₇ : Frame [⟨Dt, rr⟩] s₄.mem s₇.mem := by rw [← m₅]; exact d₇.frame
  have allP : Frame (fine c B Dt rr 0) s.mem s₇.mem :=
    (hm.frame.trans (f₄.sub hR.areasFine)).trans (f₇.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by rw [datRegion_zero]; exact fun _ h => h⟩)
  -- The buffer and the chaining value.
  have chnDat : Region.Disjoint (chnRegion c B) (datRegion Dt rr 0) := hA.apart .chn .dat (by decide)
  rw [datRegion_zero] at chnDat
  -- The bytes after the copy.
  have hdat : ∀ q < rr, s₄.mem (Dt + BitVec.ofNat 64 q) = tl.getD q 0 := fun q hq => by
    rw [← cont_dat0 c B Dt rr s₄.mem q, hY .dat q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).1,
      cont_dat0, ← hDt, ← bytesAt_getD s.mem _ (show q < len % (4 * c.bw) by rw [hrr]; exact hq), hI.tail]
  have hbuf' : ∀ q < 4 * c.bw, s₄.mem (slotA B c.buf + BitVec.ofNat 64 q) = (cs.cipher k (run F c0 xs).2).getD q 0 :=
    fun q hq => by
      show cont A s₄.mem .buf q = _
      rw [hY .buf q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).2.1, cj]
  have hchn : ∀ q < 4 * c.bw, s₄.mem (slotA B c.chnSlot + BitVec.ofNat 64 q) =
      (cs.cipher k (run F c0 xs).2).getD q 0 := fun q hq => by
    show cont A s₄.mem .chn q = _
    rw [hY .chn q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).2.2 hq, cj]
  have hcl := cs.cipher_len k (run F c0 xs).2
  refine ⟨d₇.r30, ⟨?_, fun r hr h30 h31 => ?_, by rw [d₇.rd, rd₅], by rw [d₇.wr, wr₅], ?_, ?_, ?_,
    hI.frame.trans (allP.sub hFB)⟩⟩
  · rw [d₇.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact b₅
  · rw [d₇.gpr r (kept_ne r hr).1 (kept_ne r hr).2 (r10_notKept r hr) h30 h31, g₅ r (kept_ne r hr).1 (kept_ne r hr).2,
      hm.kept r hr, hI.keep r hr h30 h31]
  · rw [chunksAt_frame allP hWO (by omega_using [hD, hdm]), hI.data, List.take_of_length_le (Nat.le_of_eq hxs),
      List.drop_of_length_le (Nat.le_of_eq hxs), List.append_nil]
  · rw [hDt, hrr]
    apply List.ext_getElem (by simp only [bytesAt_length, Spec.Cbc.xor, List.length_zipWith, hcl, htl]; omega_arith)
    intro q h1 _
    have hq : q < rr := by rw [bytesAt_length] at h1; exact h1
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, getD_xor (by omega_using [htl, hrr, hq])
      (by rw [hcl]; omega_using [hq, hmlt]), bytesAt_getD _ _ hq, d₇.data q hq, m₅,
      hdat q hq, hbuf' q (by omega_using [hq, hmlt])]
  · rw [ite_eq_right (by rw [hrr]; omega_using [hr])]
    apply List.ext_getElem (by rw [bytesAt_length, hcl])
    intro q h1 _
    have hq : q < 4 * c.bw := by rw [bytesAt_length] at h1; exact h1
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, bytesAt_getD _ _ hq]
    refine (f₇.bytes (R := chnRegion c B) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact chnDat)
      (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hq).trans (hchn q hq)

end VG.Proof.Modes.PPC64LE
