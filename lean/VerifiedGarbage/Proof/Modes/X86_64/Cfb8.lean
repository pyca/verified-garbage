import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Loop
import VerifiedGarbage.Proof.Modes.X86_64.Fb

/-!
# CFB8 on x86-64, for any core: the whole function

`cfb8_wp`: `c.cfb8 enc r`, for a core `c` with `BlockSpec c` whose cipher
is the forward cipher `CIPH_K`, and its arguments in the registers `r`,
replaces the `n` bytes at `D` with CFB8's output (`cfb8Out`) under the key
`k` that its key arguments give, from the input block at `P`, and that
block with the input block after the last byte (`cfb8In`); it keeps the
callee-saved registers, and writes nothing but the scratch buffer, the data
and the input block. `cfb8Enc_of` and `cfb8Dec_of` (`Proof/Modes/Cfb8.lean`)
state these as the specification's.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cfb8_wp (cs : BlockSpec c) (enc : Bool) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩) (sDS : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩) (fitD : D.toNat + n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩] k) (hsc : KeepsIv c.prepare ∧ KeepsIv c.crypt) :
    WP isa (c.cfb8 enc r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      bytesAt s'.mem D n = (List.range n).map (cfb8Out enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = cfb8In enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega
  have hn64 : n < 2 ^ 64 := by rw [← hn]; exact BitVec.isLt _
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, dbp, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, lbp, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega)⟩
  have slotIn : ∀ i < 7, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have slotCore : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega) (by omega)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movqX_ok sE Core.ivX r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.cfb8
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  have gA' : ∀ x, x ≠ sb → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gA x h2 h3, gS, gE x h1]
  have bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS, bE]
  have rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  have wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  have fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  let sv : Nat → BitVec 64 := fun i => s₀.gpr (Core.savedRegs.getD i .rbx)
  have svA : ∀ i < 6, sA.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mA, mS, svE i hi]
  have xA : sA.xmm Core.ivX = (0 : BitVec 64) ++ P := by
    rw [runBlock_vec rfl eA, xS, gE _ hr.ctr.1, hP]
  have kr := keyRegs_ne cs.keyRegs_ok
  have hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (kr x hx).1 (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA' fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepIv hsc.1 (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩ List.mem_cons_self hkA))
    fun s₄ ⟨⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, x₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  -- Any bytes?
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₄ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
  have mem₅ : s₅.mem = s₄.mem := m₅
  have b₅ : s₅.gpr sb = B := by rw [g₅, b₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [g₅, rsp₄, gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by rw [g₅, lr₄, lrA, gS, gE _ hr.n.1]
  have hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have sv₅ : ∀ i < 6, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mem₅, ← svA i hi]
    exact f₄.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact slotCore i (by omega)) (by decide)
  have x₅ : s₅.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₅, x₄, xA]
  have dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  have dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, 8 * c.bw⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  have m₅P : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₅, f₄.bytes (R := ⟨P, 8 * c.bw⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega) hu]
    exact fA.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have m₅D : ∀ q < n, s₅.mem (D + BitVec.ofNat 64 q) = s₀.mem (D + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₅, f₄.bytes (R := ⟨D, n⟩) dDcore (show n ≤ 2 ^ 64 by omega) hq]
    exact fA.bytes (R := ⟨D, n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      (show n ≤ 2 ^ 64 by omega) hq
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : C8Pre c s₅ B D P n := ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD,
    by rw [wr₅']; exact hwP, sDS, sPS, sPD, fitD, hn64, x₅⟩
  have fr₅ : Frame [S] s₀.mem s₅.mem :=
    fA.trans (by rw [mem₅]; exact f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩)
  -- The bytes.
  refine WP.seq (WP.mono (M := isa) (Q := C8Done cs enc s₅ s₀.mem B D P n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun u hu => by rw [hn0, m₅P u hu]; simp [cfb8In, iv, bytesAt, hu],
      fun q hq => by omega, Frame.refl _ _, rfl, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cfb8Loop_wp cs enc hiv hp hsc.2 ⟨b₅, rfl, cs.ready_frame ready₄ (by rw [mem₅]; exact Frame.refl [] _)
        (fun _ h => by simp at h) (fun r _ => by rw [g₅]), fun _ _ => rfl, ?_, ?_, by omega,
      fun u hu => by rw [m₅P u hu]; simp [cfb8In, iv, bytesAt, hu], fun q hq => ?_, Frame.refl _ _, rfl, rfl, rfl⟩
    · rw [g₅, dr₄, drA, gS, gE _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₅D q hq
  -- The exit.
  have hsv7 : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [d₆.saved i (by omega), sv₅ i hi]
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₆
    d₆.base hsv hinj (fun i hi' => by
      rw [rd₆, wr₆]
      exact inRd (inS (by simp only [Core.ctrSlots]; omega)))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, rd₆], by rw [wr₈, wr₆]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', hsv7 i (by omega)]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₈]
    apply List.ext_getElem (by simp [bytesAt])
    intro q h1 _
    have hq : q < n := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact d₆.data q hq
  · rw [m₈]
    apply List.ext_getElem (by
      rw [cfb8In_length (iv := bytesAt s₀.mem P (8 * c.bw)) enc _ _ _ (by simp [bytesAt]) hL0]; simp [bytesAt])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [d₆.ivB u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    exact (fr₅.mono fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      d₆.frame

end VG.Proof.Modes.X86_64
