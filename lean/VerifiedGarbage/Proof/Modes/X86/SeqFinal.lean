module
-- separate module: the final modes over every 32-bit x86 core, which each cipher's final functions import

public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Proof.Modes.X86.Seq
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# OFB and CFB of a message's last piece on x86 (32-bit), for any core

`seqFinal_wp`: `c.seqFinal M`, for a core `c` with `CoreSpec c` and a mode
`M` whose `pre` copies the chaining value to the buffer and whose
operations compute the step function `F` (`Computes`), with its arguments
on the stack (`f(key, iv, data, len, scratch)`), replaces the `len / L`
whole blocks of `L = 4 bw` bytes at `data` with the outputs of `F` from the
IV, XORs the `r = len % L` bytes after them with the first bytes of
`CIPH_K` of the chaining value after them, and replaces the IV with that
chaining value if `r = 0` and with its encryption otherwise; it keeps the
callee-saved registers and the return address. `cfbEncFinal_wp` and
`cfbDecFinal_wp` state these as CFB's (`Spec.Cfb.EncryptFinal`, …).

The loop over segments (`seg_wp`) is `seq`'s step (`Step.lean`: `regs`,
`areasOk`, `crypt_step`), the bytes left in `nSlot`, with the partial
segment's areas those of a step of `r` bytes at the partial segment
(`fixedT`), and its bytes XORed by `tailLoop_wp`.
-/

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

/-! ## The partial segment's bytes

`tailLoop_wp`: from the `r > 0` bytes at `K` (in `ebx`) and `R` (in `esi`,
their count in `ebp`), the loop of `tailByte` XORs each byte at `K` into
the byte at the same offset of `R`, and changes memory only there.
-/

/-- What the loop works on. -/
structure XPre (s₀ : State) (K R : BitVec 32) (r : Nat) : Prop where
  pos : 0 < r
  fitK : K.toNat + r ≤ 2 ^ 32
  fitR : R.toNat + r ≤ 2 ^ 32
  disj : Region.Disjoint ⟨K.setWidth 64, r⟩ ⟨R.setWidth 64, r⟩
  rdK : ∀ q < r, InRegions (s₀.rd ++ s₀.wr) (K.setWidth 64 + BitVec.ofNat 64 q) 1
  wrR : ∀ q < r, InRegions s₀.wr (R.setWidth 64 + BitVec.ofNat 64 q) 1

/-- The loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : BitVec 32) (r j : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = K + BitVec.ofNat 32 j
  esi : s.gpr .esi = R + BitVec.ofNat 32 j
  ebp : s.gpr .ebp = BitVec.ofNat 32 (r - j)
  lt : j < r
  data : ∀ q < r, s.mem (R.setWidth 64 + BitVec.ofNat 64 q) =
    if q < j then s₀.mem (R.setWidth 64 + BitVec.ofNat 64 q) ^^^ s₀.mem (K.setWidth 64 + BitVec.ofNat 64 q)
    else s₀.mem (R.setWidth 64 + BitVec.ofNat 64 q)
  frame : Frame [⟨R.setWidth 64, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  gpr : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .ebx → x ≠ .esi → x ≠ .ebp → s.gpr x = s₀.gpr x

/-- The loop, done. -/
structure XDone (s₀ : State) (K R : BitVec 32) (r : Nat) (s : State) : Prop where
  zf : s.zf = some true
  data : ∀ q < r, s.mem (R.setWidth 64 + BitVec.ofNat 64 q) =
    s₀.mem (R.setWidth 64 + BitVec.ofNat 64 q) ^^^ s₀.mem (K.setWidth 64 + BitVec.ofNat 64 q)
  frame : Frame [⟨R.setWidth 64, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  gpr : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .ebx → x ≠ .esi → x ≠ .ebp → s.gpr x = s₀.gpr x

/-- `[K + j]`, as the code addresses it. -/
theorem addr_off {K : BitVec 32} {j : Nat} (h : K.toNat + j < 2 ^ 32) :
    addr (K + BitVec.ofNat 32 j) 0 = K.setWidth 64 + BitVec.ofNat 64 j := by
  have hK := K.isLt
  have e : (K + BitVec.ofNat 32 j).toNat = K.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [h]), Nat.mod_eq_of_lt h]
  rw [addr_eq (by rw [e]; omega_using [h]), BitVec.add_zero]
  exact addr_eq h

theorem inRdWr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ofNat_add_one (K : BitVec 32) (j : Nat) :
    K + BitVec.ofNat 32 j + 1 = K + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem tailByte_wp {s₀ : State} {K R : BitVec 32} {r : Nat} (hp : XPre s₀ K R r) {j : Nat} {s : State}
    (hi : XInv s₀ K R r j s) :
    WP isa (.block tailByte) s fun s' => XDone s₀ K R r s' ∨
      (s'.zf = some false ∧ XInv s₀ K R r (j + 1) s') := by
  have hj := hi.lt
  have hK := hp.fitK
  have hR := hp.fitR
  have eK : addr (s.gpr .ebx) 0 = K.setWidth 64 + BitVec.ofNat 64 j := by
    rw [hi.ebx]; exact addr_off (by omega_using [hK, hj])
  have eR : addr (s.gpr .esi) 0 = R.setWidth 64 + BitVec.ofNat 64 j := by
    rw [hi.esi]; exact addr_off (by omega_using [hR, hj])
  simp only [tailByte, at_]
  refine wp_movzx rfl (by rw [eK, hi.rd, hi.wr]; exact hp.rdK j hj) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .esi = s.gpr .esi := u₁.other _ (by decide)
  refine wp_movzx rfl (by rw [e₁, eR, u₁.rd, u₁.wr, hi.rd, hi.wr]; exact inRdWr (hp.wrR j hj)) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .esi = s.gpr .esi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), e₁]
  refine wp_st8 rfl (by rw [e₃, eR, u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact hp.wrR j hj) fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ _ z₇ => WP.block_nil ?_
  -- Registers.
  have g₄ : ∀ x, x ≠ .eax → x ≠ .ecx → s₄.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₄.gpr, u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have gR : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .ebx → x ≠ .esi → x ≠ .ebp → s₇.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₇.other x h5, u₆.other x h4, u₅.other x h3, g₄ x h1 h2]
  have ebx₇ : s₇.gpr .ebx = K + BitVec.ofNat 32 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide), hi.ebx]
    exact ofNat_add_one K j
  have esi₇ : s₇.gpr .esi = R + BitVec.ofNat 32 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.esi]
    exact ofNat_add_one R j
  have ebp₆ : s₆.gpr .ebp = BitVec.ofNat 32 (r - j) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.ebp]
  have ebp₇ : s₇.gpr .ebp = BitVec.ofNat 32 (r - (j + 1)) := by
    rw [u₇.gpr, ebp₆, Wp.ofNat_pred (by omega_using [hj])]; rfl
  -- Memory.
  have ecx₃ : (s₃.gpr .ecx).setWidth 8 = s.mem (R.setWidth 64 + BitVec.ofNat 64 j) ^^^
      s.mem (K.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, e₁, eR, eK, setWidth_xor8]
  have mem₇ : s₇.mem = s.mem.writeW (R.setWidth 64 + BitVec.ofNat 64 j)
      (s.mem (R.setWidth 64 + BitVec.ofNat 64 j) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 j)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, e₃, eR, u₃.mem, u₂.mem, u₁.mem]
    exact congrArg _ ecx₃
  have hRj : Region.Sub ⟨R.setWidth 64 + BitVec.ofNat 64 j, 1⟩ ⟨R.setWidth 64, r⟩ :=
    VG.Offset.sub_base _ (by omega_using [hj])
  have hKk : ∀ q < r, s.mem (K.setWidth 64 + BitVec.ofNat 64 q) = s₀.mem (K.setWidth 64 + BitVec.ofNat 64 q) :=
    fun q hq => hi.frame.bytes (R := ⟨K.setWidth 64, r⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hp.disj) (by show r ≤ 2 ^ 64; omega_using [hK]) hq
  have data₇ : ∀ q < r, s₇.mem (R.setWidth 64 + BitVec.ofNat 64 q) =
      if q < j + 1 then s₀.mem (R.setWidth 64 + BitVec.ofNat 64 q) ^^^ s₀.mem (K.setWidth 64 + BitVec.ofNat 64 q)
      else s₀.mem (R.setWidth 64 + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₇, write1_apply]
    by_cases hqj : q = j
    · subst hqj
      rw [ite_eq_left (by rw [BitVec.sub_self]; decide), ite_eq_left (Nat.lt_succ_self _), hi.data q hq,
        ite_eq_right (Nat.lt_irrefl _), hKk q hq]
    · have hne : ¬ (R.setWidth 64 + BitVec.ofNat 64 q - (R.setWidth 64 + BitVec.ofNat 64 j)).toNat < 1 := by
        rw [VG.Offset.sub_toNat' _ (by omega_using [hR, hj]) (by omega_using [hR, hq])]
        split <;> omega_arith
      rw [ite_eq_right hne, hi.data q hq]
      by_cases h1 : q < j
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1])]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1, hqj])]
  have fr₇ : Frame [⟨R.setWidth 64, r⟩] s₀.mem s₇.mem := by
    rw [mem₇]
    exact hi.frame.writeW List.mem_cons_self _ (hRj _ (Region.contains_self _ _) |> fun h => by
      simpa [Region.Contains] using h)
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have sy₇ : s₇.syms = s₀.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms, hi.syms]
  have gpr₇ : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .ebx → x ≠ .esi → x ≠ .ebp → s₇.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [gR x h1 h2 h3 h4 h5, hi.gpr x h1 h2 h3 h4 h5]
  have hz : s₇.zf = some (decide (j + 1 = r)) := by
    rw [z₇, ebp₆, Wp.ofNat_pred (by omega_using [hj]), Wp.ofNat_beq_zero (by omega_using [hR])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hj]))
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], fun q hq => ?_, fr₇, rd₇, wr₇, sy₇, gpr₇⟩
    rw [data₇ q hq, ite_eq_left (by omega_using [hq, hdone])]
  · exact .inr ⟨by rw [hz, decide_eq_false hdone], ebx₇, esi₇, ebp₇, by omega_using [hj, hdone], data₇, fr₇, rd₇,
      wr₇, sy₇, gpr₇⟩

/-- The loop, from its first byte. -/
theorem tailLoop_wp {s₀ : State} {K R : BitVec 32} {r : Nat} (hp : XPre s₀ K R r) (h0 : XInv s₀ K R r 0 s₀) :
    WP isa (.loop (.block tailByte) .ne) s₀ (XDone s₀ K R r) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (tailByte_wp hp hj) fun s' h => ?_
  rcases h with d | ⟨z, d⟩
  · exact .inl ⟨by show VG.X86.eval .ne s' = _; simp [VG.X86.eval, d.zf], d⟩
  · exact .inr ⟨by show VG.X86.eval .ne s' = _; simp [VG.X86.eval, z], r - (j + 1),
      by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

/-! ## The segments

`seg_wp`: one segment of `seqFinal`'s loop. The whole blocks are `seq`'s
steps (`regs`, `areasOk`, `crypt_step` of `Fixed`, with the `len / L` whole
blocks as the data, `fixedW`); the partial segment's areas are those of a
step of `r = len % L` bytes at the partial segment (`fixedT`), of which
`pre` and `crypt` touch only the chaining value and the buffer.
-/

variable {c : Core}

/-- The partial segment's address. -/
abbrev tailA (c : Core) (D : BitVec 32) (len : Nat) : Addr :=
  D.setWidth 64 + BitVec.ofNat 64 (4 * c.bw * (len / (4 * c.bw)))

/-- The regions a run of the loop changes. -/
abbrev fRegions (c : Core) (B D : BitVec 32) (len : Nat) (E : BitVec 32) : List Region :=
  [coreRegion c B, dnRegion c B, ⟨D.setWidth 64, len⟩, stkRegion E c.stack]

/-- What the loop keeps fixed: `Fixed`'s, for the `len` bytes at `D`. -/
structure FPre (c : Core) (s₀ : State) (B D : BitVec 32) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : (⟨D.setWidth 64, len⟩ : Region) ∈ s₀.wr
  dataFit : D.toNat + len ≤ 2 ^ 32
  small : len < 2 ^ 32
  dataScr : Region.Disjoint ⟨D.setWidth 64, len⟩ ⟨B.setWidth 64, 4 * c.total⟩
  stkData : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) ⟨D.setWidth 64, len⟩
  stkMode : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) ⟨slotA B c.slots, 40⟩
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  layout : Layout c

theorem Layout.bw_pos {c : Core} (hL : Layout c) : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]

theorem Layout.bw_le {c : Core} (hL : Layout c) : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]

/-- The whole blocks, as `seq`'s data. -/
theorem FPre.fixedW {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) :
    Fixed c s₀ B D (len / (4 * c.bw)) (4 * c.bw) := by
  have hle : 4 * c.bw * (len / (4 * c.bw)) ≤ len := Nat.mul_div_le len _
  have hbw := hp.layout.bw_pos
  have hD := hp.dataFit
  exact ⟨hp.scr, ⟨_, 0, len, hp.dataW, (BitVec.add_zero _).symm, by omega_using [hle], by omega_using [hD]⟩,
    by omega_using [hD, hle], hp.dataScr.sub_left (Region.sub_prefix hle), hp.stkData.sub_right (Region.sub_prefix hle),
    hp.stkMode, hp.stack, ⟨by omega_using [hbw], Nat.le_refl _⟩, hp.layout⟩

theorem tailD_toNat {D : BitVec 32} {len L : Nat} (hD : D.toNat + len ≤ 2 ^ 32) (hr : 0 < len % L) :
    (D + BitVec.ofNat 32 (L * (len / L))).toNat = D.toNat + L * (len / L) := by
  have hdm := Nat.div_add_mod len L
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L * (len / L)) (by omega_using [hD, hdm, hr]),
    Nat.mod_eq_of_lt (by omega_using [hD, hdm, hr])]

theorem tailD_eq {D : BitVec 32} {len : Nat} (hD : D.toNat + len ≤ 2 ^ 32) (hr : 0 < len % (4 * c.bw)) :
    (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))).setWidth 64 = tailA c D len := by
  have hdm := Nat.div_add_mod len (4 * c.bw)
  exact addr_eq (by omega_using [hD, hdm, hr])

/-- The partial segment, as a step of `len % L` bytes. -/
theorem FPre.fixedT {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) (hr : 0 < len % (4 * c.bw)) :
    Fixed c s₀ B (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))) 1 (len % (4 * c.bw)) := by
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have hmlt : len % (4 * c.bw) < 4 * c.bw := Nat.mod_lt _ (by have := hp.layout.bw_pos; omega_using [this])
  have e := tailD_eq (c := c) hD hr
  have sub : Region.Sub ⟨tailA c D len, len % (4 * c.bw) * 1⟩ ⟨D.setWidth 64, len⟩ :=
    VG.Offset.sub_base _ (by omega_using [hdm])
  refine ⟨hp.scr, ⟨_, 4 * c.bw * (len / (4 * c.bw)), len, hp.dataW, e, by omega_using [hdm], by omega_using [hD]⟩,
    by rw [tailD_toNat hD hr]; omega_using [hD, hdm], ?_, ?_, hp.stkMode, hp.stack, ⟨hr, Nat.le_of_lt hmlt⟩, hp.layout⟩
  · simp only [dataRegion]; rw [e]; exact hp.dataScr.sub_left sub
  · simp only [dataRegion]; rw [e]; exact hp.stkData.sub_right sub

/-- The loop, before segment `j`, from the chaining value `c0`, the whole
blocks `xs` and the partial segment `tl` on entry, in `s₀`. -/
structure FInv (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (len : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (tl : List Byte) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (4 * c.bw * j)
  np : s.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (len - 4 * c.bw * j)
  lt : 4 * c.bw * j < len
  ready : cs.Ready s B k
  data : chunksAt (4 * c.bw) s.mem (D.setWidth 64) (len / (4 * c.bw)) = (run F c0 (xs.take j)).1 ++ xs.drop j
  tail : bytesAt s.mem (tailA c D len) (len % (4 * c.bw)) = tl
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (fRegions c B D len (s₀.gpr .esp)) s₀.mem s.mem

/-- The loop, done. -/
structure FDone (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (len : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (tl : List Byte) (s : State) : Prop where
  b : s.gpr sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : chunksAt (4 * c.bw) s.mem (D.setWidth 64) (len / (4 * c.bw)) = (run F c0 xs).1
  tail : bytesAt s.mem (tailA c D len) (len % (4 * c.bw)) = Spec.Cbc.xor tl (cs.cipher k (run F c0 xs).2)
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) =
    if len % (4 * c.bw) = 0 then (run F c0 xs).2 else cs.cipher k (run F c0 xs).2
  frame : Frame (fRegions c B D len (s₀.gpr .esp)) s₀.mem s.mem

/-- Input block `j`, from the invariant. -/
theorem FInv.input {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {len : Nat} {k : cs.Key} {F : StepFn}
    {c0 tl : List Byte} {xs : List (List Byte)} {j : Nat} {s : State} (hI : FInv cs s₀ B D len k F c0 xs tl j s)
    (hxs : xs.length = len / (4 * c.bw)) (hj : j < len / (4 * c.bw)) :
    bytesAt s.mem (D.setWidth 64 + BitVec.ofNat 64 (4 * c.bw * j)) (4 * c.bw) = xs[j]'(by omega_using [hxs, hj]) := by
  have hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  have e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

theorem Mid.congr {cs : CoreSpec c} {s₀ s s₁ s₂ : State} {B D : BitVec 32} {st j : Nat} {k : cs.Key} {a : Areas}
    (h : Mid cs s₀ B D st j k s a s₁) (hb : s₂.gpr sb = s₁.gpr sb) (he : s₂.gpr .esp = s₁.gpr .esp)
    (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr) (hsy : s₂.syms = s₁.syms) :
    Mid cs s₀ B D st j k s a s₂ :=
  ⟨by rw [hb]; exact h.b, by rw [he]; exact h.esp, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr,
    cs.ready_frame (rs := []) h.ready he hrd hwr hsy (fun x _ => by rw [hm]) (fun _ h => nomatch h)
      (fun _ h => nomatch h),
    by rw [hm]; exact h.agree, by rw [hm]; exact h.frame⟩

/-- `pre`, as `pre_wp`, from the facts of the invariant it needs. -/
theorem preF_wp (cs : CoreSpec c) {M : Mode} {s₀ : State} {B D : BitVec 32} {n st : Nat} {k : cs.Key}
    (hF : Fixed c s₀ B D n st) (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) {j : Nat} (hj : j < n) {s : State}
    (hb : s.gpr sb = B) (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdp : s.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j)) (hready : cs.Ready s B k) :
    WP isa (.block (c.load ++ c.opsCode M.pre)) s
      (Mid cs s₀ B D st j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  have hR := regs hF hj
  refine WP.syms_intro ?_
  refine load_wp hb ⟨by rw [hwr]; exact hF.scr.wr, hF.scr.fit⟩ hF.layout fun s₁ esi₁ _ g₁ m₁ rd₁ wr₁ => ?_
  rw [← List.append_nil (c.opsCode M.pre)]
  have b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide) (by decide)]; exact hb
  have hA : AreasOk c s₁ (lens c st) (areas c B D st j) allLocs :=
    areasOk hF hj b₁ (by rw [esi₁, hdp]) (by rw [wr₁, hwr])
  refine opsCode_wp c (fun o ho => ⟨hpre o ho, mem_allLocs _⟩) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ =>
    WP.block_nil fun sy₂ => ?_
  rw [m₁] at a₂ f₂
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hesp]
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact b₁, esp₂, by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr],
    cs.ready_frame hready (by rw [esp₂, hesp]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) sy₂ f₂
      (toWr hF hwr hR.areasW) hR.areasCore, a₂, f₂.sub hR.areasFine⟩

/-- The data pointer and the bytes left loaded, and the bytes left compared
with a block. -/
theorem cmpL_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {Q : State → Prop}
    (k : ∀ s', s'.gpr .esi = s.mem.readW (slotA B c.dSlot) 32 → s'.gpr .ebp = s.mem.readW (slotA B c.nSlot) 32 →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → s'.cf = some (decide ((s.mem.readW (slotA B c.nSlot) 32).toNat < 4 * c.bw)) → Q s') :
    WP isa (.block (c.load ++ ([.alu .cmp .ebp (.imm (BitVec.ofNat 32 (4 * c.bw)))] : List Instr))) s Q := by
  have hbw := hL.bw_le
  refine WP.syms_intro ?_
  refine load_wp hb hS hL fun s₁ esi₁ ebp₁ g₁ m₁ rd₁ wr₁ => wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil fun sy₂ => ?_
  refine k s₂ (by rw [f₂.gpr, esi₁]) (by rw [f₂.gpr, ebp₁]) (fun r h1 h2 => by rw [f₂.gpr, g₁ r h1 h2])
    (by rw [f₂.mem, m₁]) (by rw [f₂.rd, rd₁]) (by rw [f₂.wr, wr₁]) sy₂ ?_
  rw [cf₂, ebp₁, Wp.toNat_ofNat_lt (by omega_using [hbw])]

/-- The data pointer and the bytes left back to their slots. -/
theorem storeBack_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.zf = s.zf →
      s'.mem = (s.mem.writeW (slotA B c.dSlot) (s.gpr .esi)).writeW (slotA B c.nSlot) (s.gpr .ebp) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Q s') :
    WP isa (.block c.storeBack) s Q := by
  have := hL.room
  have hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega_using [this]
  have hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega_using [this]
  simp only [Core.storeBack, slotAt, at_]
  refine wp_stm hb (slot_inW hS hd) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact slot_inW hS hn) fun s₂ u₂ =>
    WP.block_nil ?_
  refine k s₂ (by rw [u₂.gpr, u₁.gpr]) (by rw [u₂.zf, u₁.zf]) ?_ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    (by rw [u₂.syms, u₁.syms])
  rw [u₂.mem, u₁.mem, u₁.gpr, addr_slotA hS.fit hd, addr_slotA hS.fit hn]

/-- The stores of the data pointer and the count change only their slots. -/
theorem dn_frame (m : Mem) (B : BitVec 32) (d n : BitVec 32) :
    Frame (dnSlots c B) m ((m.writeW (slotA B c.dSlot) d).writeW (slotA B c.nSlot) n) := by
  have h1 : (⟨slotA B c.dSlot, 4⟩ : Region).Contains (slotA B c.dSlot) (32 / 8) := Region.contains_self _ _
  have h2 : (⟨slotA B c.nSlot, 4⟩ : Region).Contains (slotA B c.nSlot) (32 / 8) := Region.contains_self _ _
  exact ((Frame.refl _ _).writeW List.mem_cons_self _ h1).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ h2

/-- On by a block. -/
theorem advanceBytes_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {Q : State → Prop}
    (k : ∀ s', s'.zf = some (s.gpr .ebp - BitVec.ofNat 32 (4 * c.bw) == 0) →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (slotA B c.dSlot) (s.gpr .esi + BitVec.ofNat 32 (4 * c.bw))).writeW (slotA B c.nSlot)
        (s.gpr .ebp - BitVec.ofNat 32 (4 * c.bw)) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Q s') :
    WP isa (.block c.advanceBytes) s Q := by
  simp only [Core.advanceBytes, List.cons_append, List.nil_append]
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ z₂ => ?_
  refine storeBack_wp (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb])
    ⟨by rw [u₂.wr, u₁.wr]; exact hS.wr, hS.fit⟩ hL fun s₃ g₃ z₃ m₃ rd₃ wr₃ sy₃ => ?_
  refine k s₃ (by rw [z₃, z₂, u₁.other _ (by decide)]) (fun r h1 h2 => by rw [g₃, u₂.other r h2, u₁.other r h1])
    ?_ (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr]) (by rw [sy₃, u₂.syms, u₁.syms])
  rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide)]

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot]); omega_arith))

/-- The partial segment is apart from what a whole segment changes. -/
theorem tail_out {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) {j : Nat}
    (hjl : 4 * c.bw * j + 4 * c.bw ≤ 4 * c.bw * (len / (4 * c.bw))) :
    ∀ r ∈ fine c B D (4 * c.bw) j (s₀.gpr .esp) ++ dnSlots c B,
      Region.Disjoint ⟨tailA c D len, len % (4 * c.bw)⟩ r := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbw := hL.bw_le
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have sT : Region.Sub ⟨tailA c D len, len % (4 * c.bw)⟩ ⟨D.setWidth 64, len⟩ :=
    VG.Offset.sub_base _ (by omega_using [hdm])
  have dS : ∀ {r : Region}, Region.Sub r ⟨B.setWidth 64, 4 * c.total⟩ →
      Region.Disjoint ⟨tailA c D len, len % (4 * c.bw)⟩ r := fun h => (hp.dataScr.sub_left sT).sub_right h
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Offset.disjoint (D.setWidth 64) (d := 4 * c.bw * (len / (4 * c.bw))) (n := len % (4 * c.bw))
      (e := 4 * c.bw * j) (k := 4 * c.bw) (.inr hjl) (by omega_using [hD, hdm]) (by omega_using [hD, hdm, hjl])
  · exact dS (Region.sub_prefix (by omega_arith))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))
  · exact (hp.stkData.sub_right sT).symm
  · exact dS (VG.Offset.sub_base _ (by slot_omega))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))

/-- What a whole segment changes, within the loop's regions. -/
theorem seg_big {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) {j : Nat}
    (hjl : 4 * c.bw * j + 4 * c.bw ≤ len) :
    ∀ r ∈ fine c B D (4 * c.bw) j (s₀.gpr .esp) ++ dnSlots c B,
      ∃ r' ∈ fRegions c B D len (s₀.gpr .esp), Region.Sub r r' := by
  have hroom := hp.layout.room
  have hbw := hp.layout.bw_le
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : ∀ {a b c' d : Region} {l : List Region}, d ∈ a :: b :: c' :: d :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, m2, VG.Offset.sub_base _ hjl⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, m1, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩
  · exact ⟨_, m3, fun _ h => h⟩
  · exact ⟨_, m1, Region.sub_prefix (by slot_omega)⟩
  · exact ⟨_, m1, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

theorem xor_nil (y : List Byte) : Spec.Cbc.xor [] y = [] := rfl

/-- A whole segment's `post`, and on. -/
theorem whole_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len) (hM : M.step = 4 * c.bw)
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c (4 * c.bw))) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hxs : xs.length = len / (4 * c.bw)) (htl : tl.length = len % (4 * c.bw)) {j : Nat}
    (hjl : 4 * c.bw * j + 4 * c.bw ≤ len) {s s₃ : State} (hI : FInv cs s₀ B D len k F c0 xs tl j s)
    (hm : Mid cs s₀ B D (4 * c.bw) j k s (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps M.pre (cont (areas c B D (4 * c.bw) j) s.mem))) s₃)
    (hesi : s₃.gpr .esi = D + BitVec.ofNat 32 (4 * c.bw * j))
    (hebp : s₃.gpr .ebp = BitVec.ofNat 32 (len - 4 * c.bw * j)) :
    WP isa (.block (c.opsCode M.post ++ c.advanceBytes)) s₃ fun s' =>
      (s'.zf = some true ∧ FDone cs s₀ B D len k F c0 xs tl s') ∨
        (s'.zf = some false ∧ FInv cs s₀ B D len k F c0 xs tl (j + 1) s') := by
  have hF := hp.fixedW
  have hL := hF.layout
  have hbw := hL.bw_le
  have hbw0 := hL.bw_pos
  have hDf := hp.dataFit
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hj1 : 4 * c.bw * (j + 1) = 4 * c.bw * j + 4 * c.bw := Nat.mul_succ _ _
  have hjn : j < len / (4 * c.bw) :=
    (Nat.le_div_iff_mul_le (by omega_using [hbw0])).mpr (by rw [Nat.mul_comm]; omega_using [hjl, hj1])
  have hjW : 4 * c.bw * j + 4 * c.bw ≤ 4 * c.bw * (len / (4 * c.bw)) := by
    rw [← hj1]; exact Nat.mul_le_mul_left _ hjn
  have hR := regs hF hjn
  have hS : ∀ {t : State}, t.wr = s₀.wr → ScrIn t B c.total := fun h => ⟨by rw [h]; exact hF.scr.wr, hF.scr.fit⟩
  refine WP.syms_intro ?_
  have hA : AreasOk c s₃ (lens c (4 * c.bw)) (areas c B D (4 * c.bw) j) allLocs :=
    areasOk hF hjn hm.b hesi hm.wr
  refine opsCode_wp c (fun o ho => ⟨hpost o ho, mem_allLocs _⟩) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_
  have b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide) (by decide)]; exact hm.b
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, hm.wr]
  refine advanceBytes_wp b₅ (hS wr₅') hL fun s₆ z₆ g₆ m₆ rd₆ wr₆ sy₆ => ?_
  intro sy
  have esi₅ : s₅.gpr .esi = D + BitVec.ofNat 32 (4 * c.bw * j) := by rw [g₅ _ (by decide) (by decide), hesi]
  have ebp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (len - 4 * c.bw * j) := by rw [g₅ _ (by decide) (by decide), hebp]
  rw [esi₅, ebp₅] at m₆
  rw [ebp₅] at z₆
  -- The step's outputs.
  let A := areas c B D (4 * c.bw) j
  have hstep : Agree (lens c (4 * c.bw)) (cont A s₅.mem) (stepA M (4 * c.bw) (cs.cipher k) (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  have xj : rd (cont A s.mem) .dat (4 * c.bw) = xs[j]'(by omega_using [hxs, hjn]) := hI.input hxs hjn
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  have out₅ : bytesAt s₅.mem (D.setWidth 64 + BitVec.ofNat 64 (4 * c.bw * j)) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  have chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  -- The stores of the data pointer and the count.
  have f₆ : Frame (dnSlots c B) s₅.mem s₆.mem := by rw [m₆]; exact dn_frame _ _ _ _
  have all : Frame (fine c B D (4 * c.bw) j (s₀.gpr .esp) ++ dnSlots c B) s.mem s₆.mem :=
    ((hm.frame.mono fun r hr => List.mem_append_left _ hr).trans
      ((f₅.sub hR.areasFine).mono fun r hr => List.mem_append_left _ hr)).trans
      (f₆.mono fun r hr => List.mem_append_right _ hr)
  have dDat : ∀ r ∈ dnSlots c B, Region.Disjoint (datRegion D (4 * c.bw) j) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
  have dChn : ∀ r ∈ dnSlots c B, Region.Disjoint (chnRegion c B) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hR.dChn.symm
    · exact hR.nChn.symm
  have out₆ : bytesAt s₆.mem (D.setWidth 64 + BitVec.ofNat 64 (4 * c.bw * j)) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).1 := by
    rw [← out₅]
    exact List.map_congr_left fun i hi => f₆.bytes dDat (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw])
      (List.mem_range.mp hi)
  have chn₆ : bytesAt s₆.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).2 := by
    rw [← chn₅]
    exact List.map_congr_left fun i hi => f₆.bytes dChn (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw])
      (List.mem_range.mp hi)
  have hrun : run F c0 (xs.take (j + 1)) =
      ((run F c0 (xs.take j)).1 ++ [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).1],
        (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hjn]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hjn]), Option.toList_some, run_snoc]
  have gg : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆ r h1 h2, g₅ r h3 h4]
  have b₆ : s₆.gpr sb = B := by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.esp
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, hm.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅']
  have data₆ : chunksAt (4 * c.bw) s₆.mem (D.setWidth 64) (len / (4 * c.bw)) =
      (run F c0 (xs.take (j + 1))).1 ++ xs.drop (j + 1) := by
    rw [chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₆, run_set F c0 (by omega_using [hxs, hjn])]
    refine all _ fun r hr hcon => ?_
    rcases List.mem_append.mp hr with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · simp only [Region.Contains] at hcon
        have e := (VG.Offset.lt_iff (D.setWidth 64 + BitVec.ofNat 64 i) (D.setWidth 64) (d := 4 * c.bw * j)
          (n := 4 * c.bw) (by omega_using [hDf, hjW, hdm])).mp (by omega_using [hcon])
        rw [sub_self_add _ (by omega_using [hDf, hi, hdm])] at e
        omega_using [hout, e]
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf, hdm])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf, hdm])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf, hdm])) hcon
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf, hdm])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf, hdm])) hcon
  have tail₆ : bytesAt s₆.mem (tailA c D len) (len % (4 * c.bw)) = tl := by
    rw [← hI.tail]
    exact List.map_congr_left fun i hi => all.bytes (tail_out hp hjW)
      (by show len % (4 * c.bw) ≤ 2 ^ 64; omega_using [hDf, hdm]) (List.mem_range.mp hi)
  have fr₆ : Frame (fRegions c B D len (s₀.gpr .esp)) s₀.mem s₆.mem := hI.frame.trans (all.sub (seg_big hp hjl))
  have hlt : len - 4 * c.bw * j < 2 ^ 32 := by have := hp.small; omega_using [this]
  have hz : s₆.zf = some (decide (4 * c.bw * (j + 1) = len)) := by
    rw [z₆, Wp.sub_ofNat (by omega_using [hjl]), Wp.ofNat_beq_zero (by omega_using [hlt])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hjl, hj1]))
  by_cases hdone : 4 * c.bw * (j + 1) = len
  · have hW : len / (4 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ (by omega_using [hbw0])
    have hr : len % (4 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
    have htk : xs.take (j + 1) = xs := List.take_of_length_le (by omega_using [hxs, hW])
    refine .inl ⟨by rw [hz, decide_eq_true hdone], b₆, esp₆, rd₆', wr₆', ?_, ?_, ?_, fr₆⟩
    · rw [data₆, htk, List.drop_of_length_le (by omega_using [hxs, hW]), List.append_nil]
    · rw [tail₆, List.eq_nil_of_length_eq_zero (htl.trans hr), xor_nil]
    · rw [ite_eq_left hr, chn₆]
      exact (congrArg Prod.snd hrun).symm.trans (congrArg (fun t => (run F c0 t).2) htk)
  · refine .inr ⟨by rw [hz, decide_eq_false hdone], b₆, esp₆, rd₆', wr₆', ?_, ?_, by omega_using [hjl, hj1, hdone],
      ?_, data₆, tail₆, by rw [chn₆, hrun], fr₆⟩
    · rw [m₆, readW_write_sep hR.dn, Mem.readW_writeW_self32, hj1, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [m₆, Mem.readW_writeW_self32, Wp.sub_ofNat (by omega_using [hjl])]
      exact congrArg _ (by omega_using [hj1])
    · exact cs.ready_frame hm.ready (by rw [gg _ (by decide) (by decide) (by decide) (by decide)])
        (by rw [rd₆, rd₅]) (by rw [wr₆, wr₅]) sy
        ((f₅.mono fun r hr => List.mem_append_left _ hr).trans (f₆.mono fun r hr => List.mem_append_right _ hr))
        (fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · exact toWr hF hm.wr hR.areasW r h
          · exact toWr hF hm.wr hR.slotsW r h)
        (fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · exact hR.areasCore r h
          · exact hR.slotsCore r h)

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

theorem cont_dat0 (c : Core) (B Dt : BitVec 32) (rr : Nat) (m : Mem) (q : Nat) :
    cont (areas c B Dt rr 0) m .dat q = m (Dt.setWidth 64 + BitVec.ofNat 64 q) := by
  simp only [cont, areas, Nat.mul_zero, BitVec.add_zero]

theorem toNat_add_ofNat {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) :
    (B + BitVec.ofNat 32 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The partial segment's step region, at its address. -/
theorem datRegion_zero (D : BitVec 32) (r : Nat) : datRegion D r 0 = ⟨D.setWidth 64, r⟩ := by
  simp only [datRegion, Nat.mul_zero]
  exact congrArg (Region.mk · r) (BitVec.add_zero _)

/-- The whole blocks are apart from what the partial segment changes. -/
theorem whole_out {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) (hr : 0 < len % (4 * c.bw)) :
    ∀ r ∈ fine c B (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))) (len % (4 * c.bw)) 0 (s₀.gpr .esp) ++
      dnSlots c B, Region.Disjoint (dataRegion D (4 * c.bw) (len / (4 * c.bw))) r := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbw := hL.bw_le
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have sW : Region.Sub (dataRegion D (4 * c.bw) (len / (4 * c.bw))) ⟨D.setWidth 64, len⟩ :=
    Region.sub_prefix (by omega_using [hdm])
  have dS : ∀ {r : Region}, Region.Sub r ⟨B.setWidth 64, 4 * c.total⟩ →
      Region.Disjoint (dataRegion D (4 * c.bw) (len / (4 * c.bw))) r := fun h => (hp.dataScr.sub_left sW).sub_right h
  intro r hr'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [datRegion_zero, tailD_eq hD hr]
    exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hD, hdm])
  · exact dS (Region.sub_prefix (by omega_arith))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))
  · exact (hp.stkData.sub_right sW).symm
  · exact dS (VG.Offset.sub_base _ (by slot_omega))
  · exact dS (VG.Offset.sub_base _ (by slot_omega))

/-- What the partial segment changes, within the loop's regions. -/
theorem part_big {s₀ : State} {B D : BitVec 32} {len : Nat} (hp : FPre c s₀ B D len) (hr : 0 < len % (4 * c.bw)) :
    ∀ r ∈ fine c B (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))) (len % (4 * c.bw)) 0 (s₀.gpr .esp) ++
      dnSlots c B, ∃ r' ∈ fRegions c B D len (s₀.gpr .esp), Region.Sub r r' := by
  have hroom := hp.layout.room
  have hbw := hp.layout.bw_le
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : ∀ {a b c' d : Region} {l : List Region}, d ∈ a :: b :: c' :: d :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro r hr'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [datRegion_zero, tailD_eq hp.dataFit hr]
    exact ⟨_, m2, VG.Offset.sub_base _ (by omega_using [hdm])⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, m1, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩
  · exact ⟨_, m3, fun _ h => h⟩
  · exact ⟨_, m1, Region.sub_prefix (by slot_omega)⟩
  · exact ⟨_, m1, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

/-- The partial segment, after `crypt`: the buffer to the chaining value,
and its first bytes XORed into the data. -/
theorem part_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len)
    (hpre : M.pre = copyBlk c.bw .buf .chn) (hxs : xs.length = len / (4 * c.bw)) (htl : tl.length = len % (4 * c.bw))
    (hr : 0 < len % (4 * c.bw)) {s s₃ : State} (hI : FInv cs s₀ B D len k F c0 xs tl (len / (4 * c.bw)) s)
    (hm : Mid cs s₀ B (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))) (len % (4 * c.bw)) 0 k s
      (cryptBuf (4 * c.bw) (cs.cipher k) (applyOps M.pre (cont (areas c B
        (D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw)))) (len % (4 * c.bw)) 0) s.mem))) s₃)
    (hesi : s₃.gpr .esi = D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw))))
    (hebp : s₃.gpr .ebp = BitVec.ofNat 32 (len % (4 * c.bw))) :
    WP isa (.seq (.block (c.opsCode (copyBlk c.bw .chn .buf) ++ c.tailStart))
      (.seq (.loop (.block tailByte) .ne) (.block c.storeBack))) s₃ fun s' =>
        s'.zf = some true ∧ FDone cs s₀ B D len k F c0 xs tl s' := by
  have hT := hp.fixedT hr
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbw := hL.bw_le
  have hbw0 := hL.bw_pos
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hD := hp.dataFit
  have hmlt : len % (4 * c.bw) < 4 * c.bw := Nat.mod_lt _ (by omega_using [hbw0])
  rw [hpre] at hm
  generalize hDt : D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw))) = Dt at hm hesi hT
  generalize hrr : len % (4 * c.bw) = rr at hm hebp hT hr hmlt htl
  have eDt : Dt.setWidth 64 = tailA c D len := by rw [← hDt]; exact tailD_eq hD (by rw [hrr]; exact hr)
  have tDt : Dt.toNat = D.toNat + 4 * c.bw * (len / (4 * c.bw)) := by
    rw [← hDt]; exact tailD_toNat hD (by rw [hrr]; exact hr)
  have hR := regs hT (j := 0) (by decide)
  let A := areas c B Dt rr 0
  have hA : AreasOk c s₃ (lens c rr) A allLocs :=
    areasOk hT (by decide) hm.b (by rw [hesi, Nat.mul_zero]; exact (BitVec.add_zero _).symm) hm.wr
  have hcIB : ∀ o ∈ copyBlk c.bw .chn .buf, o.InBounds (lens c rr) :=
    copyBlk_inBounds (by simp [lens]) (by simp [lens])
  refine WP.seq (opsCode_wp c (fun o ho => ⟨hcIB o ho, mem_allLocs _⟩) hA fun s₄ a₄ f₄ g₄ rd₄ wr₄ => ?_)
  unfold Core.tailStart
  refine wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => WP.block_nil ?_
  -- The areas after the copy.
  have hY : Agree (lens c rr) (cont A s₄.mem) (applyOps (copyBlk c.bw .chn .buf) (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps (copyBlk c.bw .buf .chn) (cont A s.mem)))) :=
    Agree.trans a₄ (applyOps_agree hcIB hm.agree)
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 xs).2 := by
    have e := hI.chn
    rw [List.take_of_length_le (Nat.le_of_eq hxs)] at e
    exact e
  have hK : (B + BitVec.ofNat 32 (4 * c.buf)).setWidth 64 = slotA B c.buf :=
    addr_slotA hfit (by omega_arith)
  have tK : (B + BitVec.ofNat 32 (4 * c.buf)).toNat = B.toNat + 4 * c.buf := toNat_add_ofNat (by omega_arith)
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have g₆ : ∀ x, x ≠ .ebx → x ≠ .eax → x ≠ .ecx → s₆.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [u₆.other x h1, u₅.other x h1, g₄ x h2 h3]
  have b₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide) (by decide)]; exact hm.b
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, rd₄, hm.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, wr₄, hm.wr]
  have sT : Region.Sub ⟨tailA c D len, rr⟩ ⟨D.setWidth 64, len⟩ := VG.Offset.sub_base _ (by omega_using [hdm, hrr])
  have hxp : XPre s₆ (B + BitVec.ofNat 32 (4 * c.buf)) Dt rr :=
    { pos := hr
      fitK := by rw [tK]; omega_arith
      fitR := by rw [tDt]; omega_using [hD, hdm, hrr]
      disj := by
        rw [hK, eDt]
        exact ((hp.dataScr.sub_left sT).sub_right (VG.Offset.sub_base _ (by omega_arith))).symm
      rdK := fun q hq => by
        rw [hK, rd₆, wr₆]
        exact ⟨_, List.mem_append_right _ hp.scr.wr, by
          rw [VG.Offset.add_add]; exact slot_contains hfit (by omega_arith)⟩
      wrR := fun q hq => by
        rw [eDt, wr₆]
        refine ⟨_, hp.dataW, ?_⟩
        rw [VG.Offset.add_add]
        exact VG.Offset.contains_base _ (by omega_using [hdm, hrr, hq]) (by omega_using [hD, hdm, hrr, hq]) }
  have hx0 : XInv s₆ (B + BitVec.ofNat 32 (4 * c.buf)) Dt rr 0 s₆ :=
    { ebx := by
        rw [u₆.gpr, u₅.gpr, g₄ _ (by decide) (by decide), hm.b]; exact (BitVec.add_zero _).symm
      esi := by rw [g₆ _ (by decide) (by decide) (by decide), hesi]; exact (BitVec.add_zero _).symm
      ebp := by rw [g₆ _ (by decide) (by decide) (by decide), hebp, Nat.sub_zero]
      lt := hr
      data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero _)]
      frame := Frame.refl _ _
      rd := rfl
      wr := rfl
      syms := rfl
      gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.mono (tailLoop_wp hxp hx0) fun s₇ d₇ => ?_)
  have b₇ : s₇.gpr sb = B := by rw [d₇.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), b₆]
  refine storeBack_wp b₇ ⟨by rw [d₇.wr, wr₆]; exact hp.scr.wr, hfit⟩ hL fun s₈ g₈ z₈ m₈ rd₈ wr₈ _ => ?_
  -- What the segment changed.
  have f₈ : Frame (dnSlots c B) s₇.mem s₈.mem := by rw [m₈]; exact dn_frame _ _ _ _
  have f₇ : Frame [⟨Dt.setWidth 64, rr⟩] s₄.mem s₇.mem := by rw [← m₆]; exact d₇.frame
  have allP : Frame (fine c B Dt rr 0 (s₀.gpr .esp) ++ dnSlots c B) s.mem s₈.mem :=
    (((hm.frame.mono fun r hr => List.mem_append_left _ hr).trans
      ((f₄.sub hR.areasFine).mono fun r hr => List.mem_append_left _ hr)).trans
      ((f₇.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, by rw [datRegion_zero]; exact fun _ h => h⟩).mono
        fun r hr => List.mem_append_left _ hr)).trans
      (f₈.mono fun r hr => List.mem_append_right _ hr)
  have hWO := whole_out hp (by rw [hrr]; exact hr)
  rw [hDt, hrr] at hWO
  have hPB := part_big hp (by rw [hrr]; exact hr)
  rw [hDt, hrr] at hPB
  -- The buffer and the chaining value.
  have kc : ∀ {R : Region}, (∀ r ∈ dnSlots c B, R.Disjoint r) → R.Disjoint ⟨Dt.setWidth 64, rr⟩ → R.len ≤ 2 ^ 64 →
      ∀ {i}, i < R.len → s₈.mem (R.base + BitVec.ofNat 64 i) = s₄.mem (R.base + BitVec.ofNat 64 i) :=
    fun h1 h2 hl _ hi => by
      rw [f₈.bytes h1 hl hi]
      exact f₇.bytes (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h2) hl hi
  have chnOut : ∀ r ∈ dnSlots c B, Region.Disjoint (chnRegion c B) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hR.dChn.symm
    · exact hR.nChn.symm
  have chnDat : Region.Disjoint (chnRegion c B) (datRegion Dt rr 0) := hA.apart .chn .dat (by decide)
  rw [datRegion_zero] at chnDat
  have datDn : ∀ r ∈ dnSlots c B, Region.Disjoint ⟨Dt.setWidth 64, rr⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := (hR.dKeep _ List.mem_cons_self).symm; rwa [datRegion_zero] at this
    · have := (hR.nKeep _ List.mem_cons_self).symm; rwa [datRegion_zero] at this
  -- The bytes after the copy.
  have hdat : ∀ q < rr, s₄.mem (Dt.setWidth 64 + BitVec.ofNat 64 q) = tl.getD q 0 := fun q hq => by
    rw [← cont_dat0 c B Dt rr s₄.mem q, hY .dat q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).1,
      cont_dat0, eDt, ← bytesAt_getD s.mem _ (show q < len % (4 * c.bw) by rw [hrr]; exact hq), hI.tail]
  have hbuf : ∀ q < 4 * c.bw, s₄.mem (slotA B c.buf + BitVec.ofNat 64 q) = (cs.cipher k (run F c0 xs).2).getD q 0 :=
    fun q hq => by
      show cont A s₄.mem .buf q = _
      rw [hY .buf q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).2.1, cj]
  have hchn : ∀ q < 4 * c.bw, s₄.mem (slotA B c.chnSlot + BitVec.ofNat 64 q) =
      (cs.cipher k (run F c0 xs).2).getD q 0 := fun q hq => by
    show cont A s₄.mem .chn q = _
    rw [hY .chn q hq, (part_vals c.bw (cs.cipher k) (cont A s.mem) q).2.2 hq, cj]
  have hcl := cs.cipher_len k (run F c0 xs).2
  refine ⟨by rw [z₈, d₇.zf], by rw [g₈]; exact b₇, ?_, by rw [rd₈, d₇.rd, rd₆], by rw [wr₈, d₇.wr, wr₆], ?_, ?_, ?_,
    hI.frame.trans (allP.sub hPB)⟩
  · rw [g₈, d₇.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆ _ (by decide) (by decide) (by decide)]
    exact hm.esp
  · rw [chunksAt_frame allP hWO (by omega_using [hD, hdm]), hI.data, List.take_of_length_le (Nat.le_of_eq hxs),
      List.drop_of_length_le (Nat.le_of_eq hxs), List.append_nil]
  · rw [← eDt, hrr]
    apply List.ext_getElem (by simp only [bytesAt_length, Spec.Cbc.xor, List.length_zipWith, hcl, htl]; omega_arith)
    intro q h1 _
    have hq : q < rr := by rw [bytesAt_length] at h1; exact h1
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, getD_xor (by omega_using [htl, hrr, hq])
      (by rw [hcl]; omega_using [hq, hmlt]), bytesAt_getD _ _ hq,
      f₈.bytes (R := ⟨Dt.setWidth 64, rr⟩) datDn (by show rr ≤ 2 ^ 64; omega_using [hmlt, hbw]) hq, d₇.data q hq, m₆,
      hdat q hq, hK, hbuf q (by omega_using [hq, hmlt])]
  · rw [ite_eq_right (by rw [hrr]; omega_using [hr])]
    apply List.ext_getElem (by rw [bytesAt_length, hcl])
    intro q h1 _
    have hq : q < 4 * c.bw := by rw [bytesAt_length] at h1; exact h1
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, bytesAt_getD _ _ hq]
    exact (kc (R := chnRegion c B) chnOut chnDat (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hq).trans (hchn q hq)

/-! ## The loop -/

theorem seg_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len) (hM : M.step = 4 * c.bw)
    (hpre : M.pre = copyBlk c.bw .buf .chn) (hpost : ∀ o ∈ M.post, o.InBounds (lens c (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = len / (4 * c.bw))
    (htl : tl.length = len % (4 * c.bw)) {j : Nat} {s : State} (hI : FInv cs s₀ B D len k F c0 xs tl j s) :
    WP isa (c.seg M) s fun s' => (s'.zf = some true ∧ FDone cs s₀ B D len k F c0 xs tl s') ∨
      (s'.zf = some false ∧ FInv cs s₀ B D len k F c0 xs tl (j + 1) s') := by
  have hL := hp.layout
  have hbw0 := hL.bw_pos
  have hdm := Nat.div_add_mod len (4 * c.bw)
  have hsm := hp.small
  have hlt := hI.lt
  have hpre' : ∀ st, ∀ o ∈ M.pre, o.InBounds (lens c st) := fun st => by
    rw [hpre]; exact copyBlk_inBounds (by simp [lens]) (by simp [lens])
  have hS : ∀ {t : State}, t.wr = s₀.wr → ScrIn t B c.total := fun h => ⟨by rw [h]; exact hp.scr.wr, hp.scr.fit⟩
  have hnp : (BitVec.ofNat 32 (len - 4 * c.bw * j)).toNat = len - 4 * c.bw * j :=
    Wp.toNat_ofNat_lt (by omega_using [hsm])
  unfold Core.seg Core.segOp
  by_cases hw : 4 * c.bw * j + 4 * c.bw ≤ len
  · -- A whole block.
    have hF := hp.fixedW
    have hj1 : 4 * c.bw * (j + 1) = 4 * c.bw * j + 4 * c.bw := Nat.mul_succ _ _
    have hjn : j < len / (4 * c.bw) :=
      (Nat.le_div_iff_mul_le (by omega_using [hbw0])).mpr (by rw [Nat.mul_comm]; omega_using [hw, hj1])
    have hR := regs hF hjn
    refine WP.seq (WP.mono (preF_wp cs hF (hpre' _) hjn hI.b hI.esp hI.rd hI.wr hI.dp hI.ready) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (crypt_step cs hF hjn h₂) fun s₃ h₃ => ?_)
    refine WP.seq (cmpL_wp h₃.b (hS h₃.wr) hL fun s₄ esi₄ ebp₄ g₄ m₄ rd₄ wr₄ sy₄ cf₄ => ?_)
    have dp₃ : s₃.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (4 * c.bw * j) := by
      rw [h₃.frame.readW (Region.contains_self _ _) hR.dKeep (by decide), hI.dp]
    have np₃ : s₃.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (len - 4 * c.bw * j) := by
      rw [h₃.frame.readW (Region.contains_self _ _) hR.nKeep (by decide), hI.np]
    have hm₄ := h₃.congr (g₄ _ (by decide) (by decide)) (g₄ _ (by decide) (by decide)) m₄ rd₄ wr₄ sy₄
    refine WP.ite false (by
      show s₄.cf = _
      rw [cf₄, np₃, hnp, decide_eq_false (by omega_using [hw])]) (fun h => by cases h) fun _ => ?_
    exact whole_wp cs hp hM hpost hcomp hxs htl hw hI hm₄ (by rw [esi₄, dp₃]) (by rw [ebp₄, np₃])
  · -- The partial segment.
    have hjr : len - 4 * c.bw * j < 4 * c.bw := by omega_using [hw, hlt, hbw0]
    have hjW : len / (4 * c.bw) = j := by
      rw [show len = 4 * c.bw * j + (len - 4 * c.bw * j) by omega_using [hlt]]; exact idx_div hjr
    have hmod : len % (4 * c.bw) = len - 4 * c.bw * j := by
      rw [show len = 4 * c.bw * j + (len - 4 * c.bw * j) by omega_using [hlt]]
      rw [idx_mod hjr]; omega_using [hlt]
    have hr : 0 < len % (4 * c.bw) := by rw [hmod]; omega_using [hlt]
    subst hjW
    have hT := hp.fixedT hr
    have hR := regs hT (j := 0) (by decide)
    refine WP.seq (WP.mono (preF_wp cs hT (hpre' _) (j := 0) (by decide) hI.b hI.esp hI.rd hI.wr
      (by rw [hI.dp, Nat.mul_zero]; exact (BitVec.add_zero _).symm) hI.ready) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (crypt_step cs hT (by decide) h₂) fun s₃ h₃ => ?_)
    refine WP.seq (cmpL_wp h₃.b (hS h₃.wr) hL fun s₄ esi₄ ebp₄ g₄ m₄ rd₄ wr₄ sy₄ cf₄ => ?_)
    have dp₃ : s₃.mem.readW (slotA B c.dSlot) 32 =
        D + BitVec.ofNat 32 (4 * c.bw * (len / (4 * c.bw))) := by
      rw [h₃.frame.readW (Region.contains_self _ _) hR.dKeep (by decide), hI.dp]
    have np₃ : s₃.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (len - 4 * c.bw * (len / (4 * c.bw))) := by
      rw [h₃.frame.readW (Region.contains_self _ _) hR.nKeep (by decide), hI.np]
    have hm₄ := h₃.congr (g₄ _ (by decide) (by decide)) (g₄ _ (by decide) (by decide)) m₄ rd₄ wr₄ sy₄
    refine WP.ite true (by
      show s₄.cf = _
      rw [cf₄, np₃, hnp, decide_eq_true hjr]) (fun _ => ?_) (fun h => by cases h)
    exact WP.mono (part_wp cs hp hpre hxs htl hr hI hm₄ (by rw [esi₄, dp₃]) (by rw [ebp₄, np₃, ← hmod]))
      fun _ h => .inl h

theorem segLoop_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {len : Nat}
    {k : cs.Key} {c0 tl : List Byte} {xs : List (List Byte)} (hp : FPre c s₀ B D len) (hM : M.step = 4 * c.bw)
    (hpre : M.pre = copyBlk c.bw .buf .chn) (hpost : ∀ o ∈ M.post, o.InBounds (lens c (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = len / (4 * c.bw))
    (htl : tl.length = len % (4 * c.bw)) {s : State} (hI : FInv cs s₀ B D len k F c0 xs tl 0 s) :
    WP isa (.loop (c.seg M) .ne) s (FDone cs s₀ B D len k F c0 xs tl) := by
  refine WP.loop (M := isa) (fun m t => ∃ j, m = len - 4 * c.bw * j ∧ FInv cs s₀ B D len k F c0 xs tl j t)
    (fun m t ht => ?_) len s ⟨0, by simp, hI⟩
  obtain ⟨j, rfl, hj⟩ := ht
  refine WP.mono (seg_wp cs hp hM hpre hpost hcomp hxs htl hj) fun s' h => ?_
  have hbw0 := hp.layout.bw_pos
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by show VG.X86.eval .ne s' = _; simp [VG.X86.eval, z], d⟩
  · have h1 := d.lt
    have h2 := hj.lt
    have hj1 : 4 * c.bw * (j + 1) = 4 * c.bw * j + 4 * c.bw := Nat.mul_succ _ _
    exact .inr ⟨by show VG.X86.eval .ne s' = _; simp [VG.X86.eval, z], len - 4 * c.bw * (j + 1),
      by omega_using [h1, h2, hj1, hbw0], j + 1, rfl, d⟩

end VG.Proof.Modes.X86
