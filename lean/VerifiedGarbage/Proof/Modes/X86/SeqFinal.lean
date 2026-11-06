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

end VG.Proof.Modes.X86
