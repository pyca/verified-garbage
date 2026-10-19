module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# A rate-136 sponge of a message, one block before each `x3` call

`hstate E b d`: the third state before block `b` of `pad(E)` (rate 136,
suffix `d`: SHA3-256's `0x06` for `H(ek)`, SHAKE256's `0x1f` for `J(z ‖ c)`)
is absorbed: the sponge of the first `b` blocks of `E`, and, once every block
is absorbed, `absorb 136 (pad 136 d E)`, the state the hash is squeezed
from. `absorbBlock_ok`: the code XORing block `b` of the message `S`
(`Hybrid.HSrc`) into the state, followed by the permutation (of the `x3`
call), takes `hstate E b d` to `hstate E (b + 1) d`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt keccakF absorb pad)
open VG.Proof.Sha3 (Rep xorAt xorByte)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)

/-! ## The sponge -/

/-- The third state before block `b` of `pad(E)` (suffix `d`) is absorbed. -/
def hstate (E : List Byte) (b : Nat) (d : Byte := BitVec.ofNat 8 6) : Spec.Sha3.State :=
  if 136 * b ≤ E.length then Rep 136 (E.take (136 * b)) else absorb 136 (pad 136 d E)

/-- The suffix of the message `S`. -/
abbrev dB (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Byte := BitVec.ofNat 8 S.sfx

theorem hstate_zero (E : List Byte) {d : Byte} : hstate E 0 d = Spec.Sha3.zero := by
  simp only [hstate, Nat.mul_zero, Nat.zero_le, ite_true, List.take_zero, Proof.Sha3.rep_nil]

theorem hstate_done {E : List Byte} {b : Nat} {d : Byte} (h : E.length < 136 * b) :
    hstate E b d = absorb 136 (pad 136 d E) := by
  simp only [hstate, ite_eq_right (show ¬136 * b ≤ E.length by omega)]

theorem xorAt_nil (A : Spec.Sha3.State) (j : Nat) : xorAt A j [] = A := rfl

theorem xorAt_append (A : Spec.Sha3.State) (j : Nat) (bs : List Byte) :
    ∀ cs, xorAt A j (bs ++ cs) = xorAt (xorAt A j bs) (j + bs.length) cs := by
  refine Proof.Sha3.snoc_induction ?_ ?_
  · rw [List.append_nil]; exact (xorAt_nil _ _).symm
  · intro cs c ih
    rw [← List.append_assoc, Proof.Sha3.xorAt_snoc, ih, Proof.Sha3.xorAt_snoc, List.length_append,
      Nat.add_assoc]

/-- A whole block. -/
theorem hstate_full {E : List Byte} {b : Nat} {d : Byte} (h : 136 * b + 136 ≤ E.length) :
    keccakF (xorAt (hstate E b d) 0 ((E.drop (136 * b)).take 136)) = hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega)
  have hbs : ((E.drop (136 * b)).take 136).length = 136 := by
    rw [List.length_take, List.length_drop]; omega
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    ((E.drop (136 * b)).take 136) (by omega) (by rw [hl, hbs]; omega)
  rw [hl, hbs, show 136 * b % 136 = 0 by omega, ite_eq_left (by decide)] at ra
  have ht : E.take (136 * (b + 1)) = E.take (136 * b) ++ (E.drop (136 * b)).take 136 := by
    rw [show 136 * (b + 1) = 136 * b + 136 by omega, List.take_add]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega),
    ite_eq_left (show 136 * (b + 1) ≤ E.length by omega), ht, ra]

/-- The last, partial block, and the padding. -/
theorem hstate_last {E : List Byte} {b : Nat} {d : Byte} (hlo : 136 * b < E.length)
    (hhi : E.length < 136 * b + 136) :
    keccakF (xorByte (xorByte (xorAt (hstate E b d) 0 (E.drop (136 * b))) (E.length - 136 * b)
      d) 135 128) = hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega)
  have hbs : (E.drop (136 * b)).length = E.length - 136 * b := List.length_drop
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    (E.drop (136 * b)) (by omega) (by rw [hl, hbs]; omega)
  rw [hl, hbs, show 136 * b % 136 = 0 by omega, ite_eq_right (show ¬0 + (E.length - 136 * b) = 136 by omega),
    List.take_append_drop] at ra
  rw [hstate_done (show E.length < 136 * (b + 1) by omega),
    Proof.Sha3.absorb_pad (by decide) (by decide), show E.length % 136 = E.length - 136 * b by omega]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega), ← ra]

/-! ## The code -/

theorem inRW {rd rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) : InRegions (rd ++ rs) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_in {X : List Region} {p : Addr} {len : Nat} (hc : Covers [⟨p, len⟩] X) {off n : Nat}
    (h : off + n ≤ len) (hl : len < 2 ^ 64) : InRegions X (p + BitVec.ofNat 64 off) n :=
  hc _ _ ⟨_, List.mem_singleton_self _, contains_off h hl⟩

/-- One word of the message XORed into the state. -/
theorem absorbWord_ok {s : State} {r : Reg} {eo off : Nat} (heo : eo % 8 = 0 ∧ eo < 4096 * 8)
    (hoff : off % 8 = 0 ∧ off < 4096 * 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 eo) 8)
    (hw : InRegions s.wr (s.gpr .x28 + BitVec.ofNat 64 off) 8) :
    WP isa (.block ([.ldr .x .x9 r eo, .ldr .x .x10 .x28 off, .logic .eor .x .x9 .x9 .x10,
      .str .x .x9 .x28 off] : List Instr)) s fun t =>
      Keep [.x9, .x10] s t ∧
        t.mem = s.mem.writeW (s.gpr .x28 + BitVec.ofNat 64 off)
          (s.mem.readW (s.gpr r + BitVec.ofNat 64 eo) 64 ^^^
            s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 off) 64) := by
  refine wp_ldrx (a := s.gpr r + BitVec.ofNat 64 eo) heo rfl hr fun a ha ea => ?_
  refine wp_ldrx (a := s.gpr .x28 + BitVec.ofNat 64 off) hoff (by rw [ha.get .x28])
    (by rw [ha.rd, ha.wr]; exact inRW hw) fun b hb eb => ?_
  refine wp_eor fun c hc ec => ?_
  have hh := (ha.trans hb).trans hc
  refine wp_strx hoff (by rw [hh.get .x28]) (by rw [hh.wr]; exact hw) fun t ht => wp_nil ?_
  refine ⟨(hh.keep.trans ht.keep).mono (by simp), ?_⟩
  rw [ht.mem, ec, hb.get .x9, ea, eb, hc.mem, hb.mem, ha.mem]

/-- The `n` words at `e + eo` (`e` in `r`) XORed into the state at `st`. -/
theorem absorbWords_ok {s : State} {r : Reg} {e st : Addr} {eo n : Nat} (hr9 : r ∉ [.x9, .x10])
    (he : s.gpr r = e)
    (hs : s.gpr .x28 = st) (hn : n ≤ 25) (heo : eo % 8 = 0) (hlim : eo + 8 * n ≤ 32768)
    (hr : ∀ w < n, InRegions (s.rd ++ s.wr) (e + BitVec.ofNat 64 (eo + 8 * w)) 8)
    (hw : Covers [stR st] s.wr) (hd : (stR st).Disjoint ⟨e + BitVec.ofNat 64 eo, 8 * n⟩) :
    WP isa (.block (Impl.MlKem.AArch64.Hybrid.absorbWords r eo n)) s fun t =>
      Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      stateAt t.mem st = xorAt (stateAt s.mem st) 0 (bytesAt s.mem (e + BitVec.ofNat 64 eo) (8 * n)) := by
  unfold Impl.MlKem.AArch64.Hybrid.absorbWords
  refine wp_range_flatMap (M := isa) (N := n)
    (fun w t => Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      stateAt t.mem st = xorAt (stateAt s.mem st) 0 (bytesAt s.mem (e + BitVec.ofNat 64 eo) (8 * w)))
    (fun w t hw' ⟨kt, ft, st'⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, by simp only [Nat.mul_zero]; rfl⟩
  have t25 : t.gpr r = e := (kt.gpr r hr9).trans he
  have t28 : t.gpr .x28 = st := (kt.get .x28).trans hs
  have cst : (stR st).Contains (st + BitVec.ofNat 64 (8 * w)) 8 :=
    Offset.contains_base st (by omega) (by omega)
  refine WP.mono (absorbWord_ok (eo := eo + 8 * w) (off := 8 * w) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [kt.rd, kt.wr, t25]; exact hr w hw')
    (by rw [kt.wr, t28]; exact hw _ _ ⟨stR st, List.mem_singleton_self _, cst⟩)) fun u ⟨ku, mu⟩ => ?_
  rw [t25, t28] at mu
  have sub : Region.Sub ⟨e + BitVec.ofNat 64 eo + BitVec.ofNat 64 (8 * w), 8⟩ ⟨e + BitVec.ofNat 64 eo, 8 * n⟩ :=
    Offset.sub_base _ (by omega)
  have bw : bytesAt t.mem (e + BitVec.ofNat 64 (eo + 8 * w)) 8 =
      bytesAt s.mem (e + BitVec.ofNat 64 eo + BitVec.ofNat 64 (8 * w)) 8 := by
    rw [← ptr_add]
    exact VG.Proof.MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.sub_right sub).symm) (by decide)
  refine ⟨(kt.trans ku).mono (by simp), ?_, ?_⟩
  · rw [mu]
    exact ft.writeW (List.mem_singleton_self _) _ cst
  · rw [mu, FixedHash.absorbWord_state _ _ _ (by omega), st', bw, show 8 * (w + 1) = 8 * w + 8 by omega,
      VG.Proof.MlKem.bytesAt_add, xorAt_append, VG.Proof.MlKem.bytesAt_length, Nat.zero_add]

theorem padCode_eq (pos sfx : Nat) :
    Impl.MlKem.AArch64.Hybrid.xorByte pos sfx ++ Impl.MlKem.AArch64.Hybrid.xorByte 135 128 =
      FixedHash.padCode .x28 0 136 pos sfx := by
  simp only [FixedHash.padCode, FixedHash.xorByteCode, Impl.MlKem.AArch64.Hybrid.xorByte, Nat.zero_add]

/-- What the code needs of the message `S`: its register is kept by the
calls around it, and its words are within reach of `ldr`. -/
structure SrcOk (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Prop where
  reg : S.r = .x25 ∨ S.r = .x28
  h8 : S.len % 8 = 0
  b8 : S.base % 8 = 0
  lim : S.base + S.len ≤ 32768

theorem SrcOk.keep {S : Impl.MlKem.AArch64.Hybrid.HSrc} (h : SrcOk S) {rs : List Reg} {s t : State}
    (k : Keep rs s t) (h25 : .x25 ∉ rs) (h28 : .x28 ∉ rs) : t.gpr S.r = s.gpr S.r := by
  rcases h.reg with e | e <;> rw [e]
  · exact k.gpr _ h25
  · exact k.gpr _ h28

theorem SrcOk.not9 {S : Impl.MlKem.AArch64.Hybrid.HSrc} (h : SrcOk S) : S.r ∉ [.x9, .x10] := by
  rcases h.reg with e | e <;> rw [e] <;> decide

/-- Block `b` of `pad(E)` XORed into the state: once permuted, the next state. -/
theorem absorbBlock_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {e st : Addr} {E : List Byte}
    {b : Nat} (hS : SrcOk S)
    (he : s.gpr S.r + BitVec.ofNat 64 S.base = e) (hs : s.gpr .x28 = st) (hb : 136 * b < S.len)
    (hE : bytesAt s.mem e S.len = E) (hst : stateAt s.mem st = hstate E b (dB S))
    (hr : Covers [⟨e, S.len⟩] (s.rd ++ s.wr))
    (hw : Covers [stR st] s.wr) (hd : (stR st).Disjoint ⟨e, S.len⟩) :
    WP isa (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S b)) s fun t =>
      Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      keccakF (stateAt t.mem st) = hstate E (b + 1) (dB S) := by
  have h8 := hS.h8
  have hb8 := hS.b8
  have hlim := hS.lim
  have hlen : E.length = S.len := by rw [← hE]; exact VG.Proof.MlKem.bytesAt_length _ _ _
  have rd : ∀ {o n : Nat}, o + n ≤ S.len → InRegions (s.rd ++ s.wr) (e + BitVec.ofNat 64 o) n :=
    fun h => covers_in hr h (by omega)
  -- the words at `S.r + S.base + o` are those at `e + o`
  have pa : ∀ o : Nat, s.gpr S.r + BitVec.ofNat 64 (S.base + o) = e + BitVec.ofNat 64 o := fun o => by
    rw [← ptr_add, he]
  unfold Impl.MlKem.AArch64.Hybrid.absorbBlock
  split
  · rename_i hfull
    refine WP.mono (absorbWords_ok (e := s.gpr S.r) (eo := S.base + 136 * b) hS.not9 rfl hs (by decide)
      (by omega) (by omega)
      (fun w hw' => by rw [Nat.add_assoc, pa]; exact rd (by omega)) hw
      (by rw [pa]; exact hd.sub_right (Offset.sub_base e (by omega)))) fun t ⟨kt, ft, mt⟩ => ⟨kt, ft, ?_⟩
    rw [mt, hst, pa, show 8 * 17 = 136 from rfl, ← VG.Proof.MlKem.bytesAt_slice _ _ hfull, hE]
    exact hstate_full (by omega)
  · rename_i hpart
    have hnw : 8 * ((S.len - 136 * b) / 8) = S.len - 136 * b := by omega
    rw [List.append_assoc, WP.block_append_iff, padCode_eq]
    refine WP.mono (absorbWords_ok (e := s.gpr S.r) (eo := S.base + 136 * b) hS.not9 rfl hs (by omega)
      (by omega) (by omega)
      (fun w hw' => by rw [Nat.add_assoc, pa]; exact rd (by omega)) hw
      (by rw [pa]; exact hd.sub_right (Offset.sub_base e (by omega)))) fun t ⟨kt, ft, mt⟩ => ?_
    have t28 : t.gpr .x28 = st := (kt.get .x28).trans hs
    refine WP.mono (FixedHash.pad_ok (s := t) (sc := .x28) (st := 0) (rate := 136)
      (pos := S.len - 136 * b) (sfx := S.sfx) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by decide)
      (by rw [kt.wr, t28, ptr_zero]; exact hw)) fun u ⟨ku, fu, mu⟩ => ?_
    rw [t28, ptr_zero] at fu mu
    refine ⟨(kt.trans ku).mono (by simp), ft.trans fu, ?_⟩
    rw [mu, mt, hst, pa, hnw, ← VG.Proof.MlKem.bytesAt_drop _ _ (by omega), hE]
    have hh := hstate_last (E := E) (b := b) (d := dB S) (by omega) (by omega)
    rw [hlen] at hh
    exact hh

end VG.Proof.MlKem.AArch64.Hybrid
