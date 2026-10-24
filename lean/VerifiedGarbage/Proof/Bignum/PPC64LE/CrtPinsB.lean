module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseD
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad

/-!
# The RSA private-key operation on PPC64LE: the registers at the later cuts

After `checks`, the cuts are after the blocks that start a power, `m₂`'s
export, `recombineP` and each half of `recombineX`, and the output: their
registers, from the initial state (`pins*`), through the correctness proof's
phases (`mid1A_ok`, `mid1B_ok`, `mid1_ok`, `mid2A_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

/-- A power's first block. -/
abbrev PW1 (xj oD oLen : Nat) : List Instr :=
  [.load .d .r30 .r23 oIn, .load .d .r31 .r23 oNLen, .load .d .r18 .r23 oD, .load .d .r19 .r23 oLen,
    .addi .r14 .r10 0] ++ xb .r15 xj

/-- `setupP` and a power's first block: the registers. -/
theorem pw1_ok {t : State} {BX I D : Addr} {Z oA wX xj k L oB oLen oD : Nat} (hs : Scr t BX Z) (hZ : 256 ≤ Z)
    (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0)
    (hB : word t.mem BX oB = off BX oA) (hLw : word t.mem BX oLen = BitVec.ofNat 64 L)
    (hI : word t.mem BX oIn = off I 0) (hK : word t.mem BX oNLen = BitVec.ofNat 64 k)
    (hDp : word t.mem BX oD = off D 0) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) :
    WP isa (.seq (.block (setupP oB oLen)) (.block (PW1 xj oD oLen))) t fun u =>
      [Reg.r10, .r11, .r14, .r15, .r18, .r19, .r23, .r27, .r28, .r29, .r30, .r31].map u.gpr =
        [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
          off BX (slot wX xj), off D 0, BitVec.ofNat 64 L, BX, off BX (slot wX 0), BitVec.ofNat 64 (8 * (wX + 2)),
          BitVec.ofNat 64 (8 * (wsWords L + 2)), off I 0, BitVec.ofNat 64 k] := by
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL hZ hB hLw hL hL') fun s₁ ⟨⟨a10, _, a29, a11, _, m1⟩, k1⟩ => ?_)
  have hI' : s₁.mem.readW (off BX 24) 64 = off I 0 := by rw [m1]; exact hI
  have hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by rw [m1]; exact hK
  have hD' : s₁.mem.readW (off BX oD) 64 = off D 0 := by rw [m1]; exact hDp
  have hL'' : s₁.mem.readW (off BX oLen) 64 = BitVec.ofNat 64 L := by rw [m1]; exact hLw
  have hs1 := hs.congr k1.wr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r30, .r31, .r18, .r19, .r14] (Q := fun u => u.gpr .r30 = off I 0 ∧
    u.gpr .r31 = BitVec.ofNat 64 k ∧ u.gpr .r18 = off D 0 ∧ u.gpr .r19 = BitVec.ofNat 64 L ∧
    u.gpr .r14 = off BX (oA + slot (wsWords L) 0) ∧ u.mem = s₁.mem) (by
      prun [(k1.gpr _ (by decide)).trans h23, a10, oIn, oNLen, hs1.ld (show 24 + 8 ≤ Z by omega),
        hs1.ld (show 16 + 8 ≤ Z by omega),
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oD < 2 ^ 15 by omega, show oD % 4 = 0 by omega⟩,
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oLen < 2 ^ 15 by omega, show oLen % 4 = 0 by omega⟩,
        hs1.ld (show oD + 8 ≤ Z by omega), hs1.ld (show oLen + 8 ≤ Z by omega), hI', hK', hD', hL'',
        BitVec.add_zero, off_off]) rfl) fun s₂ ⟨⟨a30, a31, a18, a19, a14, _⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) xj) fun u ⟨⟨a15, _⟩, k3⟩ => ?_
  simp only [List.map_cons, List.map_nil, a15, k3.gpr .r10 (by decide), k3.gpr .r11 (by decide),
    k3.gpr .r14 (by decide), k3.gpr .r18 (by decide), k3.gpr .r19 (by decide), k3.gpr .r23 (by decide),
    k3.gpr .r27 (by decide), k3.gpr .r28 (by decide), k3.gpr .r29 (by decide), k3.gpr .r30 (by decide),
    k3.gpr .r31 (by decide), k2.gpr .r10 (by decide), k2.gpr .r11 (by decide), k2.gpr .r23 (by decide),
    k2.gpr .r27 (by decide), k2.gpr .r28 (by decide), k2.gpr .r29 (by decide), k1.gpr .r23 (by decide),
    k1.gpr .r27 (by decide), k1.gpr .r28 (by decide), a10, a11, a14, a18, a19, a29, a30, a31, h23, h27, h28]

/-- What two initial states with the same public data share, of the layout. -/
theorem layout_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 d s₀)
    (h' : C0 d s₀') :
    cS s₀ = cS s₀' ∧ cwX s₀ = cwX s₀' ∧ cwP s₀ = cwP s₀' ∧ cwQ s₀ = cwQ s₀' ∧ oPa s₀ = oPa s₀' ∧
      oQa s₀ = oQa s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' := by
  obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
  simp only [cwX, cwP, cwQ, oPa, oQa, eS, ek, ep, eq, and_self]

/-- The front, `loadX` and `checks`, then `c`. -/
abbrev NA (c : Prog isa) : Prog isa := .seq (.block (Crt.save ++ Crt.args ++ setupX)) (.seq loadX (.seq checks c))

theorem pins98 : Pins (At C0 crtF 98)
    [.r10, .r11, .r14, .r15, .r18, .r19, .r23, .r27, .r28, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (cS s₀) (oPa s₀ + slot (cwP s₀) 0), off (cS s₀) (slot (cwX s₀) 4), off (stackArg s₀ 2) 0,
      BitVec.ofNat 64 (cpL s₀), cS s₀, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
      BitVec.ofNat 64 (8 * (cwP s₀ + 2)), off (s₀.gpr .r7) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NA (.seq (.block (setupP oBP oPLen)) (.block (PW1 4 oDP oPLen)))) rfl
      (WP.seq (WP.mono (front_ok s₀ h.1) fun s F => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_facts h.1
    have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t X _ k1 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      X.out.word (Or.inl hd) (by omega)
    exact pw1_ok (F.scr.congr k1.wr) (by omega) ((k1.gpr _ (by decide)).trans F.r23)
      ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by decide) (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL)
      (by rw [hd _ (by decide)]; exact F.hIn) (by rw [hd _ (by decide)]; exact F.hNL)
      (by rw [hd _ (by decide)]; exact F.hDP) p1 (by omega)
  · obtain ⟨eS, eX, eP, -, eoP, -, ek, ep, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, e7, -, -, e2, -⟩ := data_vals h h'
    simp only [eS, eX, eP, eoP, ek, ep, e7, e2]

/-- The phases through `p`'s power, then `c`. -/
abbrev NP (c : Prog isa) : Prog isa := NA (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen) c))

theorem pins150 : Pins (At C0 crtF 150)
    [.r10, .r11, .r14, .r15, .r18, .r19, .r23, .r27, .r28, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), BitVec.ofNat 64 (2 * cwQ s₀),
      off (cS s₀) (oQa s₀ + slot (cwQ s₀) 0), off (cS s₀) (slot (cwX s₀) 5), off (stackArg s₀ 4) 0,
      BitVec.ofNat 64 (cqL s₀), cS s₀, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
      BitVec.ofNat 64 (8 * (cwQ s₀ + 2)), off (s₀.gpr .r7) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NP (.seq (.block (setupP oBQ oQLen)) (.block (PW1 5 oDQ oQLen)))) rfl
      (WP.seq (WP.mono (front_ok s₀ h.1) fun s F => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_facts h.1
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t₁ X _ k1 => mid1B_ok hP F X k1 (by decide) (by decide) (by decide)
      fun t Y k2 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      Y.out.word (Or.inl hd) (by omega)
    exact pw1_ok (F.scr.congr k2.wr) (by omega) ((k2.gpr _ (by decide)).trans F.r23)
      ((k2.gpr _ (by decide)).trans F.r27) ((k2.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by decide) (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL)
      (by rw [hd _ (by decide)]; exact F.hIn) (by rw [hd _ (by decide)]; exact F.hNL)
      (by rw [hd _ (by decide)]; exact F.hDQ) q1 (by omega)
  · obtain ⟨eS, eX, -, eQ, -, eoQ, ek, -, eq⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, e7, -, -, -, e4, -⟩ := data_vals h h'
    simp only [eS, eX, eQ, eoQ, ek, eq, e7, e4]

/-- The phases through both powers, then `c`. -/
abbrev NQ (c : Prog isa) : Prog isa := NP (.seq (.block (setupP oBQ oQLen)) (.seq (power 5 oDQ oQLen) c))

/-- `m₂`'s export, its first block. -/
abbrev EX1 : List Instr :=
  PublicChecked.base .r15 4 ++ [.load .d .r17 .r23 oQLen, .add .r15 .r15 .r17, .subi .r15 .r15 1] ++ xb .r16 1

theorem ex1_ok {t : State} {BQ BX : Addr} {Z wQ wX L : Nat} (hx : Scr t BX Z) (hZ : 256 ≤ Z)
    (h10 : t.gpr .r10 = off BQ (slot wQ 0)) (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (wQ + 2)))
    (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) (hL : word t.mem BX oQLen = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) :
    WP isa (.block EX1) t fun u =>
      [Reg.r15, .r16, .r17, .r23].map u.gpr =
        [off BQ (slot wQ 4 + (L - 1)), off BX (slot wX 1), BitVec.ofNat 64 L, BX] := by
  have e4 : slot wQ 4 = 256 + 4 * (8 * (wQ + 2)) := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a15, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15, .r17] (Q := fun s₂ => s₂.gpr .r15 = off BQ (slot wQ 4 + (L - 1)) ∧
    s₂.gpr .r17 = BitVec.ofNat 64 L ∧ s₂.mem = s₁.mem) ?_ (by decide)) fun s₂ ⟨⟨b15, b17, _⟩, k2⟩ => ?_
  · have hL' : s₁.mem.readW (off BX 56) 64 = BitVec.ofNat 64 L := by rw [m1]; exact hL
    prun [a15, (k1.gpr .r23 (by decide)).trans h23, oQLen, (hx.congr k1.wr).ld (show 56 + 8 ≤ Z by omega), hL',
      off_add, BitVec.add_zero]
    rw [off_sub1 _ (by omega)]; congr 2; omega
  have k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r16) (by decide) (by decide) (k12.gpr _ (by decide) |>.trans h27)
    (k12.gpr _ (by decide) |>.trans h28) 1) fun u ⟨⟨b16, _⟩, k3⟩ => ?_
  simp only [List.map_cons, List.map_nil, b16, k3.gpr .r15 (by decide), k3.gpr .r17 (by decide),
    k3.gpr .r23 (by decide), (k12.gpr .r23 (by decide)).trans h23, b15, b17]

theorem pins201 : Pins (At C0 crtF 201) [.r15, .r16, .r17, .r23] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4 + (cqL s₀ - 1)),
      off (cS s₀) (slot (cwX s₀) 1), BitVec.ofNat 64 (cqL s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := NQ (.block EX1)) (by decide +kernel)
      (WP.seq (WP.mono (front_ok s₀ h.1) fun s F => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_facts h.1
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1_ok hP F fun t _ _ _ _ _ _ _ _ t10 t29 O1 k1 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega)
    exact ex1_ok (F.scr.congr k1.wr) (by omega) t10 t29 ((k1.gpr _ (by decide)).trans F.r23)
      ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28)
      (by rw [hd _ (by decide)]; exact F.hQL) q1
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, eq⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ, eq]

/-- `m₂`'s export and `p`'s registers, then `c`. -/
abbrev NE (c : Prog isa) : Prog isa := NQ (.seq exportM2 (.seq (.block (setupP oBP oPLen)) c))

theorem pins204 : Pins (At C0 crtF 204) [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2)), BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NE (.block [.load .d .r31 .r23 oQLen])) (by decide +kernel)
      (WP.seq (WP.mono (front_ok s₀ h.1) fun s F => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_facts h.1
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have p1 := hP.p1; have pk := hP.pk
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX1 := e (cwX s₀) 1; have eX8 := e (cwX s₀) 8; have eQ8 := e (cwQ s₀) 8; have eP8 := e (cwP s₀) 8
    have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
    have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega
    have hwQ : cwQ s₀ ≤ cwX s₀ := by have := hP.pq; unfold cwQ; omega
    refine mid1_ok hP F fun t _ _ _ _ _ _ _ _ t10 t29 O1 k1 => ?_
    have hs := F.scr.congr k1.wr
    have h23 := (k1.gpr _ (by decide)).trans F.r23
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega)
    refine WP.seq (WP.mono (exportM2_ok (L := cqL s₀) (hs.sub (show oQa s₀ + slot (cwQ s₀) 8 ≤ cZ s₀ by omega))
      (Scr.le hs (show slot (cwX s₀) 8 ≤ cZ s₀ by omega)) t10 t29 h23 ((k1.gpr _ (by decide)).trans F.r27)
      ((k1.gpr _ (by decide)).trans F.r28) (by rw [hd _ (by decide)]; exact F.hQL) q1 hqw (by omega)
      (Nat.le_refl _) (Nat.le_refl _) (fun x hx => by
        rcases ofs_rebase (cS s₀) x (o := oQa s₀) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega))
      fun u₁ ⟨⟨_, o1⟩, k2⟩ => ?_)
    have hd1 : ∀ d, d + 8 ≤ 256 → word u₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [o1.word (Or.inl (by omega)) (by omega)]; exact hd d hd'
    refine WP.seq (WP.mono (setupP_ok (oA := oPa s₀) (hs.congr k2.wr) ((k2.gpr _ (by decide)).trans h23) (by decide) (by decide)
      (by omega) (by rw [hd1 _ (by decide)]; exact F.hBP) (by rw [hd1 _ (by decide)]; exact F.hPL) p1 (by omega))
      fun u₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k3⟩ => ?_)
    have k23 := k2.trans k3
    have hQL' : u₂.mem.readW (off (cS s₀) 56) 64 = BitVec.ofNat 64 (cqL s₀) := by
      rw [m2]; exact (hd1 56 (by decide)).trans F.hQL
    refine WP.mono (WP.keep [.r31] (Q := fun v => v.gpr .r31 = BitVec.ofNat 64 (cqL s₀)) (by
      prun [(k23.gpr .r23 (by decide)).trans h23, oQLen, ((hs.congr k2.wr).congr k3.wr).ld (show 56 + 8 ≤ cZ s₀ by omega),
        hQL']) rfl) fun v ⟨a31, k4⟩ => ?_
    simp only [List.map_cons, List.map_nil, a31, k4.gpr .r10 (by decide), k4.gpr .r11 (by decide),
      k4.gpr .r21 (by decide), k4.gpr .r23 (by decide), k4.gpr .r27 (by decide), k4.gpr .r28 (by decide),
      k4.gpr .r29 (by decide), a10, a11, a21, a29, k23.gpr .r23 (by decide), k23.gpr .r27 (by decide),
      k23.gpr .r28 (by decide), h23, (k1.gpr _ (by decide)).trans F.r27, (k1.gpr _ (by decide)).trans F.r28]
  · obtain ⟨eS, eX, eP, -, eoP, -, -, -, eq⟩ := layout_eq h h'
    simp only [eS, eX, eP, eoP, eq]

/-- Through `recombineP`, from the initial state. -/
theorem pre_rec {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s u, PF s₀ → Front s₀ s → XR s₀ s u →
      Keep (mid1Regs ++ ([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] ++ recRegs)) s u → WP isa c u Q) :
    WP isa (NE (.seq recombineP c)) s₀ Q :=
  WP.seq (WP.mono (front_ok s₀ h.1) fun s F =>
    mid1_ok (pre_facts h.1) F fun _ t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 =>
      mid2A_ok (pre_facts h.1) F t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 fun u R k => hc s u (pre_facts h.1) F R k)

/-- `recombineX`'s first block. -/
abbrev X1 : List Instr :=
  setupP oBP oPLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0, .lsl .r11 .r4 1] ++ xb .r14 7 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

/-- `recombineX`'s second block. -/
abbrev X2 : List Instr :=
  setupP oBQ oQLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0] ++ xb .r14 6 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

theorem pins249 : Pins (At C0 crtF 249) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 7),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4), BitVec.ofNat 64 (2 * cwP s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE (.seq recombineP (.block X1))) (by decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega)
    refine WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega)))
      (F.scr.congr k.wr) ((k.gpr _ (by decide)).trans F.r23) (by decide) (by decide) (by omega)
      (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega)
      (by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega) ((k.gpr _ (by decide)).trans F.r27) ((k.gpr _ (by decide)).trans F.r28))
      fun v ⟨⟨a14, a11, a22, a15, _⟩, k'⟩ => ?_
    simp only [List.map_cons, List.map_nil, a14, a11, a22, a15, k'.gpr .r23 (by decide), k'.gpr .r27 (by decide),
      k'.gpr .r28 (by decide), (k.gpr _ (by decide)).trans F.r23, (k.gpr _ (by decide)).trans F.r27,
      (k.gpr _ (by decide)).trans F.r28]
  · obtain ⟨eS, eX, eP, -, eoP, -, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eP, eoP]

theorem pins255 : Pins (At C0 crtF 255) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 6),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE (.seq recombineP (.seq (.block X1) (.seq (.seq Precompute.zeroWords
      (.seq (.block (xb .r14 7 ++ [.addi .r11 .r22 0])) copyN)) (.block X2))))) (by decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 8
    have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega
    have hwP : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega
    have hs := F.scr.congr k.wr
    have h23 := (k.gpr _ (by decide)).trans F.r23
    have h27 := (k.gpr _ (by decide)).trans F.r27
    have h28 := (k.gpr _ (by decide)).trans F.r28
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega)
    refine WP.seq (WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega)))
      hs h23 (by decide) (by decide) (by omega) (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega) hwX h27 h28)
      fun v₁ ⟨⟨a14, a11, a22, a15, m1⟩, k1⟩ => ?_)
    refine WP.seq (WP.mono (xfer_ok (hs.congr k1.wr) (show oPa s₀ + slot (cwP s₀) 8 ≤ cZ s₀ by omega)
      (Nat.le_of_eq doP.symm) (by decide) (by omega) (by omega) hwX a14 a11 a22 a15
      ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28)) fun v₂ ⟨⟨_, out2⟩, k2⟩ => ?_)
    have k12 := k1.trans k2
    have hd2 : ∀ d, d + 8 ≤ 256 → word v₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out2.word (Or.inl (by omega)) (by omega), m1]; exact hd d hd'
    refine WP.mono (blk_ok (j := 6) (oA := oQa s₀) _ (fun t h11 _ => midQ_ok h11) (hs.congr k12.wr)
      ((k12.gpr _ (by decide)).trans h23) (by decide) (by decide) (by omega)
      (by rw [hd2 _ (by decide)]; exact F.hBQ) (by rw [hd2 _ (by decide)]; exact F.hQL) q1 (by omega) hwX
      ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28))
      fun v ⟨⟨b14, b11, b22, b15, _⟩, k3⟩ => ?_
    simp only [List.map_cons, List.map_nil, b14, b11, b22, b15, k3.gpr .r23 (by decide), k3.gpr .r27 (by decide),
      k3.gpr .r28 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide), k12.gpr .r28 (by decide),
      h23, h27, h28]
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ]

/-- The output's registers. -/
abbrev FIN : List Instr := [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen]

theorem pins274 : Pins (At C0 crtF 274) [.r10, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), cS s₀, off (s₀.gpr .r3) 0,
      BitVec.ofNat 64 (ck s₀), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE (.seq recombineP (.seq recombineX (.block FIN)))) (by decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX2 := e (cwX s₀) 2; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 8
    have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega
    obtain ⟨-, -, -, -, -, mQb, -⟩ := masked_facts hP
    have hs := F.scr.congr k.wr
    have h23 := (k.gpr _ (by decide)).trans F.r23
    have h27 := (k.gpr _ (by decide)).trans F.r27
    have h28 := (k.gpr _ (by decide)).trans F.r28
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega)
    refine WP.seq (WP.mono (recombineX_ok (oP := oPa s₀) (oQ := oQa s₀) hs (by omega) (Nat.le_of_eq doP.symm)
      (by omega) (by omega) pq hwX h23 h27 h28 (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) (by rw [hd _ (by decide)]; exact F.hBQ)
      (by rw [hd _ (by decide)]; exact F.hQL) p1 (by omega) q1 (by omega) R.v0 R.w0 R.v5 mQb R.h4 R.q4)
      fun v₁ ⟨⟨_, o1⟩, k1⟩ => ?_)
    have O1 : Outside (cS s₀) (slot (cwX s₀) 2) (6 * (8 * (cwX s₀ + 2))) u.mem v₁.mem := by
      intro x hx
      refine o1 x fun r hr => ?_
      change ofs (cS s₀) x < r.1 ∨ r.1 + r.2 ≤ ofs (cS s₀) x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      change ofs (cS s₀) x < slot (cwX s₀) 2 ∨ slot (cwX s₀) 2 + 6 * (8 * (cwX s₀ + 2)) ≤ ofs (cS s₀) x at hx
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp only [e] at hx ⊢ <;> omega
    have hd1 : ∀ d, d + 8 ≤ 256 → word v₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [O1.word (Or.inl (by omega)) (by omega)]; exact hd d hd'
    have hs1 := hs.congr k1.wr
    have e0 : off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
    have hO' : v₁.mem.readW (cS s₀) 64 = off (s₀.gpr .r3) 0 := by
      have h0 : word v₁.mem (cS s₀) 0 = off (s₀.gpr .r3) 0 := (hd1 0 (by decide)).trans F.hOut
      rw [← e0]; exact h0
    have ld0 : InRegions (v₁.rd ++ v₁.wr) (cS s₀) 8 := by
      have e0' : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
      have := hs1.ld (show 0 + 8 ≤ cZ s₀ by omega); rwa [e0'] at this
    have hK' : v₁.mem.readW (off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) := by
      show word v₁.mem (cS s₀) 16 = _; rw [hd1 16 (by decide)]; exact F.hNL
    refine WP.mono (WP.keep [.r10, .r29, .r27, .r28] (Q := fun t =>
      t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) ∧
        t.gpr .r27 = off (s₀.gpr .r3) 0 ∧ t.gpr .r28 = BitVec.ofNat 64 (ck s₀)) (by
      prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28,
        (k1.gpr .r23 (by decide)).trans h23, oOut, oNLen, ld0, hs1.ld (show 16 + 8 ≤ cZ s₀ by omega), hO', hK',
        BitVec.add_zero]) (by decide)) fun v ⟨⟨a10, a29, a27, a28⟩, k2⟩ => ?_
    simp only [List.map_cons, List.map_nil, a10, a29, a27, a28, k2.gpr .r23 (by decide), k1.gpr .r23 (by decide),
      h23]
  · obtain ⟨eS, eX, -, -, -, -, ek, -, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, e3, -⟩ := data_vals h h'
    simp only [eS, eX, ek, e3]

end VG.Proof.Bignum.PPC64LE.Crt
