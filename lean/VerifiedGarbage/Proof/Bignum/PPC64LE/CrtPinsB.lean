module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseD
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtR2

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

variable {pc : Bool}

/-- A power's first block. -/
abbrev PW1 (xj : Nat) : List Instr := [.load .d .r25 .r23 oNLen, .addi .r14 .r10 0] ++ xb .r15 xj

/-- `setupP` and a power's first block: the registers. -/
theorem pw1_ok {t : State} {BX : Addr} {Z oA wX xj k L oB oLen : Nat} (hs : Scr t BX Z) (hZ : 256 ≤ Z)
    (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : word t.mem BX oB = off BX oA) (hLw : word t.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word t.mem BX oNLen = BitVec.ofNat 64 k) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) :
    WP isa (.seq (.block (setupP oB oLen)) (.block (PW1 xj))) t fun u =>
      [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29].map u.gpr =
        [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
          off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
          BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] := by
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL hZ hB hLw hL hL') fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  have hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by rw [m1]; exact hK
  have hs1 := hs.congr k1.wr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 k ∧
    u.gpr .r14 = off BX (oA + slot (wsWords L) 0) ∧ u.mem = s₁.mem) (by
      prun [(k1.gpr _ (by decide)).trans h23, a10, oNLen, hs1.ld (show 16 + 8 ≤ Z by omega_arith), hK',
        BitVec.add_zero, off_off]) rfl) fun s₂ ⟨⟨a25, a14, _⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) xj) fun u ⟨⟨a15, _⟩, k3⟩ => ?_
  simp only [List.map_cons, List.map_nil, a15, k3.gpr .r10 (by decide), k3.gpr .r11 (by decide),
    k3.gpr .r14 (by decide), k3.gpr .r21 (by decide), k3.gpr .r23 (by decide), k3.gpr .r25 (by decide),
    k3.gpr .r27 (by decide), k3.gpr .r28 (by decide), k3.gpr .r29 (by decide), k2.gpr .r10 (by decide),
    k2.gpr .r11 (by decide), k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r27 (by decide),
    k2.gpr .r28 (by decide), k2.gpr .r29 (by decide), k1.gpr .r23 (by decide), k1.gpr .r27 (by decide),
    k1.gpr .r28 (by decide), a10, a11, a14, a21, a25, a29, h23, h27, h28]

/-- The registers a power's first block leaves public: with `pc`, `r30` too. -/
abbrev pwRegs (pc : Bool) : List Reg :=
  [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29] ++ if pc then [.r30] else []

/-- `setupP` and a power's first block with `r2Ptr pc q`: the registers. -/
theorem pw1G_ok {pc q : Bool} {t : State} {BX : Addr} {Z oA wX xj k L oB oLen pL : Nat} (hs : Scr t BX Z)
    (hZ : 256 ≤ Z) (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : word t.mem BX oB = off BX oA) (hLw : word t.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word t.mem BX oNLen = BitVec.ofNat 64 k) (hL : 1 ≤ L) (hL' : L < 2 ^ 60)
    (hpl : q = true → word t.mem BX oPLen = BitVec.ofNat 64 pL) (hp1 : 1 ≤ pL) (hp2 : pL < 2 ^ 60) :
    WP isa (.seq (.block (setupP oB oLen)) (.block (PW1 xj ++ r2Ptr pc q))) t fun u =>
      (pwRegs pc).map u.gpr =
        [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
          off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
          BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] ++
        if pc then [word t.mem BX oR2 + BitVec.ofNat 64 (if q then 8 * wsWords pL else 0)] else [] := by
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL hZ hB hLw hL hL') fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  have hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by rw [m1]; exact hK
  have hs1 := hs.congr k1.wr
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 k ∧
    u.gpr .r14 = off BX (oA + slot (wsWords L) 0) ∧ u.mem = s₁.mem) (by
      prun [(k1.gpr _ (by decide)).trans h23, a10, oNLen, hs1.ld (show 16 + 8 ≤ Z by omega_arith), hK',
        BitVec.add_zero, off_off]) rfl) fun s₂ ⟨⟨a25, a14, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) xj) fun u' ⟨⟨a15, m3⟩, k3⟩ => ?_
  have hu' : [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29].map u'.gpr =
      [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
        off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
        BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] := by
    simp only [List.map_cons, List.map_nil, a15, k3.gpr .r10 (by decide), k3.gpr .r11 (by decide),
      k3.gpr .r14 (by decide), k3.gpr .r21 (by decide), k3.gpr .r23 (by decide), k3.gpr .r25 (by decide),
      k3.gpr .r27 (by decide), k3.gpr .r28 (by decide), k3.gpr .r29 (by decide), k2.gpr .r10 (by decide),
      k2.gpr .r11 (by decide), k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r27 (by decide),
      k2.gpr .r28 (by decide), k2.gpr .r29 (by decide), k1.gpr .r23 (by decide), k1.gpr .r27 (by decide),
      k1.gpr .r28 (by decide), a10, a11, a14, a21, a25, a29, h23, h27, h28]
  cases pc
  · exact WP.block_nil_iff.mpr (by simpa only [pwRegs, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hu')
  · have m' : u'.mem = t.mem := by rw [m3, m2, m1]
    have k' := k12.trans k3
    refine WP.mono (r2Src_ok (hs.congr k'.wr) hZ ((k'.gpr _ (by decide)).trans h23)
      (fun hq => by rw [m']; exact hpl hq) hp1 hp2) fun u ⟨⟨a30, _⟩, k4⟩ => ?_
    simp only [pwRegs, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, a30, m']
    rw [← hu']
    congr 1
    simp only [List.map_cons, List.map_nil, k4.gpr .r10 (by decide), k4.gpr .r11 (by decide),
      k4.gpr .r14 (by decide), k4.gpr .r15 (by decide), k4.gpr .r21 (by decide), k4.gpr .r23 (by decide),
      k4.gpr .r25 (by decide), k4.gpr .r27 (by decide), k4.gpr .r28 (by decide), k4.gpr .r29 (by decide)]

/-- Two header words into `ra` and `rb`, for `r12` and `r6` or `r30` and `r31`. -/
theorem hdr2_ok {t : State} {BX : Addr} {Z oA oB : Nat} {va vb : BitVec 64} (hs : Scr t BX Z) (hZ : 256 ≤ Z)
    (h23 : t.gpr .r23 = BX) (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0)
    (hA : word t.mem BX oA = va) (hB : word t.mem BX oB = vb) :
    (WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oB]) t fun u =>
      (u.gpr .r12 = va ∧ u.gpr .r6 = vb ∧ u.mem = t.mem) ∧ Keep [.r12, .r6] t u) ∧
    (WP isa (.block [.load .d .r30 .r23 oA, .load .d .r31 .r23 oB]) t fun u =>
      (u.gpr .r30 = va ∧ u.gpr .r31 = vb ∧ u.mem = t.mem) ∧ Keep [.r30, .r31] t u) := by
  have hA' : t.mem.readW (off BX oA) 64 = va := hA
  have hB' : t.mem.readW (off BX oB) 64 = vb := hB
  refine ⟨WP.keep _ ?_ rfl, WP.keep _ ?_ rfl⟩ <;>
  prun [h23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oA < 2 ^ 15 by omega_arith, show oA % 4 = 0 by omega_arith⟩,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oB < 2 ^ 15 by omega_arith, show oB % 4 = 0 by omega_arith⟩,
    hs.ld (show oA + 8 ≤ Z by omega_arith), hs.ld (show oB + 8 ≤ Z by omega_arith), hA', hB']

/-- What two initial states with the same public data share, of the layout. -/
theorem layout_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') :
    cS s₀ = cS s₀' ∧ cwX s₀ = cwX s₀' ∧ cwP s₀ = cwP s₀' ∧ cwQ s₀ = cwQ s₀' ∧ oPa s₀ = oPa s₀' ∧
      oQa s₀ = oQa s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' := by
  obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
  simp only [cwX, cwP, cwQ, oPa, oQa, eS, ek, ep, eq, and_self]

/-- The cut index of `crt` (`a`), or with `pc` of `crtP` (`b`). -/
abbrev ix (pc : Bool) (a b : Nat) : Nat := if pc then b else a

/-- With `pc`, the cached values (`R2F`) and the header's word of their address. -/
theorem c0_r2 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s : State} (h : C0 pc d s₀)
    (hhd : pc = true → word s.mem (cS s₀) oR2 = s₀.gpr .r31) :
    pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31 := fun hp => by
  subst hp; exact ⟨r2F_of h.1, hhd rfl⟩

/-- The front, `loadX` and `checks`, then `c`. -/
abbrev NA (pc : Bool) (c : Prog isa) : Prog isa := .seq (.block (Crt.save ++ argsG pc ++ setupX)) (.seq loadX (.seq checks c))

/-- Then `loadIn`. -/
abbrev NL (pc : Bool) (c : Prog isa) : Prog isa := NA pc (.seq loadIn c)

theorem pins91 : Pins (At (C0 pc) (crtF pc) 91) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r7) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := NA pc (LD oIn oNLen)) (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => by
        have hP := pre_factsG (preG_core h.1)
        have hn := hP.nw; have room := hP.room
        have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
        refine mid1A_ok hP F fun t X a10 k1 => ?_
        have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
          X.out.word (Or.inl hd) (by omega_arith)
        refine WP.mono (hdr2_ok (va := off (s₀.gpr .r7) 0) (vb := BitVec.ofNat 64 (ck s₀)) (F.scr.congr k1.wr) (by omega_arith) ((k1.gpr _ (by decide)).trans F.r23)
          (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hIn) (by rw [hd _ (by decide)]; exact F.hNL)).1
          fun u ⟨⟨a12, a6, _⟩, k2⟩ => ?_
        simp only [ldVals, List.map_cons, List.map_nil, a12, a6, k2.gpr .r10 (by decide), k2.gpr .r11 (by decide),
          k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r29 (by decide), a10,
          (k1.gpr .r11 (by decide)).trans F.r11, (k1.gpr .r21 (by decide)).trans F.r21,
          (k1.gpr .r23 (by decide)).trans F.r23, (k1.gpr .r29 (by decide)).trans F.r29])))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.1 E.2.1

/-- A power's head, then `c`. -/
abbrev PH (pc q : Bool) (xj : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block (PW1 xj ++ r2Ptr pc q)) (.seq copyN (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++
    PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3)) (.seq (r2Step pc) (.seq reduceIn c))))

theorem pins100 : Pins (At (C0 pc) (crtF pc) 100) (pwRegs pc) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (cS s₀) (oPa s₀ + slot (cwP s₀) 0), off (cS s₀) (slot (cwX s₀) 4),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2))] ++
      if pc then [s₀.gpr .r31] else [])
    (fun _ s₀ h => WP.of_flat (c := NL pc (.seq (.block (setupP oBP oPLen)) (.block (PW1 4 ++ r2Ptr pc false))))
      (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t X _ k1 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      X.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (pw1G_ok (pc := pc) (q := false) (pL := 1) (F.scr.congr k1.wr) (by omega_arith)
      ((k1.gpr _ (by decide)).trans F.r23)
      ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL)
      (by rw [hd _ (by decide)]; exact F.hNL) p1 (by omega_arith) nofun (Nat.le_refl _) (by decide)) fun u hu => ?_
    rw [hu]
    cases pc
    · rfl
    · rw [hd oR2 (by unfold oR2; omega_arith), hhd rfl]
      simp only [↓reduceIte, Bool.false_eq_true, BitVec.add_zero]
  · obtain ⟨eS, eX, eP, -, eoP, -, ek, -, -⟩ := layout_eq h h'
    have E := two_data h h'
    cases pc
    · simp only [eS, eX, eP, eoP, ek, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eoP, ek, E.r31 rfl, ↓reduceIte]

/-- The front through `p`'s power head and its exponent's registers. -/
theorem pins124 : Pins (At (C0 pc) (crtF pc) (ix pc 124 118)) [.r10, .r11, .r23, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwP s₀ + 2)), off (stackArg s₀ 2) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NL pc (.seq (.block (setupP oBP oPLen))
      (PH pc false 4 (.block [.load .d .r30 .r23 oDP, .load .d .r31 .r23 oPLen])))) (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have pq := hP.pq
    have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24; have fP8 := e (wsWords (cpL s₀)) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
    obtain ⟨_, mPo, _, _, mPb, _, _, _, _⟩ := masked_facts hP
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t X _ k1 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      X.out.word (Or.inl hd) (by omega_arith)
    refine phasePA_ok (q := false) (hR2 := fun hp => by
      subst hp; exact ⟨_, _, _, (c0_r2 h hhd rfl).1.p hP F (c0_r2 h hhd rfl).2 X.out
        (by rw [k1.rd, k1.wr, F.keep.rd, F.keep.wr]) X.r26⟩) (wX := cwX s₀) (xj := 4) (oA := oPa s₀) (L := cpL s₀) (k := ck s₀) (Pv := mP s₀) (Cv := vC s₀)
      (F.scr.congr k1.wr) (by omega_arith) (Nat.le_refl _) rfl (by unfold wsWords; omega_arith) hwX (by decide)
      ((k1.gpr _ (by decide)).trans F.r23) ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28)
      (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL)
      (by rw [hd _ (by decide)]; exact F.hNL) p1 (by omega_arith) (by omega_arith) (by omega_arith)
      X.v4 mPb (by have := (masked_facts hP).1; omega_arith) mPo X.v6
      (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) fun u out u10 u11 _ u29 ku => ?_
    have hdu : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.mono (hdr2_ok (va := off (stackArg s₀ 2) 0) (vb := BitVec.ofNat 64 (cpL s₀)) ((F.scr.congr k1.wr).congr ku.wr) (by omega_arith)
      ((ku.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans F.r23)) (by decide) (by decide)
      (by rw [hdu _ (by decide)]; exact F.hDP) (by rw [hdu _ (by decide)]; exact F.hPL)).2
      fun v ⟨⟨v30, v31, _⟩, kv⟩ => ?_
    simp only [List.map_cons, List.map_nil, v30, v31, kv.gpr .r10 (by decide), kv.gpr .r11 (by decide),
      kv.gpr .r23 (by decide), kv.gpr .r29 (by decide), u10, u11, u29, ku.gpr .r23 (by decide),
      (k1.gpr .r23 (by decide)).trans F.r23]
  · obtain ⟨eS, -, eP, -, eoP, -, -, ep, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, -, -, -, e2, -⟩ := data_vals h h'
    simp only [eS, eP, eoP, ep, e2]

/-- The phases through `p`'s power, then `c`. -/
abbrev NP (pc : Bool) (c : Prog isa) : Prog isa :=
  NL pc (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen) c))

theorem pins148 : Pins (At (C0 pc) (crtF pc) (ix pc 148 142)) (pwRegs pc) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), BitVec.ofNat 64 (2 * cwQ s₀),
      off (cS s₀) (oQa s₀ + slot (cwQ s₀) 0), off (cS s₀) (slot (cwX s₀) 5),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), cS s₀, BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwQ s₀ + 2))] ++
      if pc then [s₀.gpr .r31 + BitVec.ofNat 64 (8 * cwP s₀)] else [])
    (fun _ s₀ h => WP.of_flat (c := NP pc (.seq (.block (setupP oBQ oQLen)) (.block (PW1 5 ++ r2Ptr pc true))))
      (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have p1 := hP.p1; have pk := hP.pk
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t₁ X _ k1 => mid1B_ok hP F (c0_r2 h hhd) X k1 (by decide) (by decide) (by decide) fun t Y k2 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      Y.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (pw1G_ok (pc := pc) (q := true) (pL := cpL s₀) (F.scr.congr k2.wr) (by omega_arith)
      ((k2.gpr _ (by decide)).trans F.r23)
      ((k2.gpr _ (by decide)).trans F.r27) ((k2.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL)
      (by rw [hd _ (by decide)]; exact F.hNL) q1 (by omega_arith)
      (fun _ => by rw [hd oPLen (by unfold oPLen; omega_arith)]; exact F.hPL) p1 (by omega_arith)) fun u hu => ?_
    rw [hu]
    cases pc
    · rfl
    · rw [hd oR2 (by unfold oR2; omega_arith), hhd rfl]
      simp only [↓reduceIte]
  · obtain ⟨eS, eX, eP, eQ, -, eoQ, ek, -, -⟩ := layout_eq h h'
    have E := two_data h h'
    cases pc
    · simp only [eS, eX, eQ, eoQ, ek, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eQ, eoQ, ek, E.r31 rfl, ↓reduceIte]

theorem pins172 : Pins (At (C0 pc) (crtF pc) (ix pc 172 160)) [.r10, .r11, .r23, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwQ s₀ + 2)), off (stackArg s₀ 4) 0, BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NP pc (.seq (.block (setupP oBQ oQLen))
      (PH pc true 5 (.block [.load .d .r30 .r23 oDQ, .load .d .r31 .r23 oQLen])))) (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have pq := hP.pq
    have k64 := hP.k64; have k1024 := hP.k1024; have q1 := hP.q1; have qk := hP.qk
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX8 := e (cwX s₀) 8; have eQ8 := e (cwQ s₀) 24; have eP8 := e (cwP s₀) 24
    have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
    obtain ⟨_, _, _, mQo, _, mQb, _, _, _⟩ := masked_facts hP
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t₁ X _ k1 => mid1B_ok hP F (c0_r2 h hhd) X k1 (by decide) (by decide) (by decide) fun t Y k2 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      Y.out.word (Or.inl hd) (by omega_arith)
    refine phasePA_ok (q := true) (hR2 := fun hp => by
      subst hp; exact ⟨_, _, _, (c0_r2 h hhd rfl).1.q hP F (c0_r2 h hhd rfl).2 Y.out
        (by rw [k2.rd, k2.wr, F.keep.rd, F.keep.wr]) Y.r26⟩) (wX := cwX s₀) (xj := 5) (oA := oQa s₀) (L := cqL s₀) (k := ck s₀) (Pv := mQ s₀) (Cv := vC s₀)
      (F.scr.congr k2.wr) (by omega_arith) (by omega_arith) rfl (by unfold wsWords; omega_arith) hwX (by decide)
      ((k2.gpr _ (by decide)).trans F.r23) ((k2.gpr _ (by decide)).trans F.r27) ((k2.gpr _ (by decide)).trans F.r28)
      (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL)
      (by rw [hd _ (by decide)]; exact F.hNL) q1 (by omega_arith) (by omega_arith) (by omega_arith)
      Y.v5 mQb (by have := (masked_facts hP).2.2.1; omega_arith) mQo Y.v6
      (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) fun u out u10 u11 _ u29 ku => ?_
    have hdu : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.mono (hdr2_ok (va := off (stackArg s₀ 4) 0) (vb := BitVec.ofNat 64 (cqL s₀)) ((F.scr.congr k2.wr).congr ku.wr) (by omega_arith)
      ((ku.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans F.r23)) (by decide) (by decide)
      (by rw [hdu _ (by decide)]; exact F.hDQ) (by rw [hdu _ (by decide)]; exact F.hQL)).2
      fun v ⟨⟨v30, v31, _⟩, kv⟩ => ?_
    simp only [List.map_cons, List.map_nil, v30, v31, kv.gpr .r10 (by decide), kv.gpr .r11 (by decide),
      kv.gpr .r23 (by decide), kv.gpr .r29 (by decide), u10, u11, u29, ku.gpr .r23 (by decide),
      (k2.gpr .r23 (by decide)).trans F.r23]
  · obtain ⟨eS, -, -, eQ, -, eoQ, -, -, eq⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, e4, -⟩ := data_vals h h'
    simp only [eS, eQ, eoQ, eq, e4]

/-- The phases through both powers, then `c`. -/
abbrev NQ (pc : Bool) (c : Prog isa) : Prog isa :=
  NP pc (.seq (.block (setupP oBQ oQLen)) (.seq (powerG pc true 5 oDQ oQLen) c))

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
    prun [a15, (k1.gpr .r23 (by decide)).trans h23, oQLen, (hx.congr k1.wr).ld (show 56 + 8 ≤ Z by omega_arith), hL',
      off_add, BitVec.add_zero]
    rw [off_sub1 _ (by omega_arith)]; congr 2; omega_arith
  have k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r16) (by decide) (by decide) (k12.gpr _ (by decide) |>.trans h27)
    (k12.gpr _ (by decide) |>.trans h28) 1) fun u ⟨⟨b16, _⟩, k3⟩ => ?_
  simp only [List.map_cons, List.map_nil, b16, k3.gpr .r15 (by decide), k3.gpr .r17 (by decide),
    k3.gpr .r23 (by decide), (k12.gpr .r23 (by decide)).trans h23, b15, b17]

theorem pins195 : Pins (At (C0 pc) (crtF pc) (ix pc 195 183)) [.r15, .r16, .r17, .r23] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4 + (cqL s₀ - 1)),
      off (cS s₀) (slot (cwX s₀) 1), BitVec.ofNat 64 (cqL s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := NQ pc (.block EX1)) (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1_ok hP F (c0_r2 h hhd) fun t _ _ _ _ _ _ _ _ t10 t29 O1 k1 => ?_
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega_arith)
    exact ex1_ok (F.scr.congr k1.wr) (by omega_arith) t10 t29 ((k1.gpr _ (by decide)).trans F.r23)
      ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28)
      (by rw [hd _ (by decide)]; exact F.hQL) q1
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, eq⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ, eq]

/-- `m₂`'s export and `p`'s registers, then `c`. -/
abbrev NE (pc : Bool) (c : Prog isa) : Prog isa := NQ pc (.seq exportM2 (.seq (.block (setupP oBP oPLen)) c))

theorem pins198 : Pins (At (C0 pc) (crtF pc) (ix pc 198 186))
    ([.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r31] ++ if pc then [.r30] else []) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2)), BitVec.ofNat 64 (cqL s₀)] ++
      if pc then [s₀.gpr .r31] else [])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.block ([.load .d .r31 .r23 oQLen] ++ r2Ptr pc false)))
      (by cases pc <;> decide +kernel)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    have hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have p1 := hP.p1; have pk := hP.pk
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX1 := e (cwX s₀) 1; have eX8 := e (cwX s₀) 8; have eQ8 := e (cwQ s₀) 24; have eP8 := e (cwP s₀) 24
    have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
    have hwQ : cwQ s₀ ≤ cwX s₀ := by have := hP.pq; unfold cwQ; omega_arith
    refine mid1_ok hP F (c0_r2 h hhd) fun t _ _ _ _ _ _ _ _ t10 t29 O1 k1 => ?_
    have hs := F.scr.congr k1.wr
    have h23 := (k1.gpr _ (by decide)).trans F.r23
    have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (exportM2_ok (L := cqL s₀) (hs.sub (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith))
      (Scr.le hs (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith)) t10 t29 h23 ((k1.gpr _ (by decide)).trans F.r27)
      ((k1.gpr _ (by decide)).trans F.r28) (by rw [hd _ (by decide)]; exact F.hQL) q1 hqw (by omega_arith)
      (Nat.le_refl _) (Nat.le_refl _) (fun x hx => by
        rcases ofs_rebase (cS s₀) x (o := oQa s₀) (by omega_arith) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith))
      fun u₁ ⟨⟨_, o1⟩, k2⟩ => ?_)
    have hd1 : ∀ d, d + 8 ≤ 256 → word u₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [o1.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.seq (WP.mono (setupP_ok (oA := oPa s₀) (hs.congr k2.wr) ((k2.gpr _ (by decide)).trans h23) (by decide) (by decide)
      (by omega_arith) (by rw [hd1 _ (by decide)]; exact F.hBP) (by rw [hd1 _ (by decide)]; exact F.hPL) p1 (by omega_arith))
      fun u₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k3⟩ => ?_)
    have k23 := k2.trans k3
    have hQL' : u₂.mem.readW (off (cS s₀) 56) 64 = BitVec.ofNat 64 (cqL s₀) := by
      rw [m2]; exact (hd1 56 (by decide)).trans F.hQL
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r31] (Q := fun v => v.gpr .r31 = BitVec.ofNat 64 (cqL s₀) ∧ v.mem = u₂.mem) (by
      prun [(k23.gpr .r23 (by decide)).trans h23, oQLen, ((hs.congr k2.wr).congr k3.wr).ld (show 56 + 8 ≤ cZ s₀ by omega_arith),
        hQL']) rfl) fun v' ⟨⟨a31, mv⟩, k4⟩ => ?_
    have hv' : [Reg.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r31].map v'.gpr =
        [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
          off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0),
          BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2)), BitVec.ofNat 64 (cqL s₀)] := by
      simp only [List.map_cons, List.map_nil, a31, k4.gpr .r10 (by decide), k4.gpr .r11 (by decide),
        k4.gpr .r21 (by decide), k4.gpr .r23 (by decide), k4.gpr .r27 (by decide), k4.gpr .r28 (by decide),
        k4.gpr .r29 (by decide), a10, a11, a21, a29, k23.gpr .r23 (by decide), k23.gpr .r27 (by decide),
        k23.gpr .r28 (by decide), h23, (k1.gpr _ (by decide)).trans F.r27, (k1.gpr _ (by decide)).trans F.r28]
    cases pc
    · exact WP.block_nil_iff.mpr (by simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil] using hv')
    · have k' := k23.trans k4
      refine WP.mono (r2Src_ok (q := false) (pL := 1) ((hs.congr k'.wr)) (by omega_arith)
        ((k'.gpr _ (by decide)).trans h23) nofun (Nat.le_refl _) (by decide)) fun v ⟨⟨a30, _⟩, k5⟩ => ?_
      simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, a30, mv, m2, Bool.false_eq_true,
        BitVec.add_zero]
      rw [hd1 oR2 (by unfold oR2; omega_arith), hhd rfl, ← hv']
      simp only [List.map_cons, List.map_nil, k5.gpr .r10 (by decide), k5.gpr .r11 (by decide),
        k5.gpr .r21 (by decide), k5.gpr .r23 (by decide), k5.gpr .r27 (by decide), k5.gpr .r28 (by decide),
        k5.gpr .r29 (by decide), k5.gpr .r31 (by decide)]
  · obtain ⟨eS, eX, eP, -, eoP, -, -, -, eq⟩ := layout_eq h h'
    have E := two_data h h'
    cases pc
    · simp only [eS, eX, eP, eoP, eq, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eoP, eq, E.r31 rfl, ↓reduceIte]

/-- Through `recombineP`, from the initial state. -/
theorem pre_rec {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀)
    (hc : ∀ s u, PF s₀ → Front s₀ s → XR s₀ s u →
      Keep (mid1Regs ++ (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs)) s u → WP isa c u Q) :
    WP isa (NE pc (.seq (recombinePG pc) c)) s₀ Q :=
  WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ =>
    mid1_ok (pre_factsG (preG_core h.1)) F (c0_r2 h hhd) fun _ t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 =>
      mid2A_ok (pre_factsG (preG_core h.1)) F (c0_r2 h hhd) t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 fun u R k => hc s u (pre_factsG (preG_core h.1)) F R k)

/-- `recombineX`'s first block. -/
abbrev X1 : List Instr :=
  setupP oBP oPLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0, .lsl .r11 .r4 1] ++ xb .r14 7 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

/-- `recombineX`'s second block. -/
abbrev X2 : List Instr :=
  setupP oBQ oQLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0] ++ xb .r14 6 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

theorem pins233 : Pins (At (C0 pc) (crtF pc) (ix pc 233 215)) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 7),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4), BitVec.ofNat 64 (2 * cwP s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.block X1))) (by cases pc <;> decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega_arith)))
      (F.scr.congr k.wr) ((k.gpr _ (by decide)).trans F.r23) (by decide) (by decide) (by omega_arith)
      (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega_arith)
      (by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith) ((k.gpr _ (by decide)).trans F.r27) ((k.gpr _ (by decide)).trans F.r28))
      fun v ⟨⟨a14, a11, a22, a15, _⟩, k'⟩ => ?_
    simp only [List.map_cons, List.map_nil, a14, a11, a22, a15, k'.gpr .r23 (by decide), k'.gpr .r27 (by decide),
      k'.gpr .r28 (by decide), (k.gpr _ (by decide)).trans F.r23, (k.gpr _ (by decide)).trans F.r27,
      (k.gpr _ (by decide)).trans F.r28]
  · obtain ⟨eS, eX, eP, -, eoP, -, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eP, eoP]

theorem pins239 : Pins (At (C0 pc) (crtF pc) (ix pc 239 221)) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 6),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.seq (.block X1) (.seq (.seq Precompute.zeroWords
      (.seq (.block (xb .r14 7 ++ [.addi .r11 .r22 0])) copyN)) (.block X2))))) (by cases pc <;> decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24
    have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    have hwP : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
    have hs := F.scr.congr k.wr
    have h23 := (k.gpr _ (by decide)).trans F.r23
    have h27 := (k.gpr _ (by decide)).trans F.r27
    have h28 := (k.gpr _ (by decide)).trans F.r28
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega_arith)))
      hs h23 (by decide) (by decide) (by omega_arith) (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega_arith) hwX h27 h28)
      fun v₁ ⟨⟨a14, a11, a22, a15, m1⟩, k1⟩ => ?_)
    refine WP.seq (WP.mono (xfer_ok (hs.congr k1.wr) (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith)
      (Nat.le_of_eq doP.symm) (by decide) (by omega_arith) (by omega_arith) hwX a14 a11 a22 a15
      ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28)) fun v₂ ⟨⟨_, out2⟩, k2⟩ => ?_)
    have k12 := k1.trans k2
    have hd2 : ∀ d, d + 8 ≤ 256 → word v₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out2.word (Or.inl (by omega_arith)) (by omega_arith), m1]; exact hd d hd'
    refine WP.mono (blk_ok (j := 6) (oA := oQa s₀) _ (fun t h11 _ => midQ_ok h11) (hs.congr k12.wr)
      ((k12.gpr _ (by decide)).trans h23) (by decide) (by decide) (by omega_arith)
      (by rw [hd2 _ (by decide)]; exact F.hBQ) (by rw [hd2 _ (by decide)]; exact F.hQL) q1 (by omega_arith) hwX
      ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28))
      fun v ⟨⟨b14, b11, b22, b15, _⟩, k3⟩ => ?_
    simp only [List.map_cons, List.map_nil, b14, b11, b22, b15, k3.gpr .r23 (by decide), k3.gpr .r27 (by decide),
      k3.gpr .r28 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide), k12.gpr .r28 (by decide),
      h23, h27, h28]
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ]

/-- The output's registers. -/
abbrev FIN : List Instr := [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen]

theorem pins252 : Pins (At (C0 pc) (crtF pc) (ix pc 252 234)) [.r10, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), cS s₀, off (s₀.gpr .r3) 0,
      BitVec.ofNat 64 (ck s₀), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.seq recombineX (.block FIN)))) (by cases pc <;> decide +kernel)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX2 := e (cwX s₀) 2; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24
    have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    have hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    obtain ⟨-, -, -, -, -, mQb, -⟩ := masked_facts hP
    have hs := F.scr.congr k.wr
    have h23 := (k.gpr _ (by decide)).trans F.r23
    have h27 := (k.gpr _ (by decide)).trans F.r27
    have h28 := (k.gpr _ (by decide)).trans F.r28
    have hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (recombineX_ok (oP := oPa s₀) (oQ := oQa s₀) hs (by omega_arith) (Nat.le_of_eq doP.symm)
      (by omega_arith) (by omega_arith) pq hwX h23 h27 h28 (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) (by rw [hd _ (by decide)]; exact F.hBQ)
      (by rw [hd _ (by decide)]; exact F.hQL) p1 (by omega_arith) q1 (by omega_arith) R.v0 R.w0 R.v5 mQb R.h4 R.q4)
      fun v₁ ⟨⟨_, o1⟩, k1⟩ => ?_)
    have O1 : Outside (cS s₀) (slot (cwX s₀) 2) (6 * (8 * (cwX s₀ + 2))) u.mem v₁.mem := by
      intro x hx
      refine o1 x fun r hr => ?_
      change ofs (cS s₀) x < r.1 ∨ r.1 + r.2 ≤ ofs (cS s₀) x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      change ofs (cS s₀) x < slot (cwX s₀) 2 ∨ slot (cwX s₀) 2 + 6 * (8 * (cwX s₀ + 2)) ≤ ofs (cS s₀) x at hx
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp only [e] at hx ⊢ <;> omega_arith
    have hd1 : ∀ d, d + 8 ≤ 256 → word v₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [O1.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    have hs1 := hs.congr k1.wr
    have e0 : off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
    have hO' : v₁.mem.readW (cS s₀) 64 = off (s₀.gpr .r3) 0 := by
      have h0 : word v₁.mem (cS s₀) 0 = off (s₀.gpr .r3) 0 := (hd1 0 (by decide)).trans F.hOut
      rw [← e0]; exact h0
    have ld0 : InRegions (v₁.rd ++ v₁.wr) (cS s₀) 8 := by
      have e0' : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
      have := hs1.ld (show 0 + 8 ≤ cZ s₀ by omega_arith); rwa [e0'] at this
    have hK' : v₁.mem.readW (off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) := by
      show word v₁.mem (cS s₀) 16 = _; rw [hd1 16 (by decide)]; exact F.hNL
    refine WP.mono (WP.keep [.r10, .r29, .r27, .r28] (Q := fun t =>
      t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) ∧
        t.gpr .r27 = off (s₀.gpr .r3) 0 ∧ t.gpr .r28 = BitVec.ofNat 64 (ck s₀)) (by
      prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28,
        (k1.gpr .r23 (by decide)).trans h23, oOut, oNLen, ld0, hs1.ld (show 16 + 8 ≤ cZ s₀ by omega_arith), hO', hK',
        BitVec.add_zero]) (by decide)) fun v ⟨⟨a10, a29, a27, a28⟩, k2⟩ => ?_
    simp only [List.map_cons, List.map_nil, a10, a29, a27, a28, k2.gpr .r23 (by decide), k1.gpr .r23 (by decide),
      h23]
  · obtain ⟨eS, eX, -, -, -, -, ek, -, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, e3, -⟩ := data_vals h h'
    simp only [eS, eX, ek, e3]

end VG.Proof.Bignum.PPC64LE.Crt
