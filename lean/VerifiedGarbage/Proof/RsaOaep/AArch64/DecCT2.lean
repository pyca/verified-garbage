module

import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSAES-OAEP decryption on AArch64: the decoding in constant time

`decMain` from two runs in the same frame and working space, with the label,
`out`, `*msg_len` and `k` the same in both (`DecX`): the label's hash and
MGF1 as for any caller, the loops from the registers their heads fix
(`*_pin`), and the blocks by the taint analysis (`decMain_tr`). Between the
scan and the shift, each run also keeps the index the scan found and the
zeros after the buffer's first 1024 bytes, which the shift's correctness
needs.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-- Where the label, `out` and `*msg_len` are, `k` in its slot, and the
hash functions' numbers and lengths in theirs. -/
def DecX (F S : Addr) (k : Nat) (lab : Addr) (labLen : Nat) (o ml : Addr) (kH DH kG DG : Nat)
    (W : Nat → BitVec 64) (t : State) : Prop :=
  LabAt t F S W lab labLen ∧ OutAt t F S W o ml k ∧ W 21 = BitVec.ofNat 64 k ∧ HSlots W kH DH kG DG

theorem DecX.step {F S : Addr} {k : Nat} {lab : Addr} {labLen : Nat} {o ml : Addr} {kH DH kG DG : Nat}
    {W W' : Nat → BitVec 64} {t u : State} (h : DecX F S k lab labLen o ml kH DH kG DG W t) {ws : List Region}
    (hS : Step F S ws t u) (hW : ∀ j, (j = 19 ∨ j = 21 ∨ (25 ≤ j ∧ j ≤ 27) ∨ (2 ≤ j ∧ j ≤ 5)) → W' j = W j) :
    DecX F S k lab labLen o ml kH DH kG DG W' u :=
  ⟨h.1.congr hS.rd hS.wr (hW 25 (by omega)) (hW 26 (by omega)),
    h.2.1.congr hS.wr (hW 19 (by omega)) (hW 27 (by omega)), (hW 21 (by omega)).trans h.2.2.1,
    h.2.2.2.of_eq fun j h1 h2 => hW j (by omega)⟩

/-! ## The loops' heads -/

section
variable {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
  (R : Rep u.mem F S V W)
include L

include R in
theorem accA_pin {D : Nat} (hl : W 4 = BitVec.ofNat 64 D) :
    WP isa (.block (scr .x11 oLh ++ ([.ldrSp .x13 sHl] : List Instr) ++ scr .x12 (oEm + 1) ++
      ([.add .x .x12 .x12 .x13] : List Instr) ++ scr .x10 oEm)) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x10, .x11, .x12, .x13], u'.gpr r =
        ([(Reg.x10, off S oEm), (.x11, off S oLh), (.x12, off S (oEm + 1 + D)), (.x13, BitVec.ofNat 64 D)].lookup r).getD
          0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h32 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 32) 8 := L.ld (d := 32) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rl := R.rd8 (d := 32) (k := 4) rfl (by decide) hl
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x10 = off S oEm ∧ u'.gpr .x11 = off S oLh ∧
      u'.gpr .x12 = off S (oEm + 1 + D) ∧ u'.gpr .x13 = BitVec.ofNat 64 D) ?_
    fun u' ⟨hs, x10, x11, x12, x13⟩ => pin_list [(Reg.x10, off S oEm), (.x11, off S oLh),
      (.x12, off S (oEm + 1 + D)), (.x13, BitVec.ofNat 64 D)]
      hs (by simp only [List.mem_cons, List.not_mem_nil, or_false]
             rintro p (rfl | rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, lay, sScr, sHl, h96, h32, L.sp, hs, rl, show oLh < 4096 by decide,
    show oEm + 1 < 4096 by decide, show oEm < 4096 by decide, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

include R in
theorem scanA_pin {D : Nat} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hl : W 4 = BitVec.ofNat 64 D)
    (hD : 2 * D + 2 ≤ k) :
    WP isa (.block (tArgs ++ ([.movz .x .x13 0 0, .subImm .x .x13 .x13 1, .movz .x .x8 0 0, .ldrSp .x14 sAcc,
      .movz .x .x9 0 0, .movz .x .x17 1 0] : List Instr))) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x11, .x12], u'.gpr r =
        ([(Reg.x11, off S (1 + 2 * D)), (.x12, BitVec.ofNat 64 (k - 2 * D - 1))].lookup r).getD 0 :=
  WP.mono (scanHead_ok L R hk hl hD) fun u' I => pin_list [(Reg.x11, off S (1 + 2 * D)),
    (.x12, BitVec.ofNat 64 (k - 2 * D - 1))] (I.st.sp) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact I.x11.trans (by rw [Nat.add_zero])
      · exact I.x12.trans (by rw [Nat.sub_zero]))

theorem clearA_pin :
    WP isa (.block (scr .x11 oBuf ++ ([.movz .x .x12 256 0, .movz .x .x13 0 0] : List Instr))) u fun u' =>
      u'.sp = u.sp ∧ ∀ r ∈ [Reg.x11, .x12], u'.gpr r =
        ([(Reg.x11, off S oBuf), (.x12, BitVec.ofNat 64 256)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = BitVec.ofNat 64 256) ?_
    fun u' ⟨hs, x11, x12⟩ => pin_list [(Reg.x11, off S oBuf), (.x12, BitVec.ofNat 64 256)] hs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, lay, sScr, oBuf, h96, L.sp, hs]
  oaep_fin

include R in
theorem copyA_pin {D : Nat} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hl : W 4 = BitVec.ofNat 64 D)
    (hD : 2 * D + 2 ≤ k) :
    WP isa (.block (tArgs ++ ([mov .x13 .x12, mov .x10 .x11] : List Instr) ++ scr .x12 oBuf ++
      ([mov .x11 .x10] : List Instr))) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r = ([(Reg.x11, off S (1 + 2 * D)), (.x12, off S oBuf),
        (.x13, BitVec.ofNat 64 (k - (2 * D + 1)))].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  have h32 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 32) 8 := L.ld (d := 32) (by decide)
  have rl := R.rd8 (d := 32) (k := 4) rfl (by decide) hl
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = off S (1 + 2 * D) ∧
      u'.gpr .x12 = off S oBuf ∧ u'.gpr .x13 = BitVec.ofNat 64 (k - (2 * D + 1))) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, off S (1 + 2 * D)), (.x12, off S oBuf),
      (.x13, BitVec.ofNat 64 (k - (2 * D + 1)))] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [tArgs, mov, scr, Mgf1.scr, lay, sScr, sK, sHl, oBuf, oEm, h96, h168, h32, L.sp, hs, rk, rl,
    Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 1 + (D + D) = 1 + 2 * D by omega,
    Offset.ofNat_sub_ofNat (show D + D ≤ k by omega), Offset.ofNat_sub_ofNat (show 1 ≤ k - (D + D) by omega),
    show k - (D + D) - 1 = k - (2 * D + 1) by omega, BitVec.or_self]

theorem shiftA_pin :
    WP isa (.block (scr .x17 oBuf ++ ([.ldrSp .x9 sIdx, .addImm .x .x9 .x9 1, .movz .x .x14 1 0,
      .movz .x .x8 10 0] : List Instr))) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x17, .x14, .x8], u'.gpr r = ([(Reg.x17, off S oBuf), (.x14, BitVec.ofNat 64 1),
        (.x8, BitVec.ofNat 64 10)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h240 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 240) 8 := L.ld (d := 240) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x14 = BitVec.ofNat 64 1 ∧ u'.gpr .x8 = BitVec.ofNat 64 10) ?_
    fun u' ⟨hs, x17, x14, x8⟩ => pin_list [(Reg.x17, off S oBuf), (.x14, BitVec.ofNat 64 1),
      (.x8, BitVec.ofNat 64 10)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, lay, sScr, sIdx, oBuf, h96, h240, L.sp, hs]
  oaep_fin

include R in
theorem outA_pin {o : Addr} {k : Nat} (ho : W 19 = o) (hk : W 21 = BitVec.ofNat 64 k) :
    WP isa (.block (scr .x12 oBuf ++ ([.ldrSp .x11 sOut, .ldrSp .x13 sK, .ldrSp .x15 sOk] : List Instr))) u
      fun u' => u'.sp = u.sp ∧ ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r =
        ([(Reg.x11, o), (.x12, off S oBuf), (.x13, BitVec.ofNat 64 k)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h152 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h248 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 248) 8 := L.ld (d := 248) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) ho
  have rk := R.rdK hk
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = o ∧ u'.gpr .x12 = off S oBuf ∧
      u'.gpr .x13 = BitVec.ofNat 64 k) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, o), (.x12, off S oBuf), (.x13, BitVec.ofNat 64 k)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, lay, sScr, sOut, sK, sOk, oBuf, h96, h152, h168, h248, L.sp, hs, ro, rk]

include R in
theorem retA_pin {ml : Addr} (hml : W 27 = ml) :
    WP isa (.block [.ldrSp .x14 sOk, .ldrSp .x10 sK, .ldrSp .x12 sHl, .sub .x .x10 .x10 .x12, .sub .x .x10 .x10 .x12,
      .subImm .x .x10 .x10 2, .ldrSp .x11 sIdx, .sub .x .x10 .x10 .x11, .logic .and .x .x10 .x10 .x14,
      .ldrSp .x11 sMl]) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x11], u'.gpr r = ml := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h216 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have h240 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 240) 8 := L.ld (d := 240) (by decide)
  have h248 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 248) 8 := L.ld (d := 248) (by decide)
  have h32 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 32) 8 := L.ld (d := 32) (by decide)
  have rml := R.rd8 (d := 216) (k := 27) rfl (by decide) hml
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = ml) ?_
    fun u' ⟨hs, x11⟩ => ⟨hs, fun r hr => by rw [List.mem_singleton.mp hr]; exact x11⟩
  oaep_run [sOk, sK, sIdx, sMl, sHl, h168, h216, h240, h248, h32, L.sp, rml]

end

/-! ## The decoding -/

variable {hs : List Hash} {kH kG : Nat} {Hl Gm : Hash} (hnH : Num hs kH Hl) (hnG : Num hs kG Gm)
  (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

/-- Each run's index from the scan. -/
def IdxX (W : Nat → BitVec 64) : Prop := ∃ idx, W 30 = BitVec.ofNat 64 idx ∧ idx + 1 < 1024

/-- Zeros after the buffer's first 1024 bytes. -/
def ZX (S : Addr) (t : State) : Prop := ∀ x, 1024 ≤ x → x < 2048 → t.mem (off S (oBuf + x)) = 0

include hnH hnG hH hG in
theorem decMain_tr {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs)
    {F S : Addr} {k : Nat} {lab : Addr} {labLen : Nat} {o ml : Addr} (hD : 2 * Hl.D + 2 ≤ k) (hk' : k ≤ 1024)
    (hlen : labLen < 2 ^ 64) :
    RelCT isa (LR F S (DecX F S k lab labLen o ml kH Hl.D kG Gm.D)) (decMain hs) fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have cB : oBuf = 1024 := rfl
  have f2 : MFit (1 + Hl.D) (k - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  have f4 : MFit 1 Hl.D (1 + Hl.D) (k - Hl.D - 1) :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- The label's hash.
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D) (hashLabel_tr hnH hH hlen (.inr rfl) fun _ _ h => ⟨h.1, h.2.2.2.hsel⟩)
    fun t V W L R hx => WP.mono (hashLabel_ok hnH hH (Hs := Hs) hHh L R hx.1 hx.2.2.2.hsel (.inr rfl))
      fun u ⟨Lu, Su, V', Ru, _, _⟩ => ⟨V', W, Lu, Ru, hx.step Su fun _ _ => rfl⟩).seq ?_
  -- The seed unmasked.
  refine (lr_wp (X' := fun W t => DecX F S k lab labLen o ml kH Hl.D kG Gm.D W t ∧ MArgs W S (1 + Hl.D) (k - Hl.D - 1) 1 Hl.D)
    (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (seedArgs_ok L R hx.2.2.1 hx.2.2.2.hlen hD (by omega) hk' [])
      fun u ⟨Lu, Su, Ru⟩ => ⟨V, _, Lu, Ru, hx.step Su (fun j hj => mW_eq _ _ _ _ _ _ (by omega)),
        mW_args _ _ _ _ _ _⟩).seq ?_
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D)
      (mgfXor_tr hnG hG f2 fun _ _ h => ⟨h.2, h.1.2.2.2.msel⟩)
    fun t V W L R hx => WP.mono (mgfXor_ok hnG hG hGh hGl hGv L R f2 hx.2 hx.1.2.2.2.msel)
      fun u ⟨Lu, Su, V', W', Ru, hW', _⟩ => ⟨V', W', Lu, Ru, hx.1.step Su fun j hj =>
        hW' j (by unfold nW frameBytes; omega) (by omega) (by omega)⟩).seq ?_
  -- `DB` unmasked.
  refine (lr_wp (X' := fun W t => DecX F S k lab labLen o ml kH Hl.D kG Gm.D W t ∧ MArgs W S 1 Hl.D (1 + Hl.D) (k - Hl.D - 1))
    (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (dbArgs_ok L R hx.2.2.1 hx.2.2.2.hlen hD (by omega) hk' [])
      fun u ⟨Lu, Su, Ru⟩ => ⟨V, _, Lu, Ru, hx.step Su (fun j hj => mW_eq _ _ _ _ _ _ (by omega)),
        mW_args _ _ _ _ _ _⟩).seq ?_
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D)
      (mgfXor_tr hnG hG f4 fun _ _ h => ⟨h.2, h.1.2.2.2.msel⟩)
    fun t V W L R hx => WP.mono (mgfXor_ok hnG hG hGh hGl hGv L R f4 hx.2 hx.1.2.2.2.msel)
      fun u ⟨Lu, Su, V', W', Ru, hW', _⟩ => ⟨V', W', Lu, Ru, hx.1.step Su fun j hj =>
        hW' j (by unfold nW frameBytes; omega) (by omega) (by omega)⟩).seq ?_
  -- `lHash'` against `lHash`.
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D) (RelCT.seq_block_append (lr_seq_tr
      [.x10, .x11, .x12, .x13]
      (fun r => ([(Reg.x10, off S oEm), (.x11, off S oLh), (.x12, off S (oEm + 1 + Hl.D)),
        (.x13, BitVec.ofNat 64 Hl.D)].lookup r).getD 0)
      (by taint_decide) (by taint_decide)
      fun t V W L R hx => accA_pin L R hx.2.2.2.hlen))
    fun t V W L R hx => WP.mono (accLh_ok L R hx.2.2.2.hlen (by omega) hD0)
      fun u ⟨Lu, Su, Ru⟩ => ⟨V, _, Lu, Ru, hx.step Su fun j hj => by simp only [upd]; rw [ifn (by omega)]⟩).seq ?_
  -- The scan.
  refine (lr_wp (X' := fun W t => DecX F S k lab labLen o ml kH Hl.D kG Gm.D W t ∧ IdxX W) (lr_seq_tr [.x11, .x12]
      (fun r => ([(Reg.x11, off S (1 + 2 * Hl.D)), (.x12, BitVec.ofNat 64 (k - 2 * Hl.D - 1))].lookup r).getD 0)
      (by taint_decide) (by taint_decide)
      fun t V W L R hx => scanA_pin L R hx.2.2.1 hx.2.2.2.hlen hD)
    fun t V W L R hx => WP.mono (scan_ok L R hx.2.2.1 hx.2.2.2.hlen hD hk') fun u ⟨Lu, Su, Ru⟩ => ⟨V, _, Lu, Ru,
      hx.step Su (fun j hj => by simp only [upd]; rw [ifn (by omega), ifn (by omega)]), by
        obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V Hl.D) (W 29) (k - 2 * Hl.D - 1)
        exact ⟨idx, by simp only [upd, ite_true]; exact hidx, by omega⟩⟩).seq ?_
  -- The buffer.
  refine (lr_wp (X' := fun W t => DecX F S k lab labLen o ml kH Hl.D kG Gm.D W t ∧ IdxX W ∧ ZX S t) (lr_seq_tr [.x11, .x12]
      (fun r => ([(Reg.x11, off S oBuf), (.x12, BitVec.ofNat 64 256)].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun t V W L R _ => clearA_pin L)
    fun t V W L R hx => WP.mono (clearBuf_ok L R) fun u ⟨Lu, Su, Ru⟩ => ⟨_, W, Lu, Ru,
      hx.1.step Su fun _ _ => rfl, hx.2, fun x h1 h2 => by
        rw [Ru.scr _ (by unfold oRsa; omega), zV, ifp (by omega)]⟩).seq ?_
  refine (lr_wp (X' := fun W t => DecX F S k lab labLen o ml kH Hl.D kG Gm.D W t ∧ IdxX W ∧ ZX S t) (lr_seq_tr [.x11, .x12, .x13]
      (fun r => ([(Reg.x11, off S (1 + 2 * Hl.D)), (.x12, off S oBuf),
        (.x13, BitVec.ofNat 64 (k - (2 * Hl.D + 1)))].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun t V W L R hx => copyA_pin L R hx.1.2.2.1 hx.1.2.2.2.hlen hD)
    fun t V W L R ⟨hx, hi, hz⟩ => WP.mono (copyT_ok L R hx.2.2.1 hx.2.2.2.hlen hD hk') fun u ⟨Lu, Su, Ru⟩ => ⟨_, W, Lu, Ru,
      hx.step Su fun _ _ => rfl, hi, fun x h1 h2 => by
        rw [Ru.scr _ (by unfold oRsa; omega), cpV, ifn (by omega), ← R.scr _ (by unfold oRsa; omega)]
        exact hz x h1 h2⟩).seq ?_
  -- The shift.
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D) (lr_seq_tr [.x17, .x14, .x8]
      (fun r => ([(Reg.x17, off S oBuf), (.x14, BitVec.ofNat 64 1), (.x8, BitVec.ofNat 64 10)].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun t V W L R _ => shiftA_pin L)
    fun t V W L R ⟨hx, ⟨idx, hidx, hidx'⟩, hz⟩ => WP.mono (shift_ok L R hidx hidx' fun x h1 h2 => by
        rw [← R.scr _ (by unfold oRsa; omega)]; exact hz x h1 h2)
      fun u ⟨Lu, Su, V', Ru, _, _⟩ => ⟨V', W, Lu, Ru, hx.step Su fun _ _ => rfl⟩).seq ?_
  -- `ok`.
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D) (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (okMask_ok L R) fun u ⟨Lu, Su, Ru⟩ => ⟨V, _, Lu, Ru,
      hx.step Su fun j hj => by simp only [upd]; rw [ifn (by omega)]⟩).seq ?_
  -- `out`.
  refine (lr_wp (X' := DecX F S k lab labLen o ml kH Hl.D kG Gm.D) (lr_seq_tr [.x11, .x12, .x13]
      (fun r => ([(Reg.x11, o), (.x12, off S oBuf), (.x13, BitVec.ofNat 64 k)].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun t V W L R hx => outA_pin L R hx.2.1.ho hx.2.2.1)
    fun t V W L R hx => WP.mono (outLoop_ok L R hx.2.1.ho hx.2.2.1 (by omega) hk' hx.2.1.hw hx.2.1.hnw hx.2.1.ha)
      fun u ⟨Lu, Su, Ru, _⟩ => ⟨V, W, Lu, Ru, hx.step Su fun _ _ => rfl⟩).seq ?_
  -- The length and the result.
  show RelCT isa _ (.block (([.ldrSp .x14 sOk, .ldrSp .x10 sK, .ldrSp .x12 sHl, .sub .x .x10 .x10 .x12,
    .sub .x .x10 .x10 .x12, .subImm .x .x10 .x10 2, .ldrSp .x11 sIdx, .sub .x .x10 .x10 .x11,
    .logic .and .x .x10 .x10 .x14, .ldrSp .x11 sMl] : List Instr) ++
    (([.str .x .x10 .x11 0, .movz .x .x15 1 0, .logic .and .x .x14 .x14 .x15] : List Instr) ++ faultBit ++
      ([.logic .orr .x .x0 .x0 .x14] : List Instr)))) _
  exact RelCT.block_append (lr_seq_tr [.x11] (fun _ => ml) (by taint_decide) (by taint_decide)
    fun t V W L R hx => retA_pin L R hx.2.1.hml)

end VG.Proof.RsaOaep.AArch64
