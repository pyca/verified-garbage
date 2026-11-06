module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP on AArch64: MGF1

As on x86-64 (`Proof/RsaOaep/X86_64/Mgf.lean`): the blocks of
`mgfXor lay G`, which XORs `MGF1(src, dstLen)` into `dst`, where `src` (`srcLen` bytes)
and `dst` (`dstLen` bytes) are ranges of our working space below the hash
function's, given by MGF1's slots: for each counter `c`, the state is set
by `init`, `update` absorbs `src` and then `I2OSP(c, 4)` (written to
`scratch + oCtr`, `updCtr_ok`), `finalize` writes the digest to
`scratch + oDig`, and the first `min(hLen, dstLen - c hLen)` bytes of the
digest are XORed into `dst + c hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs round xorOut xorHead xorBody nextCtr initArgs updSrcArgs updCtrArgs
  finArgs mgfXor)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK VecKept)

/-! ## Blocks -/

/-- A slot, read through `Rep`. -/
theorem Rep.rd8 {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : W k = v) : m.read (F + BitVec.ofNat 64 d) 8 = v := by
  rw [← hv, ← R.fr k hk, hd]; rfl

/-- What MGF1's slots hold. -/
structure MArgs (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Prop where
  hsrc : W 13 = off S src
  hsl : W 14 = BitVec.ofNat 64 srcLen
  hdst : W 15 = off S dst
  hdl : W 16 = BitVec.ofNat 64 dstLen

theorem MArgs.of_eq {W W' : Nat → BitVec 64} {S : Addr} {src srcLen dst dstLen : Nat}
    (h : MArgs W S src srcLen dst dstLen) (hW : ∀ k, 13 ≤ k → k ≤ 16 → W' k = W k) :
    MArgs W' S src srcLen dst dstLen :=
  ⟨(hW 13 (by omega_using []) (by omega_using [])).trans h.hsrc, (hW 14 (by omega_using []) (by omega_using [])).trans h.hsl,
    (hW 15 (by omega_using []) (by omega_using [])).trans h.hdst, (hW 16 (by omega_using []) (by omega_using [])).trans h.hdl⟩

theorem initArgs_ok {u : State} {F S : Addr} (L : Lay u F S) (ws : List Region) :
    WP isa (.block (initArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt := by
  have h₁ : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  oaep_run [initArgs, Mgf1.scr, lay, sScr, oSt, h₁, L.sp, hs]
  exact ⟨blk_step, trivial⟩

theorem updSrc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat} (A : MArgs W S src srcLen dst dstLen) (ws : List Region) :
    WP isa (.block (updSrcArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 0 ∧ u'.gpr .x2 = off S src ∧ u'.gpr .x3 = BitVec.ofNat 64 srcLen ∧
      u'.gpr .x4 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h104 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 104) 8 := L.ld (d := 104) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hsrc := R.rd8 (d := 104) (k := 13) rfl (by decide) A.hsrc
  have hsl := R.rd8 (d := 112) (k := 14) rfl (by decide) A.hsl
  oaep_run [updSrcArgs, Mgf1.scr, lay, sScr, sSrc, sSrcLen, oSt, oW, h96, h104, h112, L.sp, hs, hsrc, hsl]
  exact ⟨blk_step, trivial, trivial, by decide, trivial⟩

theorem finA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen : Nat} (hl : W 14 = BitVec.ofNat 64 srcLen) (ws : List Region) :
    WP isa (.block (finArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .x2 = off S oDig ∧ u'.gpr .x3 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hsl := R.rd8 (d := 112) (k := 14) rfl (by decide) hl
  oaep_run [finArgs, Mgf1.scr, lay, sScr, sSrcLen, oSt, oW, oDig, h96, h112, L.sp, hs, hsl]
  exact ⟨blk_step, trivial, trivial, by rw [BitVec.ofNat_add], trivial⟩

/-! ## The counter -/

/-- `I2OSP(c, 4)` at `scratch + oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oCtr ≤ x ∧ x < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (x - oCtr) 0 else V x

theorem trunc8 (x : Nat) : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]

theorem shr8 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 8 = BitVec.ofNat 64 (x / 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem updCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen c : Nat} (hl : W 14 = BitVec.ofNat 64 srcLen) (hc : W 17 = BitVec.ofNat 64 c)
    (hc32 : c < 2 ^ 32) (ws : List Region) :
    WP isa (.block (updCtrArgs lay)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧ Rep u'.mem F S (ctrV V c) W ∧
      u'.gpr .x0 = off S oSt ∧ u'.gpr .x1 = BitVec.ofNat 64 srcLen ∧ u'.gpr .x2 = off S oCtr ∧
      u'.gpr .x3 = BitVec.ofNat 64 4 ∧ u'.gpr .x4 = off S oW := by
  have G' := L.geo
  have w12 : W 12 = S := (R.fr 12 (by decide)).symm.trans L.slot
  have R1 := (((R.wb G' (o := 3459) (by decide) (BitVec.ofNat 8 c)).wb G'
    (o := 3458) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G'
    (o := 3457) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G'
    (o := 3456) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have h136 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 136) 8 := L.ld (d := 136) (by decide)
  have s0 : InRegions u.wr (S + BitVec.ofNat 64 3456) 1 := L.sst (o := 3456) (by decide)
  have s1 : InRegions u.wr (S + BitVec.ofNat 64 3457) 1 := L.sst (o := 3457) (by decide)
  have s2 : InRegions u.wr (S + BitVec.ofNat 64 3458) 1 := L.sst (o := 3458) (by decide)
  have s3 : InRegions u.wr (S + BitVec.ofNat 64 3459) 1 := L.sst (o := 3459) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hcr := R.rd8 (d := 136) (k := 17) rfl (by decide) hc
  have hs4 := R1.rd8 (d := 96) (k := 12) rfl (by decide) w12
  have hl4 := R1.rd8 (d := 112) (k := 14) rfl (by decide) hl
  refine WP.mono (Q := fun (u' : State) => u'.mem = (((u.mem.write (off S 3459) 1 (BitVec.ofNat 8 c)).write (off S 3458) 1
      (BitVec.ofNat 8 (c / 2 ^ 8))).write (off S 3457) 1 (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).write (off S 3456) 1
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 srcLen ∧ u'.gpr .x2 = off S oCtr ∧ u'.gpr .x3 = BitVec.ofNat 64 4 ∧
      u'.gpr .x4 = off S oW) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x0, x1, x2, x3, x4⟩ => ?_
  · oaep_run [updCtrArgs, Mgf1.scr, lay, sScr, sSrcLen, sCtr, oSt, oW, oCtr, h96, h112, h136, L.sp, hs, hcr,
      BitVec.add_assoc, BitVec.reduceAdd, s0, s1, s2, s3, trunc8, shr8 (show c < 2 ^ 64 by omega_using [hc32]),
      shr8 (show c / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]), shr8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]), hs4, hl4]
    exact ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, trivial, trivial, trivial, by decide, trivial⟩
  have R' : Rep u'.mem F S (ctrV V c) W := by
    rw [hm]
    refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R1
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    simp only [upd, ctrV, oCtr, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = 3456 ∨ x = 3457 ∨ x = 3458 ∨ x = 3459 ∨ ¬(3456 ≤ x ∧ x < 3456 + 4) by omega_using []) with
      h | h | h | h | h
    · subst h; simp [e1]
    · subst h; simp [e2]
    · subst h; simp [e3]
    · subst h; simp
    · rw [ifn h, ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', x0, x1, x2, x3, x4⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]
    exact frame_wb (frame_wb (frame_wb (frame_wb (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _

/-! ## The digest into `dst` -/

theorem imm16 {n : Nat} (hn : n < 65536) : BitVec.setWidth 64 (BitVec.ofNat 16 n) <<< 0 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [hn]


/-! ## Where MGF1 works -/

/-- The ranges of our working space the hash functions' calls and MGF1's
counter write. -/
def hashR : List (Nat × Nat) := [(oSt, 256), (oDig, 64), (oCtr, 4), (oW, 1072)]

/-- Outside them. -/
def mOut (o : Nat) : Prop := ¬ inR hashR o

theorem mOut_iff (o : Nat) : mOut o ↔ o < oSt ∨ (oDig + 64 ≤ o ∧ o < oCtr) ∨ (oCtr + 4 ≤ o ∧ o < oW) ∨
    oW + 1072 ≤ o := by
  simp only [mOut, hashR, inR_cons, inR_nil, or_false, oSt, oDig, oCtr, oW]
  omega_using []

/-- `src` and `dst`, below the hash functions' ranges and apart. -/
structure MFit (src srcLen dst dstLen : Nat) : Prop where
  fs : src + srcLen ≤ oSt
  fd : dst + dstLen ≤ oSt
  sep : src + srcLen ≤ dst ∨ dst + dstLen ≤ src
  pos : 0 < dstLen
  dstB : dstLen ≤ 2048

/-- The loop's invariant after `c` counters. -/
structure MgfI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (mk : List Byte)
    (dst dstLen D c : Nat) (v : State) : Prop where
  L : Lay v F S
  st : Step F S [] u₀ v
  rep : ∃ V' W', Rep v.mem F S V' W' ∧ W' 17 = BitVec.ofNat 64 c ∧ W' 18 = BitVec.ofNat 64 (c * D) ∧
    (∀ k < nW, k ≠ 17 → k ≠ 18 → W' k = W k) ∧
    ∀ o < oRsa, mOut o → V' o = mixV V mk dst (min (c * D) dstLen) o

/-- The view of memory after a call, as a function of its own. -/
theorem Rep.ex {m : Mem} {F S : Addr} {p : Nat → Prop} [DecidablePred p] {f V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep m F S (fun o => if p o then f o else V o) W) :
    ∃ V', Rep m F S V' W ∧ (∀ o, ¬ p o → V' o = V o) ∧ (∀ o, p o → V' o = f o) :=
  ⟨_, R, fun _ h => ifn h _ _, fun _ h => ifp h _ _⟩

theorem repr_congr {R : Mem → Addr → List Byte → Prop} {m : Mem} {p : Addr} {a b : List Byte} (h : a = b)
    (hr : R m p a) : R m p b := h ▸ hr

/-! ## One counter -/

section
variable {G : Hash} (hG : StreamOK G.stream)


end

end VG.Proof.RsaOaep.AArch64
