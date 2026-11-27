module

import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.EncodeEq
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.RsaPss.EncodeEq
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncContract
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
meta import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
meta import VerifiedGarbage.Proof.Mgf1.Basic
meta import VerifiedGarbage.Proof.RsaPss.EncBytes
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncContract
meta import VerifiedGarbage.Proof.RsaPss.EncodingContract
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre

/-! ### `RsaPss.AArch64.EncCorrect`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.Restore`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on AArch64: the epilogue

The restores and the frame's release, for any of the functions with the
frame of `frameBytes` bytes at `fb s` (`restore_frame_ok`): the caller's
registers are back, and `x0` and memory are kept.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb saved_offs saved_ho)

theorem preserved_saved : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide

theorem restore_frame_ok {s w : State} (hsp : w.sp = fb s) (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (hv : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hwr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega_using [this]) (by have := saved_offs p hp'; omega_using [this]))))
    (by rw [o₁.mem]; exact hsv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp (preserved_saved r hr')
    exact hr.gpr p hp'
  · simp only [freed]
    rw [hr.sp, o₁.sp, hsp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hv r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]


/-- `restoreP`: the restores but those of `x19` and `x20`, which hold the
caller's values already. -/
theorem restoreP_frame_ok {s w : State} (hsp : w.sp = fb s) (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (hv : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hsv : Spill.Saved (fb s) s.gpr (saved.drop 2) w.mem) (h19 : w.gpr .x19 = s.gpr .x19)
    (h20 : w.gpr .x20 = s.gpr .x20) :
    WP isa (.block restoreP) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restoreP
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved.drop 2) (B := fb s) e₁ (fun p hp => saved_ho p
      (List.mem_of_mem_drop hp)) (by decide)
    (fun p hp' => by
      have := saved_offs p (List.mem_of_mem_drop hp')
      rw [o₁.rd, o₁.wr, hwr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by unfold frameBytes; omega_using [this]) (by omega_using [this]))))
    (by rw [o₁.mem]; exact hsv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    by_cases h : r ∈ (saved.drop 2).map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
      exact hr.gpr p hp'
    · rw [hr.other r h, o₁.gpr r (by revert h hr'; cases r <;> decide)]
      have : r = .x19 ∨ r = .x20 := by revert h hr'; cases r <;> decide
      rcases this with rfl | rfl
      · exact h19
      · exact h20
  · simp only [freed]
    rw [hr.sp, o₁.sp, hsp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hv r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]

end VG.Proof.RsaPss.AArch64

end

end

/-! ### `RsaPss.AArch64.EncPre`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's encoding on AArch64: the precondition

`PreE D tsH tsG s`: the precondition of `encode` (`encK`), with the stack
`stk 288` of the frame, MGF1's frame and the hash functions' calls, and the
tables `tsH` and `tsG` at the stack arguments. The frame is that of signing
(`Sgn.fb`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0)

/-- The stack `encode` uses: its frame, and the 288 bytes below it that MGF1's
frame and the hash functions' calls use. -/
abbrev encStack : Nat := stk 288

/-- The buffers: `em`, the digest, the salt and the working space, the
tables and the stack arguments. -/
abbrev emR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x2, D⟩
abbrev saR (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev sR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 0) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 1) 11
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- What the code needs at the entry, for the tables
`tsH` of `MdHash` and `tsG` of `MdHash`. -/
structure PreE (D : Nat) (tsH tsG : List FnTable) (s : State) : Prop where
  sp1 : encStack ≤ s.sp.toNat
  sp2 : s.sp.toNat + 16 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 0) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 1) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : s.rd = [dgR D s, saR s, tHR s, tGR s, aR s]
  hwr : s.wr = [emR s, sR s]
  ed : (emR s).Disjoint (dgR D s)
  esa : (emR s).Disjoint (saR s)
  es : (emR s).Disjoint (sR s)
  etH : (emR s).Disjoint (tHR s)
  etG : (emR s).Disjoint (tGR s)
  eA : (emR s).Disjoint (aR s)
  ds : (dgR D s).Disjoint (sR s)
  sas : (saR s).Disjoint (sR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sA : (sR s).Disjoint (aR s)
  ke : (kR 288 s).Disjoint (emR s)
  kd : (kR 288 s).Disjoint (dgR D s)
  ksa : (kR 288 s).Disjoint (saR s)
  ks : (kR 288 s).Disjoint (sR s)
  ktH : (kR 288 s).Disjoint (tHR s)
  ktG : (kR 288 s).Disjoint (tGR s)
  kA : (kR 288 s).Disjoint (aR s)
  we : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wd : (s.gpr .x2).toNat + D ≤ 2 ^ 64
  wsa : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  ws : (s.gpr .x6).toNat + (s.gpr .x7).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 0).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 1).toNat + 88 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .x5).toNat
  b2 : (s.gpr .x5).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .x1).toNat = Spec.RsaPss.emLength (s.gpr .x5).toNat
  hs : Proof.RsaPss.encScratch ≤ (s.gpr .x7).toNat

variable {D : Nat} {tsH tsG : List FnTable} {s : State}

theorem PreE.k1 (hp : PreE D tsH tsG s) : 1 ≤ (s.gpr .x1).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega_arith

theorem PreE.k2 (hp : PreE D tsH tsG s) : (s.gpr .x1).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega_arith

/-- `z = 8 emLen - emBits`, the bits of `em` above `emBits`, is below 8. -/
theorem PreE.z (hp : PreE D tsH tsG s) : (s.gpr .x5).toNat ≤ 8 * (s.gpr .x1).toNat ∧
    8 * (s.gpr .x1).toNat - (s.gpr .x5).toNat < 8 := by
  have := hp.hel; unfold Spec.RsaPss.emLength at *; omega_using [this]

theorem fb_toNat (hp : PreE D tsH tsG s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack stk at this; omega_using [this]

end VG.Proof.RsaPss.AArch64.Enc

end

end

/-! ### `RsaPss.AArch64.EncFrame`, which only this module used -/

section

/-!
# EMSA-PSS's encoding on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`FrE`), `scratch` in `x20`, `x19` and `x21` set, `emLen` in
`x23`, the mask `0xFF >>> z` in `sC` and `lo = 0` in `sLo` (`AtE`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm wp_ldrx wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_ldrSp)
open VG.Proof.RsaPss.AArch64 (off maskBits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb in_frame wr_frame kR frame_sub0 stackArgAddr_fb)

/-- The argument registers kept in slots of the frame. -/
def encSlots : List (Reg × Nat) := [(.x0, sOut), (.x2, sDig), (.x3, sSalt), (.x4, sSaltLen)]

theorem fits : Spill.Fits (saved ++ encSlots) := by decide

/-- `z = 8 emLen - emBits`, and the mask of `maskedDB`'s top bits. -/
abbrev zE (s : State) : Nat := 8 * (s.gpr .x1).toNat - (s.gpr .x5).toNat
abbrev cE (s : State) : Byte := (0xFF : Byte) >>> zE s

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure FrE (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  rs : Spill.Saved (fb s) s.gpr encSlots m

/-- The slots of `FrE`: `[96, 248)` of the frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩

theorem FrE.frame {s : State} {m m' : Mem} (h : FrE s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) : FrE s m' :=
  ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, h.rs.frame_in (lo := 96) (n := 152) (by decide) hf hA⟩

/-- After the prologue. -/
structure AtE (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : u.gpr .x19 = off (s.gpr .x6) oSt
  x20 : u.gpr .x20 = s.gpr .x6
  x21 : u.gpr .x21 = off (s.gpr .x6) oDig
  x23 : u.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  fr : FrE s u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 0
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 (cE s)

theorem prologue_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block encPrologue) u (AtE s) := by
  unfold encPrologue save regsUp
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  obtain hin : ∀ p ∈ saved ++ encSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ encSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ encSlots) = m₂
  obtain fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  obtain sv₂ : Spill.Saved (fb s) s.gpr (saved ++ encSlots) m₂ := by
    rw [← hm₂, e₁]
    intro p hp'
    rw [Spill.saveMem_saved fits _ _ _ p hp']
    have : p.1 ≠ .x16 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg]
  obtain gs : ∀ r, r ≠ .x16 → u₁.gpr r = s.gpr r := fun r h => by rw [o₁.gpr r (by simpa using h), hg]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ =>
    wp_addImm (by decide) fun u₆ o₆ e₆ => ?_
  obtain O₆ : Only [.x23, .x20, .x19, .x21] { u₁ with mem := m₂ } u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  obtain sp₆ : u₆.sp = fb s := by rw [O₆.sp]; show u₁.sp = _; rw [o₁.sp, hsp]
  obtain wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr]; show u₁.wr = _; rw [o₁.wr, hwr]
  obtain x20₆ : u₆.gpr .x20 = s.gpr .x6 := by
    rw [o₆.get .x20, o₅.get .x20, e₄, o₃.get .x6]; exact gs .x6 (by decide)
  obtain x23₆ : u₆.gpr .x23 = s.gpr .x1 := by
    rw [o₆.get .x23, o₅.get .x23, o₄.get .x23, e₃]; exact gs .x1 (by decide)
  obtain x5₆ : u₆.gpr .x5 = s.gpr .x5 := by rw [O₆.get .x5]; exact gs .x5 (by decide)
  have hk2 := hp.k2
  have hz := hp.z
  refine WP.mono (maskBits_ok (F := fb s) sp₆ (by rw [wr₆]; exact in_frame s _ (by decide))
    (by rw [wr₆]; exact in_frame s _ (by decide)) (r := .x5) (by decide) (k := (s.gpr .x1).toNat)
    (eb := (s.gpr .x5).toNat) (by rw [x23₆, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [x5₆, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hz.1 hz.2 (by omega_using [hk2])) fun u₇ ⟨K, hm₇⟩ => ?_
  obtain hm₇' : u₇.mem = (m₂.writeW (fb s + BitVec.ofNat 64 sC) (BitVec.setWidth 64 (cE s))).writeW
      (fb s + BitVec.ofNat 64 sLo) (0 : BitVec 64) := by rw [hm₇, O₆.mem]
  obtain W2 : Frame [⟨fb s + BitVec.ofNat 64 sC, 8⟩, ⟨fb s + BitVec.ofNat 64 sLo, 8⟩] m₂ u₇.mem := by
    rw [hm₇']
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  exact {
    sp := K.sp.trans sp₆
    rd := by rw [K.rd, O₆.rd]; show u₁.rd = _; rw [o₁.rd, hrd]
    wr := K.wr.trans wr₆
    x19 := by rw [K.get .x19, o₆.get .x19, e₅, e₄, o₃.get .x6, gs .x6 (by decide)]
    x20 := by rw [K.get .x20, x20₆]
    x21 := by rw [K.get .x21, e₆, o₅.get .x20, e₄, o₃.get .x6, gs .x6 (by decide)]
    x23 := by rw [K.get .x23, x23₆]
    v := fun r hr => by
      rw [K.vcs r hr, O₆.vcs r hr]
      show (u₁.v r).extractLsb' 0 64 = _
      rw [o₁.vcs r hr, hv r hr]
    mem := by
      rw [hm₇']
      exact (fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    fr := by
      obtain sv₇ := sv₂.frame W2 fun p hp' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
      exact ⟨sv₇.sub fun p hp => List.mem_append_left _ hp, sv₇.sub fun p hp => List.mem_append_right _ hp⟩
    lo := by rw [hm₇', Mem.readW_writeW_self64]; rfl
    c := by
      rw [hm₇', Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64] }

/-! ## The tables' words to their slots -/

/-- After `tabSlots`: the prologue's facts, and the slots of the tables'
words. -/
structure AtT (s u : State) : Prop where
  e : AtE s u
  wm : u.mem.readW (fb s + BitVec.ofNat 64 sMgfT) 64 = stackArg s 1
  wi : u.mem.readW (fb s + BitVec.ofNat 64 sIniH) 64 = s.mem.readW (stackArg s 0) 64
  wc : u.mem.readW (fb s + BitVec.ofNat 64 sCmpH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64
  wd : u.mem.readW (fb s + BitVec.ofNat 64 sDigH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64
  sy : u.syms = s.syms

/-- What `AtE` says, after writes to slots apart from its own. -/
theorem AtE.writes {s u v : State} (h : AtE s u) {m : Mem} (hv : v.mem = m) (hsp : v.sp = u.sp) (hrd : v.rd = u.rd)
    (hwr : v.wr = u.wr) (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], v.gpr r = u.gpr r)
    (hvv : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64)
    {ds : List Nat} (hd : ∀ d ∈ ds, 248 ≤ d ∧ d + 8 ≤ frameBytes ∧ (d + 8 ≤ sLo ∨ sLo + 8 ≤ d) ∧
      (d + 8 ≤ sC ∨ sC + 8 ≤ d)) (hf : Frame (ds.map fun d => (⟨fb s + BitVec.ofNat 64 d, 8⟩ : Region)) u.mem m) :
    AtE s v where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := (hg _ (by simp)).trans h.x19
  x20 := (hg _ (by simp)).trans h.x20
  x21 := (hg _ (by simp)).trans h.x21
  x23 := (hg _ (by simp)).trans h.x23
  v := fun r hr => (hvv r hr).trans (h.v r hr)
  mem := by
    rw [hv]
    exact h.mem.trans (hf.sub fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (hd d hd').2.1⟩)
  fr := by
    rw [hv]
    exact h.fr.frame hf fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ (by omega_using [this]) (by unfold frameBytes at this; omega_using []) (by unfold frameBytes at this; omega_using [this])
  lo := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sLo, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.1.symm (by decide) (by unfold frameBytes at this; omega_using [this])) (by decide)]
    exact h.lo
  c := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sC, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.2.symm (by decide) (by unfold frameBytes at this; omega_using [this])) (by decide)]
    exact h.c

/-- `tabSlots` after its first load, of the table's address into `x9`. -/
theorem tabSlotsT_ok {D : Nat} {tsH tsG : List FnTable} {s u u₁ : State} (hp : PreE D tsH tsG s) (hu : AtE s u)
    (o₁ : Only [.x9] u u₁) (e₁ : u₁.gpr .x9 = stackArg s 0) (hsy : u₁.syms = s.syms) :
    WP isa (.block tabSlots.tail) u₁ (AtT s) := by
  obtain rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega_using [hd])⟩
  obtain rT : ∀ d, d + 8 ≤ 88 → InRegions (u.rd ++ u.wr) (stackArg s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨tHR s, by simp, Offset.contains_base _ hd (by have := hp.wtH; omega_using [hd])⟩
  obtain kF : ∀ {R : Region}, (kR 288 s).Disjoint R → ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_sub0 288 s)).symm
  obtain mT : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ d, d + 8 ≤ 88 →
      m.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := tHR s) (Offset.contains_base _ hd (by have := hp.wtH; omega_using [hd])) (kF hp.ktH) (by decide)
  obtain mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ j, j < 2 →
      m.readW (stackArgAddr s j) 64 = stackArg s j := fun hf j hj =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by simp [stackArgAddr]]
      exact Offset.contains_base _ (by omega_using [hj]) (by have := hp.sp2; simp; omega_using [hj])) (kF hp.kA) (by decide)
  unfold tabSlots arg st
  simp only [List.cons_append, List.nil_append, List.tail_cons]
  refine WP.of_syms ?_
  refine wp_ldrx (by decide) (by rw [e₁]) (by rw [o₁.rd, o₁.wr]; exact rT 0 (by decide)) fun u₂ o₂ e₂ => ?_
  refine wp_addSp (by decide) fun u₃ o₃ e₃ => ?_
  refine wp_strx (by decide) (by rw [e₃, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₄ m₄ => ?_
  obtain f₄ : Frame [⟨fb s, frameBytes⟩] s.mem u₄.mem := by
    rw [m₄.mem, o₃.mem, o₂.mem, o₁.mem]
    exact hu.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrx (by decide) (by rw [m₄.gpr, o₃.get .x9, o₂.get .x9, e₁])
    (by rw [m₄.rd, o₃.rd, o₂.rd, o₁.rd, m₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact rT 24 (by decide)) fun u₅ o₅ e₅ => ?_
  rw [mT f₄ 24 (by decide)] at e₅
  refine wp_addSp (by decide) fun u₆ o₆ e₆ => ?_
  refine wp_strx (by decide) (by rw [e₆, o₅.sp, m₄.sp, o₃.sp, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₇ m₇ => ?_
  obtain f₇ : Frame [⟨fb s, frameBytes⟩] s.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]
    exact f₄.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrx (by decide) (by rw [m₇.gpr, o₆.get .x9, o₅.get .x9, m₄.gpr, o₃.get .x9, o₂.get .x9, e₁])
    (by rw [m₇.rd, o₆.rd, o₅.rd, m₄.rd, o₃.rd, o₂.rd, o₁.rd, m₇.wr, o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr]
        exact rT 32 (by decide)) fun u₈ o₈ e₈ => ?_
  rw [mT f₇ 32 (by decide)] at e₈
  refine wp_addSp (by decide) fun u₉ o₉ e₉ => ?_
  obtain sp₉ : u₉.sp = fb s := by rw [o₉.sp, o₈.sp, m₇.sp, o₆.sp, o₅.sp, m₄.sp, o₃.sp, o₂.sp, o₁.sp, hu.sp]
  obtain wr₉ : u₉.wr = ⟨fb s, frameBytes⟩ :: s.wr := by
    rw [o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, hu.wr]
  obtain rd₉ : u₉.rd = u.rd := by rw [o₉.rd, o₈.rd, m₇.rd, o₆.rd, o₅.rd, m₄.rd, o₃.rd, o₂.rd, o₁.rd]
  refine wp_strx (by decide) (by rw [e₉, ← o₉.sp, sp₉, BitVec.add_zero]) (by rw [wr₉]; exact in_frame s _ (by decide))
    fun u₁₀ m₁₀ => ?_
  obtain f₁₀ : Frame [⟨fb s, frameBytes⟩] s.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]
    exact f₇.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain r1 : InRegions (u₁₀.rd ++ u₁₀.wr) (u₁₀.sp + BitVec.ofNat 64 (frameBytes + 8 * 1)) 8 := by
    rw [m₁₀.sp, sp₉, m₁₀.rd, rd₉, m₁₀.wr, ← stackArgAddr_fb]
    have := rA 8 (by decide)
    rw [show stackArgAddr s 0 + BitVec.ofNat 64 8 = stackArgAddr s 1 by simp [stackArgAddr]] at this
    rw [wr₉, ← hu.wr]; exact this
  refine wp_ldrSp (by decide) r1 fun u₁₁ o₁₁ e₁₁ => ?_
  rw [m₁₀.sp, sp₉, ← stackArgAddr_fb, mA f₁₀ 1 (by decide)] at e₁₁
  refine wp_addSp (by decide) fun u₁₂ o₁₂ e₁₂ => ?_
  refine wp_strx (by decide) (by rw [e₁₂, o₁₁.sp, m₁₀.sp, sp₉, BitVec.add_zero])
    (by rw [o₁₂.wr, o₁₁.wr, m₁₀.wr, wr₉]; exact in_frame s _ (by decide)) fun u₁₃ m₁₃ => wp_nil fun sy => ?_
  obtain hm : u₁₃.mem = (((u.mem.writeW (fb s + BitVec.ofNat 64 sIniH) (s.mem.readW (stackArg s 0 + 0#64) 64)).writeW
      (fb s + BitVec.ofNat 64 sCmpH) (s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64)).writeW
      (fb s + BitVec.ofNat 64 sDigH) (s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64)).writeW
      (fb s + BitVec.ofNat 64 sMgfT) (stackArg s 1) := by
    obtain v1 : u₃.gpr .x10 = s.mem.readW (stackArg s 0 + 0#64) 64 := by
      rw [o₃.get .x10, e₂, o₁.mem, mT hu.mem 0 (by decide)]
    obtain v2 : u₆.gpr .x10 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64 := by rw [o₆.get .x10, e₅]
    obtain v3 : u₉.gpr .x10 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64 := by rw [o₉.get .x10, e₈]
    rw [m₁₃.mem, o₁₂.mem, o₁₁.mem, m₁₀.mem, o₉.mem, o₈.mem, m₇.mem, o₆.mem, o₅.mem, m₄.mem, o₃.mem, o₂.mem,
      o₁.mem, o₁₂.get .x9, e₁₁, v3, v2, v1]
  obtain K : Keep [.x9, .x10, .x16] u u₁₃ :=
    ((((((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans m₄.keep).trans o₅.keep).trans o₆.keep).trans
      m₇.keep).trans o₈.keep).trans o₉.keep).trans m₁₀.keep).trans o₁₁.keep).trans o₁₂.keep).trans m₁₃.keep).mono
  obtain hds : ∀ d ∈ [sIniH, sCmpH, sDigH, sMgfT], 248 ≤ d ∧ d + 8 ≤ frameBytes ∧ (d + 8 ≤ sLo ∨ sLo + 8 ≤ d) ∧
      (d + 8 ≤ sC ∨ sC + 8 ≤ d) := by decide
  obtain hf : Frame ([sIniH, sCmpH, sDigH, sMgfT].map fun d => (⟨fb s + BitVec.ofNat 64 d, 8⟩ : Region)) u.mem
      u₁₃.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  obtain sep : ∀ a b : Nat, b + 8 ≤ a ∨ a + 8 ≤ b → a + 8 ≤ 336 → b + 8 ≤ 336 →
      ∀ (m : Mem) (v : BitVec 64), (m.writeW (fb s + BitVec.ofNat 64 a) v).readW (fb s + BitVec.ofNat 64 b) 64 =
        m.readW (fb s + BitVec.ofNat 64 b) 64 := fun a b hab ha hb m v =>
    Mem.readW_writeW_sep (Offset.sep _ hab (by omega_using [hb]) (by omega_using [ha]))
      (by decide)
  refine ⟨AtE.writes hu rfl K.sp K.rd K.wr (fun r hr => K.get r (by revert r; decide)) K.vcs hds hf, ?_, ?_, ?_, ?_,
    sy.trans hsy⟩
  · rw [hm, Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, BitVec.add_zero]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

/-- `tabSlots`' first load: the table's address into `x9`. -/
theorem arg0_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hu : AtE s u) :
    WP isa (.block [arg .x9 0]) u fun u₁ => Only [.x9] u u₁ ∧ u₁.gpr .x9 = stackArg s 0 := by
  obtain rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega_using [hd])⟩
  obtain kF : ∀ {R : Region}, (kR 288 s).Disjoint R → ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_sub0 288 s)).symm
  obtain mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m →
      m.readW (stackArgAddr s 0) 64 = stackArg s 0 := fun hf =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s 0 = stackArgAddr s 0 + BitVec.ofNat 64 0 by simp]
      exact Offset.contains_base _ (by omega_using []) (by omega_using [])) (kF hp.kA) (by decide)
  obtain r0 : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * 0)) 8 := by
    have := rA 0 (by decide)
    rwa [BitVec.add_zero, stackArgAddr_fb, ← hu.sp] at this
  refine wp_ldrSp (by decide) r0 fun u₁ o₁ e₁ => wp_nil ⟨o₁, ?_⟩
  rw [e₁, hu.sp, ← stackArgAddr_fb, mA hu.mem]

theorem tabSlots_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hu : AtE s u)
    (hsy : u.syms = s.syms) :
    WP isa (.block tabSlots) u (AtT s) := by
  have e : tabSlots = [arg .x9 0] ++ tabSlots.tail := rfl
  rw [e, WP.block_append_iff]
  exact WP.mono_syms (arg0_ok hp hu) fun u₁ ⟨o₁, e₁⟩ sy₁ => tabSlotsT_ok hp hu o₁ e₁ (sy₁.trans hsy)

end VG.Proof.RsaPss.AArch64.Enc
end

end


/-!
# EMSA-PSS's encoding on AArch64: correctness

`code_ok`: `encode` keeps the calling convention, and returns 1 with `em`
holding `Spec.RsaPss.encode`'s encoding, or 0 if it fails (`Post`). After
the prologue, the checks of the lengths (`fitH_ok`, `saltFits_ok`), then the
encoding (`signEnc_ok`, with `k = emLen` and `lo = 0`) and its copy to `em`
(`encMain_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov copy_ok)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off off_add Lay mgfWr signEnc_ok fitH_ok saltFits_ok restore_frame_ok ld_slot
  slot_not_below)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

/-- What `encodeTContract.post` asks for: the encoding with the hash function
`Hs` (of digests of `D` bytes) and MGF1's `Gs`. -/
def encOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x2) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (s.gpr .x5).toNat

/-- The outcome, from the memory and `x0`. -/
def OutOk (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) (m : Mem) (r : BitVec 64) : Prop :=
  match encOut D Hs Gs s with
  | some e => r.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .x0) (s.gpr .x1).toNat = e
  | none => r.setWidth 32 = 0

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidE (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem

theorem AtE.toMid {s u : State} (h : AtE s u) : MidE s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtE` after code that writes registers other than ours. -/
theorem AtE.only {s u u' : State} (h : AtE s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtE s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- `AtT` after code that writes registers other than ours. -/
theorem AtT.only {s u u' : State} (h : AtT s u) {rs : List Reg} (o : Only rs u u') (hsy : u'.syms = u.syms)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtT s u' :=
  ⟨h.e.only o hr, o.mem ▸ h.wm, o.mem ▸ h.wi, o.mem ▸ h.wc, o.mem ▸ h.wd, hsy.trans h.sy⟩

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) : Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa Proof.RsaPss.encScratch at *; omega_using [this])

/-- The 16 bytes below the frame, in the stack. -/
theorem below16_sub (s : State) : Region.Sub (below (fb s) 16) (kR 288 s) := fun x h =>
  below_sub 288 s x (Offset.sub_below (fb s) (a := 16) (n := 16) (b := 288) (m := 288) (by decide) (by decide) x h)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {tsH tsG : List FnTable} {s w : State} (hp : PreE D tsH tsG s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  obtain hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hhs]⟩⟩
    Fw := by omega_using [hfb]
    Sw := by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFS := (hp.ks.sub_left (frame_sub0 288 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below16_sub s)).sub_right (rsa_sub hp) }

/-- A buffer apart from the stack and the working space is apart from what
the encoding writes. -/
theorem mgfWr_disj {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {R : Region} (hk : (kR 288 s).Disjoint R)
    (hs : R.Disjoint (sR s)) : ∀ r ∈ mgfWr (fb s) (s.gpr .x6), R.Disjoint r := by
  intro r hr
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (rsa_sub hp)
  · exact (hk.sub_left (below16_sub s)).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · rw [mgfFrame_eq]; exact (hk.sub_left (below_sub 288 s)).symm

/-- What the encoding writes keeps `FrE`. -/
theorem fr_mgf {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {m m' : Mem} (h : FrE s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6)) m m') : FrE s m' := by
  refine h.frame hf fun r hr => ?_
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.ks.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))).sub_right (rsa_sub hp)
  · exact Offset.disjoint_below _ (by omega_using [])
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_below _ (by rw [mgfFrame_eq]; omega_using [])

/-- An input, in memory changed only in the frame. -/
theorem bytes_frame {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {R : Region}
    (hk : (kR 288 s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaPkcs1Sig.bytes_apart hf (hk.sub_left (frame_sub0 288 s)).symm hl

/-- A refusal: 0. -/
theorem ret0_ok {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s u : State} (hu : AtE s u) (hn : encOut D Hs Gs s = none) :
    WP isa ret0 u fun t => MidE s t ∧ OutOk D Hs Gs s t.mem (t.gpr .x0) := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨(hu.only o).toMid, ?_⟩
  simp only [OutOk, hn, e]
  rfl

/-- The encoding's bytes, from the entry state: `emLen = k` bytes with
`lo = 0`. -/
def encF (Hs Gs : Spec.Mgf1.Hash) (D : Nat) (s : State) : Nat → Byte :=
  RsaPss.emT 0 ((s.gpr .x1).toNat - 0 - D - 1) (s.gpr .x4).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
    (Spec.Mgf1.mgf1 Gs (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ((s.gpr .x1).toNat - 0 - D - 1)) (cE s)

/-- After `signEnc`: `EM` holds `em`. -/
structure AtCopy (s : State) (em : Nat → Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : t.gpr .x20 = s.gpr .x6
  x23 : t.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem
  em : ∀ i < (s.gpr .x1).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = em i

/-- The slots of the table of `MdHash`, from the table at the entry. -/
theorem ht_of {H : Hash} {dn : String} {f : MdFns} {G : Impl.Pbkdf2.Md.AArch64.Stream}
    {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State} (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s)
    (hw : AtT s w) : HT H dn f (fb s) w.mem w.syms where
  wi := hw.wi.trans (ht.h0.trans (by rw [hw.sy]))
  wc := hw.wc.trans (ht.h3.trans (by rw [hw.sy]))
  wd := hw.wd.trans (ht.h4.trans (by rw [hw.sy]))
  fi := by rw [hw.sy]; exact ht.fi
  fc := by rw [hw.sy]; exact ht.fc
  fd := by rw [hw.sy]; exact ht.fd

/-- MGF1's working space, in ours. -/
theorem mgfScr_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) :
    Region.Sub ⟨off (s.gpr .x6) mgfOff, 8192⟩ (sR s) :=
  Offset.sub_base _ (by have := hp.hs; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [this])

/-- Where MGF1 works, and the table of `MdHash`, from the table at the entry. -/
theorem env_of {D : Nat} {tsH tsG : List FnTable} {H : Hash} {dn : String} {f : MdFns}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State}
    (hp : PreE D tsH tsG s) (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w) :
    Env G g w (fb s) (s.gpr .x6) (stackArg s 1) := by
  obtain hfb := fb_toNat hp
  have hsp1 := hp.sp1
  have hwtG := hp.wtG
  have hws := hp.ws
  have hhs := hp.hs
  obtain hS := mgfScr_sub hp
  obtain kG : ∀ {R : Region}, R.Sub (kR 288 s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.ktG.sub_left hR).symm
  obtain sG : ∀ {R : Region}, R.Sub (sR s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.stG.sub_left hR).symm
  obtain hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [⟨off (s.gpr .x6) mgfOff, 8192⟩, slotR (fb s) sPos],
      Region.Disjoint ⟨stackArg s 1, 88⟩ r := by
    intro r hr
    simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sG (rsa_sub hp)
    · exact kG (below16_sub s)
    · exact kG (frame_sub 288 s (by decide))
    · exact kG (frame_sub 288 s (by decide))
    · rw [mgfFrame_eq]; exact (hp.ktG.sub_left (below_sub 288 s)).symm
    · exact sG hS
    · exact kG (frame_sub 288 s (by decide))
  obtain hd0 : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], Region.Disjoint ⟨stackArg s 1, 88⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact kG (frame_sub0 288 s)
  obtain hin : ∀ d, d + 8 ≤ 88 → InRegions (w.rd ++ w.wr) (off (stackArg s 1) d) 8 := fun d hd' => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨tGR s, by simp, Offset.contains_base _ (k := 88) (by omega_using [hd']) (by omega_using [hd'])⟩
  exact {
    slot := hw.wm
    ok := by rw [hw.sy]; exact ht.gok
    rd := fun j hj => hin (8 * j) (by omega_using [hj])
    rdD := hin 48 (by decide)
    mem := fun m hm => by
      rw [hw.sy]
      exact ⟨TabMem.keep (TabMem.keep ht.gm hw.e.mem hd0) hm hd,
        ((tabG_keep hm hd (by decide)).trans (tabG_keep hw.e.mem hd0 (by decide))).trans ht.gD⟩
    sc := Covers.one (by
      rw [hw.e.wr, hp.hwr]
      exact ⟨sR s, by simp, Offset.contains_base _ (by unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hhs])
        (by unfold mgfOff; omega_using [])⟩)
    F288 := by rw [mgfFrame_eq]; unfold encStack Sgn.stk at hsp1; omega_using [hfb, hsp1]
    dStk := by rw [mgfFrame_eq]; exact (hp.ks.sub_left (below_sub 288 s)).sub_right hS
    Sw := by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFw := (hp.ks.sub_left (frame_sub0 288 s)).sub_right hS }

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hGh hGl hGv hdo in
/-- After the checks: the encoding. -/
theorem enc_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (signEnc f H g) w (AtCopy s (encF Hs Gs H.D s)) := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain L := lay_of hp hw.e.sp hw.e.x20 hw.e.wr
  obtain hwd := hp.wd; have hwsa := hp.wsa
  obtain hdR : ∀ j < H.D, InRegions (w.rd ++ w.wr) (s.gpr .x2 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hfit, hj])⟩
  obtain hqR : ∀ j < (s.gpr .x4).toNat, InRegions (w.rd ++ w.wr) (s.gpr .x3 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨saR s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain hbd : Spec.Rsa.bytesAt w.mem (s.gpr .x2) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D :=
    bytes_frame (R := dgR H.D s) hw.e.mem hp.kd (by dsimp only; omega_using [hfit])
  obtain hbs : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat :=
    bytes_frame (R := saR s) hw.e.mem hp.ksa (by dsimp only; omega_using [])
  refine WP.mono (signEnc_ok hH hGm hGh hGl hGv hHs hdo L (fun _ _ => rfl) (k := (s.gpr .x1).toNat) (lo := 0)
    (sl := (s.gpr .x4).toNat) (c := cE s) (dig := s.gpr .x2) (q := s.gpr .x3) hw.e.x19 hw.e.x21
    (by rw [hw.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h9, Nat.sub_zero]) hw.e.lo hw.e.c
    (hw.e.fr.rs (.x2, sDig) (by simp [encSlots])) (hw.e.fr.rs (.x3, sSalt) (by simp [encSlots]))
    (by rw [hw.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hk2 (Nat.zero_le 1) (by omega_using [hfit]) hdR (mgfWr_disj hp hp.kd hp.ds) hqR (mgfWr_disj hp hp.ksa hp.sas)
    (ht_of ht hw) (env_of hp ht hw)) fun t ⟨sp₁, rd₁, wr₁, cs₁, v₁, f₁, em₁⟩ => ?_
  rw [hbd, hbs] at em₁
  exact {
    sp := sp₁.trans hw.e.sp
    rd := rd₁.trans hw.e.rd
    wr := wr₁.trans hw.e.wr
    x20 := (cs₁ .x20 (by decide)).trans hw.e.x20
    x23 := (cs₁ .x23 (by decide)).trans hw.e.x23
    v := fun r hr => (v₁ r hr).trans (hw.e.v r hr)
    fr := fr_mgf hp hw.e.fr f₁
    em := em₁ }

end

/-- The arguments of the copy: `EM`, `em` and `emLen`. -/
theorem copyArgs_ok {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
    WP isa (.block [.addImm .x .x11 .x20 oEm, ld .x14 sOut, VG.Impl.MdStream.AArch64.mov .x12 .x23]) t
      fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off (s.gpr .x6) oEm ∧ u.gpr .x14 = s.gpr .x0 ∧
        u.gpr .x12 = s.gpr .x1 := by
  obtain L := lay_of hp ht.sp ht.x20 ht.wr
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_ldrSp (by decide)
    (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_, ?_, ?_⟩
  · rw [o₃.get .x11, o₂.get .x11, e₁, ht.x20]
  · rw [o₃.get .x14, e₂, o₁.mem, o₁.sp, ht.sp]
    exact ht.fr.rs (.x0, sOut) (by simp [encSlots])
  · rw [e₃, o₂.get .x23, o₁.get .x23, ht.x23]

/-- The copy of `EM` to `em`, and 1. -/
theorem copy_ok' {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
    WP isa (.seq copyOut (.block [movi .x0 1])) t fun t' => MidE s t' ∧ t'.gpr .x0 = BitVec.ofNat 64 1 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .x0) (s.gpr .x1).toNat = (List.range (s.gpr .x1).toNat).map em := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  obtain L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x1).toNat = k at hk1 hk2 hwe
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (copyArgs_ok hp ht) fun u ⟨O, h11, h14, h12⟩ => ?_))
  obtain hd : ∀ j < k, ∀ i < k, off (s.gpr .x6) oEm + BitVec.ofNat 64 j ≠ s.gpr .x0 + BitVec.ofNat 64 i := by
    intro j hj i hi h
    obtain h₁ : (emR s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base (s.gpr .x0) (d := i) (n := 1) (k := (s.gpr .x1).toNat) (by omega_using [hk, hi]) (by omega_using [hk, hi])
    obtain h₂ : (⟨s.gpr .x6, oRsa⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
      rw [← h, off_add]
      exact Offset.contains_base _ (by unfold oEm oRsa; omega_using [hk2, hj]) (by unfold oEm; omega_using [hk2, hj])
    exact hp.es _ h₁ (rsa_sub hp _ h₂)
  refine WP.mono (copy_ok (p := s.gpr .x0) (q := off (s.gpr .x6) oEm) (n := k) (by omega_using [hk1]) (by omega_using [hk]) h14 h11
    (by rw [h12, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [O.rd, O.wr, off_add]; exact L.ld (by simp only [oEm, oRsa]; omega_using [hk2, hj]))
    (fun i hi => by
      rw [O.wr, ht.wr, hp.hwr]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hk, hi])⟩) hd) fun u₄ ⟨K₄, m₄⟩ => ?_
  refine wp_movz fun t₅ o₅ e₅ => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by rw [e₅]; rfl, ?_⟩
  · rw [o₅.sp, K₄.sp, O.sp, ht.sp]
  · rw [o₅.rd, K₄.rd, O.rd, ht.rd]
  · rw [o₅.wr, K₄.wr, O.wr, ht.wr]
  · intro r hr; rw [o₅.vcs r hr, K₄.vcs r hr, O.vcs r hr, ht.v r hr]
  · rw [o₅.mem, m₄, O.mem]
    refine ht.fr.frame (writeBytes_frame _ _ _ (Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.bytesAt_length]
    have := hp.ke.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))
    dsimp only [emR] at this
    rwa [hk] at this
  rw [o₅.mem, m₄, O.mem]
  obtain hx := VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes t.mem (s.gpr .x0)
    (Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega_using [hk])
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hx
  rw [hx, show Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k =
    (List.range k).map fun i => t.mem (off (s.gpr .x6) oEm + BitVec.ofNat 64 i) from rfl]
  refine List.map_congr_left fun i hi => ?_
  rw [off_add, ht.em i (by rw [hk]; exact List.mem_range.mp hi)]

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (encMain f H g) w fun t => MidE s t ∧ OutOk H.D Hs Gs s t.mem (t.gpr .x0) := by
  unfold encMain seqs seqs
  refine WP.seq (WP.mono (enc_ok hH hGm hHs hGh hGl hGv hdo hp ht hw h9 hfit) fun t ht => ?_)
  refine WP.mono (copy_ok' hp ht) fun t' ⟨m, h0, hb⟩ => ⟨m, ?_⟩
  obtain hsl' : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  obtain he := RsaPss.encode_eq₂ Hs Gs hHv hGv (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (emBits := (s.gpr .x5).toNat)
    (emLen := (s.gpr .x1).toNat) (db := (s.gpr .x1).toNat - 0 - H.D - 1)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hHl])
    hp.hel.symm (by rw [hHl]; omega_using []) (by rw [hsl', hHl]; omega_using [hfit])
  simp only [OutOk, encOut, he]
  refine ⟨by rw [h0]; rfl, ?_⟩
  rw [hb, hsl']
  rfl

end

end VG.Proof.RsaPss.AArch64.Enc

end

end

/-! ### `RsaPss.AArch64.EncCTEnc`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.EncCTBase`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's encoding on AArch64: constant time, the public data

The pointers, the lengths and the tables' addresses are public (`PubE`),
and so are the addresses of the tables' functions; the digest and the salt
are secret. Two runs with the same public data as an anchor `a` (`E`), whose
tables name the same functions (`Tabs`), are related at each point of the
code by what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the tables' addresses. -/
structure PubE (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  sa : ∀ j < 2, stackArg s j = stackArg a j

theorem PubE.refl (s : State) : PubE s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- An entry state with the anchor's public data, whose tables name `T`'s
functions at the anchor's addresses. -/
def E (T : Tabs) (a s : State) : Prop :=
  PreE T.H.D T.tsH T.tsG s ∧ PubE a s ∧ T.At s ∧ ∀ n ∈ T.names, s.syms n = a.syms n

namespace E
variable {T : Tabs} {a s : State} (h : E T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.1.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.1.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

theorem arg {j : Nat} (hj : j < 2) : stackArg s j = stackArg a j := h.2.1.sa j hj

theorem sym {n : String} (hn : n ∈ T.names) : s.syms n = a.syms n := h.2.2.2 n hn

end E

end VG.Proof.RsaPss.AArch64.Enc

end

end

/-!
# EMSA-PSS's encoding on AArch64: the encoding is constant time

`encEnc_ct`: two runs of `signEnc` in `encode` (with `k = emLen` and
`lo = 0`), from states with the same public data, leak the same trace. Two
runs of the encoding from states with the same public
data leak the same trace. Between its pieces, each run is described by the
registers and slots of the frame that the anchor's public data fix (`SR`);
the pieces are checked by the taint analysis from those registers, the loads
of the salt's address and length from the frame are related by correctness
(`RelCT.seq_block_append`), the hash by `ctHash_ct` and MGF1 by `mgfXor_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_add wp_sub wp_subImm wp_strb eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64.Sgn (fb)
open VG.Proof.RsaPss.AArch64 (off two_taintE zH Lay slot_keep slotR mgfWr PssChecks HA HE MA MS
  dbRegs_ok clearY_ok copyDigest_ok copySaltY_ok signLen_ok clearEm_ok putSalt_ok putH_ok clearTop_ok
  ctHash_ct mgfXor_ct mgfXor_ok ctHashWith_out two_step pins_nil pad80_ok nb_keep slot_not_below wS_frame off_sub off_add ld_slot
  DbAt)

/-! ## The public values -/

/-- `k`, `lo`, `dbLen`, `sLen` and the number of blocks of `M'`, from the
anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .x1).toNat
abbrev loA (_a : State) : Nat := 0
abbrev dbA (D : Nat) (a : State) : Nat := kA a - loA a - D - 1
abbrev slA (a : State) : Nat := (a.gpr .x4).toNat
abbrev nbA (H : Hash) (a : State) : Nat := (8 + H.D + slA a + H.P.L) / H.P.B + 1

/-- The encoding fits: the checks passed. -/
structure SOk (D : Nat) (a : State) : Prop where
  k1 : 1 ≤ kA a
  k2 : kA a ≤ 1024
  fit : D + slA a + 2 ≤ kA a - loA a

/-- A run of the encoding, from an entry state with the anchor's public
data: the frame and the working space, and registers (`rs`) and slots (`sl`)
the anchor fixes. -/
structure SR (T : Tabs) (D : Nat) (rs : List (Reg × (State → BitVec 64))) (sl : List (Nat × (State → BitVec 64)))
    (a t : State) : Prop where
  ex : ∃ s t₀, E T a s ∧ AtT s t₀ ∧ Frame (mgfWr (fb a) (scr a)) t₀.mem t.mem ∧ t.syms = t₀.syms ∧
    t.rd = s.rd ∧ t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  L : Lay t (fb a) (scr a)
  r : ∀ q ∈ rs, t.gpr q.1 = q.2 a
  sl : ∀ q ∈ sl, t.mem.readW (off (fb a) q.1) 64 = q.2 a
  ok : SOk D a
  hD : D = T.H.D

theorem SR.pins {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
    {qs : List Reg} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) : Pins (SR T D rs sl) qs :=
  fun a s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.L.sp, h₂.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | ⟨f, hf⟩
    · rw [h₁.L.x20, h₂.L.x20]
    · rw [h₁.r _ hf, h₂.r _ hf]

theorem SR.keep {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
    {a u u' : State} (h : SR T D rs sl a u) {ks : List Reg} (k : Keep ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks)
    (h20 : Reg.x20 ∉ ks) {ws : List Region} (hf : Frame ws u.mem u'.mem)
    (hs : ∀ q ∈ sl, ∀ r ∈ ws, Region.Disjoint (slotR (fb a) q.1) r) (hsy : u'.syms = u.syms)
    (hws : ∀ r ∈ ws, r ∈ mgfWr (fb a) (scr a) := by simp [mgfWr]) : SR T D rs sl a u' where
  ex := let ⟨s, t₀, e, h0, fm, sy, hrd, hwr⟩ := h.ex
    ⟨s, t₀, e, h0, fm.trans (hf.mono hws), hsy.trans sy, k.rd.trans hrd, k.wr.trans hwr⟩
  L := h.L.congr k.sp k.wr (k.gpr .x20 h20)
  r := fun q hq => by rw [k.gpr q.1 (hk q hq)]; exact h.r q hq
  sl := fun q hq => by rw [slot_keep hf (hs q hq)]; exact h.sl q hq
  ok := h.ok
  hD := h.hD

/-- The registers of the encoding: `st`, the digest, `k`, `DB` and `dbLen`. -/
def sregs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x1),
    (.x24, fun a => off (scr a) (oEm + loA a)), (.x25, fun a => BitVec.ofNat 64 (dbA D a))]

theorem sregs_fst {D : Nat} {q : Reg × (State → BitVec 64)} (hq : q ∈ sregs D) :
    q.1 ∈ [Reg.x19, .x21, .x23, .x24, .x25] := by
  simp only [sregs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

/-- Registers apart from the encoding's, for `decide`. -/
theorem nk_of {D : Nat} {ks : List Reg} (h : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∉ ks) :
    ∀ q ∈ sregs D, q.1 ∉ ks :=
  fun _ hq => h _ (sregs_fst hq)

/-- The slots it reads: the digest's and the salt's addresses, the salt's
length and `lo`. -/
def sslots : List (Nat × (State → BitVec 64)) :=
  [(sDig, fun a => a.gpr .x2), (sSalt, fun a => a.gpr .x3), (sSaltLen, fun a => a.gpr .x4),
    (sLo, fun a => BitVec.ofNat 64 (loA a))]

theorem sslots_S {F S : Addr} {t : State} (L : Lay t F S) :
    ∀ q ∈ sslots, ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint (slotR F q.1) r := by
  intro q hq r hr
  rw [List.mem_singleton.mp hr]
  simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> exact L.dFS.sub_left (Offset.sub_base F (by decide))


/-- `SR` at a later state of the same run, from what it says there. -/
theorem SR.congr {T : Tabs} {D : Nat} {rs rs' : List (Reg × (State → BitVec 64))} {sl sl' : List (Nat × (State → BitVec 64))}
    {a u u' : State} (h : SR T D rs sl a u) (sp : u'.sp = u.sp) (rd : u'.rd = u.rd) (wr : u'.wr = u.wr)
    (h20 : u'.gpr .x20 = u.gpr .x20) (hr : ∀ q ∈ rs', u'.gpr q.1 = q.2 a)
    (hs : ∀ q ∈ sl', u'.mem.readW (off (fb a) q.1) 64 = q.2 a) (hsy : u'.syms = u.syms)
    (hfm : Frame (mgfWr (fb a) (scr a)) u.mem u'.mem) : SR T D rs' sl' a u' where
  ex := let ⟨s, t₀, e, h0, fm, sy, hrd, hwr⟩ := h.ex
    ⟨s, t₀, e, h0, fm.trans hfm, hsy.trans sy, rd.trans hrd, wr.trans hwr⟩
  L := h.L.congr sp wr h20
  r := hr
  sl := hs
  ok := h.ok
  hD := h.hD

namespace SR
variable {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
  {a u : State} (h : SR T D rs sl a u)
include h

/-- The digest is readable and apart from our working space. -/
theorem dig : (∀ j < D, InRegions (u.rd ++ u.wr) (a.gpr .x2 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨a.gpr .x2, D⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, _, e, _, _, _, hrd, hwr⟩ := h.ex
  have hp := e.1
  have hD := h.hD
  subst hD
  rw [← e.gpr (r := .x2) (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.ds.sub_right (rsa_sub hp)⟩
  rw [hrd, hp.hrd]
  exact ⟨dgR T.H.D s, by simp, Offset.contains_base _ (by omega_arith) (by have := hp.wd; omega_arith)⟩

/-- The salt is readable and apart from what the encoding writes. -/
theorem salt : (∀ j < slA a, InRegions (u.rd ++ u.wr) (a.gpr .x3 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨a.gpr .x3, slA a⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, _, e, _, _, _, hrd, hwr⟩ := h.ex
  have hp := e.1
  rw [← e.gpr (r := .x3) (by decide), slA, ← e.gpr (r := .x4) (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.sas.sub_right (rsa_sub hp)⟩
  rw [hrd, hp.hrd]
  exact ⟨saR s, by simp, Offset.contains_base _ (by omega_arith) (by have := hp.wsa; omega_arith)⟩

theorem sl_le : slA a ≤ 1024 := by have := h.ok.fit; have := h.ok.k2; omega_arith

theorem x23 (h23 : (Reg.x23, fun a : State => a.gpr .x1) ∈ rs) : u.gpr .x23 = BitVec.ofNat 64 (kA a) := by
  rw [h.r _ h23, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end SR

theorem SR.sp {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))} :
    ∀ a s₁ s₂, SR T D rs sl a s₁ → SR T D rs sl a s₂ → s₁.sp = s₂.sp :=
  fun _ _ _ h₁ h₂ => by rw [h₁.L.sp, h₂.L.sp]

/-! ## The pieces -/

/-- At the start of the encoding: `emLen - hLen - 2` in `x9`. -/
def sregs0 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x1),
    (.x9, fun a => BitVec.ofNat 64 (kA a - loA a - (D + 2)))]

theorem dbRegs_sct {T : Tabs} {D : Nat} :
    RelCT isa (Two (SR T D (sregs0 D) sslots)) (.block dbRegs) (Two (SR T D (sregs D) sslots)) := by
  refine two_post (two_taint [] (pins_nil SR.sp) (by taint_decide)) fun a u h => ?_
  have hf := h.ok.fit
  refine WP.mono_syms (dbRegs_ok h.L (x := kA a - loA a - (D + 2)) (lo := loA a)
    (h.r (.x9, fun a => BitVec.ofNat 64 (kA a - loA a - (D + 2))) (by simp [sregs0]))
    (h.sl (sLo, fun a => BitVec.ofNat 64 (loA a)) (by simp [sslots]))) fun u' ⟨O, x25, x24⟩ sy =>
    h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) (fun q hq => by rw [O.mem]; exact h.sl q hq) sy (by rw [O.mem]; exact Frame.refl _ _)
  simp only [sregs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [O.get .x19]; exact h.r (.x19, fun a => off (scr a) oSt) (by simp [sregs0])
  · rw [O.get .x21]; exact h.r (.x21, fun a => off (scr a) oDig) (by simp [sregs0])
  · rw [O.get .x23]; exact h.r (.x23, fun a => a.gpr .x1) (by simp [sregs0])
  · exact x24
  · rw [x25]; show _ = BitVec.ofNat 64 (kA a - loA a - D - 1)
    rw [show kA a - loA a - (D + 2) + 1 = kA a - loA a - D - 1 by omega_arith]

theorem clearY_sct {T : Tabs} {D : Nat} :
    RelCT isa (Two (SR T D (sregs D) sslots)) clearY (Two (SR T D (sregs D) sslots)) :=
  two_post (two_taint [.x20] (SR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun _ _ h => WP.mono_syms (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ sy =>
      h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy

section
variable {T : Tabs} {H : Hash} (hH : HashOK H)

include hH in
theorem copyDigest_sct :
    RelCT isa (Two (SR T H.D (sregs H.D) sslots)) (copyDigest H) (Two (SR T H.D (sregs H.D) sslots)) := by
  refine two_post ?_ fun a u h => WP.mono_syms (copyDigest_ok hH h.L (fun _ _ => rfl) (dig := a.gpr .x2)
    (h.sl (sDig, fun a => a.gpr .x2) (by simp [sslots])) h.dig.1 h.dig.2) fun _ ⟨k, f, _⟩ sy =>
      h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := SR T H.D (sregs H.D ++ [(.x11, fun a => a.gpr .x2)]) sslots)
    (two_taint [] (pins_nil SR.sp) (by taint_decide)) (fun a u h => ?_)
    (two_taintE [.x11, .x20] (SR.pins fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x11] := nk_of (by decide)
  unfold ld
  refine WP.of_syms ?_
  refine wp_ldrSp (by decide) (by rw [h.L.sp]; exact h.L.fld (by decide)) fun u' o e =>
    wp_nil fun sy => (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_) (fun q hq => by rw [o.mem]; exact h.sl q hq) sy (by rw [o.mem]; exact Frame.refl _ _))
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sl (sDig, fun a => a.gpr .x2) (by simp [sslots])

/-- After the salt's address, place and length are loaded. -/
def rsY (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x11, fun a => a.gpr .x3), (.x14, fun a => off (scr a) (oY + 8 + D)), (.x12, fun a => a.gpr .x4)]

include hH in
theorem copySaltY_sct :
    RelCT isa (Two (SR T H.D (sregs H.D) sslots)) (copySaltY H) (Two (SR T H.D (sregs H.D) sslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  refine two_post ?_ fun a u h => WP.mono_syms (copySaltY_ok hH h.L (fun _ _ => rfl) (q := a.gpr .x3) (sl := slA a)
    (h.sl (sSalt, fun a => a.gpr .x3) (by simp [sslots]))
    (by rw [h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [sslots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    h.sl_le h.salt.1 h.salt.2) fun _ ⟨k, f, _⟩ sy => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy
  unfold copySaltY
  refine two_step (Ψ := SR T H.D (rsY H.D) sslots)
    (two_taintE [] (pins_nil SR.sp) (c' := Code.eraseOff (.block [ld .x11 sSalt, .addImm .x .x14 .x20 (oY + 8 + zH.D),
      ld .x12 sSaltLen])) rfl (by taint_decide)) (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x11, .x14, .x12] := nk_of (by decide)
    unfold ld
    refine WP.of_syms ?_
    refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun u₁ o₁ e₁ => wp_addImm (by unfold oY; omega_arith)
      fun u₂ o₂ e₂ => wp_ldrSp (by decide) (by rw [o₂.sp, o₂.rd, o₂.wr, o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide))
        fun u₃ o₃ e₃ => wp_nil fun sy => ?_
    obtain O : Only [.x11, .x14, .x12] u u₃ := (o₁.trans (o₂.trans o₃)).mono
    refine h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) (fun q hq => by rw [O.mem]; exact h.sl q hq) sy (by rw [O.mem]; exact Frame.refl _ _)
    rcases List.mem_append.mp hq with hq | hq
    · rw [O.get q.1 (nk q hq)]; exact h.r q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · rw [o₃.get .x11, o₂.get .x11, e₁, h.L.sp]; exact h.sl (sSalt, fun a => a.gpr .x3) (by simp [sslots])
      · rw [o₃.get .x14, e₂, o₁.get .x20, h.L.x20]
      · rw [e₃, o₂.mem, o₁.mem, o₂.sp, o₁.sp, h.L.sp]
        exact h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [sslots])
  · have p12 : ∀ a s, SR T H.D (rsY H.D) sslots a s → s.gpr .x12 = a.gpr .x4 := fun a s h =>
      h.r (.x12, fun a => a.gpr .x4) (by simp [rsY])
    refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, p12 a s₁ h₁, p12 a s₂ h₂])
      (two_taint [] (fun a s₁ s₂ h₁ h₂ => pins_nil SR.sp a s₁ s₂ h₁.1 h₂.1) (by taint_decide))
      (two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ => SR.pins (rs := rsY H.D) (fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp [rsY]) a s₁ s₂ h₁.1 h₂.1) (by taint_decide))

/-- After `signLen`: `ℓ` and the number of blocks of `M'`. -/
def rsL (D : Nat) : List (Reg × (State → BitVec 64)) := sregs D ++ [(.x22, fun a => BitVec.ofNat 64 (8 + D + slA a))]
def slL (H : Hash) : List (Nat × (State → BitVec 64)) := sslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]

include hH in
theorem signLen_sct :
    RelCT isa (Two (SR T H.D (sregs H.D) sslots)) (.block (signLen H)) (Two (SR T H.D (rsL H.D) (slL H))) := by
  refine two_post (two_taintE [] (pins_nil SR.sp) (c' := Code.eraseOff (.block (signLen zH))) rfl (by taint_decide))
    fun a u h => WP.mono_syms (signLen_ok hH h.L (sl := slA a)
      (by rw [h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [sslots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
      h.sl_le) fun u' ⟨k, x22, m⟩ sy => h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_) sy
        (by rw [m]; exact (frame_slot _ _ sNb _).mono (by simp [mgfWr]))
  · have nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x9, .x22, .x16] := nk_of (by decide)
    rcases List.mem_append.mp hq with hq | hq
    · rw [k.get q.1 (nk q hq)]; exact h.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · rw [m, slot_keep (frame_slot _ _ sNb _) fun r hr => ?_]
      · exact h.sl q hq
      rw [List.mem_singleton.mp hr]
      simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

theorem sslots_fb : ∀ q ∈ sslots, q.1 + 8 ≤ frameBytes := by
  intro q hq
  simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

theorem sregs_cs : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28] := by
  decide

theorem clearEm_sct {T : Tabs} {D : Nat} :
    RelCT isa (Two (SR T D (sregs D) sslots)) clearEm (Two (SR T D (sregs D) sslots)) :=
  two_post (two_taint [.x20, .x23] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [sregs]) (by taint_decide))
    fun a _ h => WP.mono_syms (clearEm_ok h.L (fun _ _ => rfl) (k := kA a) (h.x23 (by simp [sregs]))
      (by have := h.ok.k1; omega_arith) h.ok.k2) fun _ ⟨k, f, _⟩ sy => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy

/-- In `putSalt`, after `x14 := DB + dbLen` and the salt's length, and after
the `0x01` and the salt's address. -/
def rsP1 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x14, fun a => off (scr a) (oEm + loA a + dbA D a)), (.x12, fun a => a.gpr .x4)]
def rsP2 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x11, fun a => a.gpr .x3), (.x14, fun a => off (scr a) (oEm + loA a + dbA D a - slA a)),
    (.x12, fun a => a.gpr .x4)]

theorem sl_ofNat (a : State) : a.gpr .x4 = BitVec.ofNat 64 (slA a) := by
  rw [slA, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem putSalt_sct {T : Tabs} {D : Nat} :
    RelCT isa (Two (SR T D (sregs D) sslots)) putSalt (Two (SR T D (sregs D) sslots)) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  obtain x24 : ∀ {rs : List (Reg × (State → BitVec 64))} {a u : State}, SR T D (sregs D ++ rs) sslots a u →
      u.gpr .x24 = off (scr a) (oEm + loA a) := fun h =>
    h.r (.x24, fun a => off (scr a) (oEm + loA a)) (List.mem_append_left _ (by simp [sregs]))
  obtain x25 : ∀ {rs : List (Reg × (State → BitVec 64))} {a u : State}, SR T D (sregs D ++ rs) sslots a u →
      u.gpr .x25 = BitVec.ofNat 64 (dbA D a) := fun h =>
    h.r (.x25, fun a => BitVec.ofNat 64 (dbA D a)) (List.mem_append_left _ (by simp [sregs]))
  refine two_post ?_ fun a u h => ?_
  rotate_left
  · have hf := h.ok.fit; have hk2 := h.ok.k2
    have hdb : dbA D a = kA a - loA a - D - 1 := rfl
    exact WP.mono_syms (putSalt_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA D a) (q := a.gpr .x3)
      (sl := slA a) (x24 (rs := []) (by rw [List.append_nil]; exact h)) (x25 (rs := []) (by rw [List.append_nil]; exact h))
      (h.sl (sSalt, fun a => a.gpr .x3) (by simp [sslots]))
      ((h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [sslots])).trans (sl_ofNat a))
      (by omega_arith) (by omega_arith) h.salt.1 h.salt.2) fun _ ⟨k, f, _⟩ sy =>
        h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy
  unfold putSalt
  refine RelCT.seq_block_append (M := isa) (l₁ := [.add .x .x14 .x24 .x25, ld .x12 sSaltLen]) ?_
  refine two_step (Ψ := SR T D (rsP1 D) sslots) (two_taint [] (pins_nil SR.sp) (by taint_decide))
    (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs D, q.1 ∉ [Reg.x14, .x12] := nk_of (by decide)
    unfold ld
    refine WP.of_syms ?_
    refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide) (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide))
      fun u₂ o₂ e₂ => wp_nil fun sy => ?_
    obtain O : Only [.x14, .x12] u u₂ := (o₁.trans o₂).mono
    refine h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) (fun q hq => by rw [O.mem]; exact h.sl q hq) sy (by rw [O.mem]; exact Frame.refl _ _)
    rcases List.mem_append.mp hq with hq | hq
    · rw [O.get q.1 (nk q hq)]; exact h.r q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [o₂.get .x14, e₁, x24 (rs := []) (by rw [List.append_nil]; exact h),
          x25 (rs := []) (by rw [List.append_nil]; exact h), off_add]
      · rw [e₂, o₁.mem, o₁.sp, h.L.sp]; exact h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [sslots])
  refine two_step (Ψ := SR T D (rsP2 D) sslots) (two_taint [.x12, .x14] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [rsP1]) (by taint_decide)) (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs D, q.1 ∉ [Reg.x14, .x9, .x11] := nk_of (by decide)
    obtain hf := h.ok.fit; have hk2 := h.ok.k2
    have hdb : dbA D a = kA a - loA a - D - 1 := rfl
    obtain x14 : u.gpr .x14 = off (scr a) (oEm + loA a + dbA D a) :=
      h.r (.x14, fun a => off (scr a) (oEm + loA a + dbA D a)) (by simp [rsP1])
    obtain x12 : u.gpr .x12 = a.gpr .x4 := h.r (.x12, fun a => a.gpr .x4) (by simp [rsP1])
    unfold ld
    refine WP.of_syms ?_
    refine wp_sub fun u₃ o₃ e₃ => wp_subImm (by decide) fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => ?_
    obtain h14 : u₅.gpr .x14 = off (scr a) (oEm + loA a + dbA D a - slA a - 1) := by
      rw [o₅.get .x14, e₄, e₃, x14, x12, sl_ofNat, off_sub _ (by omega_arith), off_sub _ (by omega_arith)]
    obtain O₅ : Only [.x14, .x9] u u₅ := (o₃.trans (o₄.trans o₅)).mono
    refine wp_strb (by decide) (by rw [h14, BitVec.add_zero]) (by rw [O₅.wr]; exact h.L.st (by omega_arith))
      fun u₆ m₆ => wp_addImm (by decide) fun u₇ o₇ e₇ => wp_ldrSp (by decide)
        (by rw [o₇.sp, o₇.rd, o₇.wr, m₆.sp, m₆.rd, m₆.wr, O₅.sp, O₅.rd, O₅.wr]; exact ld_slot h.L (by decide))
        fun u₈ o₈ e₈ => wp_nil fun sy => ?_
    obtain K : Keep [.x14, .x9, .x11] u u₈ := (O₅.keep.trans (m₆.keep.trans (o₇.keep.trans o₈.keep))).mono
    obtain hm : u₈.mem = u.mem.writeW (off (scr a) (oEm + loA a + dbA D a - slA a - 1)) (1 : Byte) := by
      rw [o₈.mem, o₇.mem, m₆.mem, O₅.mem, e₅]; rfl
    obtain hfr := wS_frame u.mem (scr a) (x := oEm + loA a + dbA D a - slA a - 1) (by omega_arith) (1 : Byte)
    refine h.congr K.sp K.rd K.wr (K.get .x20) (fun q hq => ?_) (fun q hq => ?_) sy
      (by rw [hm]; exact hfr.mono (by simp [mgfWr]))
    · rcases List.mem_append.mp hq with hq | hq
      · rw [K.get q.1 (nk q hq)]; exact h.r q (List.mem_append_left _ hq)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [e₈, o₇.mem, m₆.mem, O₅.mem, o₇.sp, m₆.sp, O₅.sp, h.L.sp, ← O₅.mem, ← m₆.mem, ← o₇.mem, ← o₈.mem, hm,
            slot_keep hfr (h.L.slotSd (by decide))]
          exact h.sl (sSalt, fun a => a.gpr .x3) (by simp [sslots])
        · rw [o₈.get .x14, e₇, m₆.gpr, h14, off_add, show oEm + loA a + dbA D a - slA a - 1 + 1 =
            oEm + loA a + dbA D a - slA a by omega_arith]
        · rw [K.get .x12]; exact x12
    · rw [hm, slot_keep hfr (sslots_S h.L q hq)]; exact h.sl q hq
  obtain p12 : ∀ a s, SR T D (rsP2 D) sslots a s → s.gpr .x12 = a.gpr .x4 := fun a s h =>
    h.r (.x12, fun a => a.gpr .x4) (by simp [rsP2])
  exact two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, p12 a s₁ h₁, p12 a s₂ h₂])
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => pins_nil SR.sp a s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    (two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ => SR.pins (rs := rsP2 D) (fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [rsP2]) a s₁ s₂ h₁.1 h₂.1) (by taint_decide))

include hH in
theorem putH_sct :
    RelCT isa (Two (SR T H.D (sregs H.D) sslots)) (putH H) (Two (SR T H.D (sregs H.D) sslots)) := by
  have c1 : oEm = 2560 := rfl
  refine two_post (two_taintE [.x20, .x21, .x23, .x24, .x25] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [sregs])
    (c' := Code.eraseOff (putH zH)) rfl (by taint_decide)) fun a u h => ?_
  obtain hf := h.ok.fit; have hk2 := h.ok.k2
  have hdb : dbA H.D a = kA a - loA a - H.D - 1 := rfl
  exact WP.mono_syms (putH_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (k := kA a)
    (h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [sregs]))
    (h.r (.x25, fun a => BitVec.ofNat 64 (dbA H.D a)) (by simp [sregs]))
    (h.r (.x21, fun a => off (scr a) oDig) (by simp [sregs])) (h.x23 (by simp [sregs])) (by omega_arith) (by omega_arith) hk2)
    fun _ ⟨k, f, _⟩ sy => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L) sy

/-- After `mgfXor`: `DB`'s place. -/
def rsT : List (Reg × (State → BitVec 64)) := [(.x24, fun a => off (scr a) (oEm + loA a))]

theorem clearTop_sct {T : Tabs} {D : Nat} : RelCT isa (Two (SR T D rsT [])) (.block clearTop) fun _ _ => True :=
  two_taint [.x24] (SR.pins fun r hr => by simp at hr; subst hr; simp [rsT]) (by taint_decide)

end

namespace SR
variable {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
  {a u : State} (h : SR T D rs sl a u)
include h

/-- The addresses of the tables' functions are the anchor's. -/
theorem names : ∀ n ∈ T.names, u.syms n = a.syms n := by
  obtain ⟨s, t₀, e, h0, _, sy, _, _⟩ := h.ex
  exact fun n hn => by rw [sy, h0.sy]; exact e.sym hn

/-- The slots of the table of `MdHash`. -/
theorem ht : HT T.H T.dn T.f (fb a) u.mem u.syms := by
  obtain ⟨s, t₀, e, h0, fm, sy, _, _⟩ := h.ex
  obtain L0 := lay_of e.1 h0.e.sp h0.e.x20 h0.e.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L0
  obtain h1 := ht_of e.2.2.1 h0
  rw [e.fb] at h1
  rw [sy]
  exact h1.stepW L0 fm

/-- Where MGF1 works, and the table of `MdHash`. -/
theorem env : Env T.G T.g u (fb a) (scr a) (stackArg a 1) := by
  obtain ⟨s, t₀, e, h0, fm, sy, hrd, hwr⟩ := h.ex
  obtain L0 := lay_of e.1 h0.e.sp h0.e.x20 h0.e.wr
  obtain E0 := env_of e.1 e.2.2.1 h0
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L0 E0
  rw [e.arg (j := 1) (by decide)] at E0
  exact E0.step L0 fm (hrd.trans h0.e.rd.symm) (hwr.trans h0.e.wr.symm) sy

end SR

theorem ctHash_sct {T : Tabs} (hH : HashOK T.H) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (SR T T.H.D (rsL T.H.D) (slL T.H))) (ctHash T.f T.H) (Two (SR T T.H.D (sregs T.H.D) sslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  obtain hlg : 2 ^ lgB T.H = T.H.P.B ∧ lgB T.H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  obtain hb : ∀ a : State, slA a ≤ 1024 → 8 + T.H.D + slA a + 1 + T.H.P.L ≤ nbA T.H a * T.H.P.B ∧ nbA T.H a * T.H.P.B ≤ 2048 :=
    fun a hs => by
      obtain hnb1 := Nat.lt_div_mul_add (a := 8 + T.H.D + slA a + T.H.P.L) (b := T.H.P.B) hB0
      obtain hnb2 := Nat.div_mul_le_self (8 + T.H.D + slA a + T.H.P.L) T.H.P.B
      obtain hnbB : ((8 + T.H.D + slA a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B =
          (8 + T.H.D + slA a + T.H.P.L) / T.H.P.B * T.H.P.B + T.H.P.B := Nat.succ_mul _ _
      show _ ≤ ((8 + T.H.D + slA a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ∧ ((8 + T.H.D + slA a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ≤ 2048
      rw [hnbB]; omega_arith
  obtain x19 : ∀ {a u : State}, SR T T.H.D (rsL T.H.D) (slL T.H) a u → u.gpr .x19 = off (scr a) oSt := fun h =>
    h.r (.x19, fun a => off (scr a) oSt) (by simp [rsL, sregs])
  obtain x21 : ∀ {a u : State}, SR T T.H.D (rsL T.H.D) (slL T.H) a u → u.gpr .x21 = off (scr a) oDig := fun h =>
    h.r (.x21, fun a => off (scr a) oDig) (by simp [rsL, sregs])
  obtain x22 : ∀ {a u : State}, SR T T.H.D (rsL T.H.D) (slL T.H) a u → u.gpr .x22 = BitVec.ofNat 64 (8 + T.H.D + slA a) :=
    fun h => h.r (.x22, fun a => BitVec.ofNat 64 (8 + T.H.D + slA a)) (by simp [rsL])
  obtain nb : ∀ {a u : State}, SR T T.H.D (rsL T.H.D) (slL T.H) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (nbA T.H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (nbA T.H a)) (by simp [slL])
  refine two_post (two_map (fun a => (⟨fb a, scr a, nbA T.H a, none, a.syms T.H.initN, a.syms T.H.compN, a.syms T.dn⟩ : HA)) (fun a u h => {
      L := h.L
      x19 := x19 h
      x21 := x21 h
      nb := nb h
      len := ⟨8 + T.H.D + slA a, x22 h, (hb a h.sl_le).1⟩
      hnb := (hb a h.sl_le).2
      fx := fun _ e => nomatch e
      ht := h.ht
      ai := h.names _ (by simp [Tabs.names])
      ac := h.names _ (by simp [Tabs.names])
      ad := h.names _ (by simp [Tabs.names]) }) (ctHash_ct hH hc hdo)) fun a u h => ?_
  have hs := h.sl_le
  refine WP.mono_syms (ctHashWith_out hH (pad80 T.H) h.L (fun _ _ => rfl) (x19 h) (x21 h) (x22 h) (nb h) (hb a hs).1
    (hb a hs).2 (fun L' R' h22' hNb' => ?_) h.ht hdo) fun u' O sy => ?_
  · exact WP.mono (pad80_ok T.H L' R' hlg.1 hlg.2 (by omega_arith) (hb a hs).2 (by have := (hb a hs).1; omega_arith) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) (fun q hq => ?_) sy (O.fr.mono (by simp [mgfWr]))
  · rw [O.cs q.1 (sregs_cs _ (sregs_fst hq))]; exact h.r q (List.mem_append_left _ hq)
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (sslots_fb q hq))
    · exact slot_not_below _ (sslots_fb q hq)

theorem mgfXor_sct {T : Tabs} {Gs : Spec.Mgf1.Hash} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
    (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) :
    RelCT isa (Two (SR T T.H.D (sregs T.H.D) sslots)) (mgfXor T.H T.g) (Two (SR T T.H.D rsT [])) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  obtain hd : ∀ a : State, SOk T.H.D a → DbAt T.H.D (oEm + loA a) (dbA T.H.D a) := fun a ok => by
    obtain hf := ok.fit; have hk2 := ok.k2
    have hdb : dbA T.H.D a = kA a - loA a - T.H.D - 1 := rfl
    exact ⟨by omega_arith, by omega_arith, by omega_arith⟩
  obtain g : ∀ {a u : State}, SR T T.H.D (sregs T.H.D) sslots a u → u.gpr .x24 = off (scr a) (oEm + loA a) ∧
      u.gpr .x25 = BitVec.ofNat 64 (dbA T.H.D a) := fun h =>
    ⟨h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [sregs]),
      h.r (.x25, fun a => BitVec.ofNat 64 (dbA T.H.D a)) (by simp [sregs])⟩
  refine two_post (two_map (fun a => (⟨fb a, scr a, oEm + loA a, dbA T.H.D a, stackArg a 1, a.syms T.G.initN,
      a.syms T.G.updN, a.syms T.G.finN⟩ : MA))
    (fun a u h => ⟨h.L, hd a h.ok, (g h).1, (g h).2, h.env, h.names _ (by simp [Tabs.names]),
      h.names _ (by simp [Tabs.names]), h.names _ (by simp [Tabs.names])⟩) (mgfXor_ct hGm (H := T.H)))
    fun a u h => WP.mono (mgfXor_ok hGm hGh hGl hGv h.L (fun _ _ => rfl) (hd a h.ok) (g h).1 (g h).2 h.env)
      fun u' ⟨sp, rd, wr, cs, _, fr, sy, _⟩ => h.congr sp rd wr (cs .x20 (by decide) (by decide)) (fun q hq => ?_)
        (fun _ h => absurd h List.not_mem_nil) sy fr
  rw [List.mem_singleton.mp hq]
  exact (cs .x24 (by decide) (by decide)).trans (g h).1

/-- The encoding is constant time. -/
theorem encEnc_ct {T : Tabs} {Gs : Spec.Mgf1.Hash} (hH : HashOK T.H)
    (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x)
    (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (SR T T.H.D (sregs0 T.H.D) sslots)) (signEnc T.f T.H T.g) fun _ _ => True := by
  unfold signEnc seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  exact RelCT.seq dbRegs_sct (RelCT.seq clearY_sct (RelCT.seq (copyDigest_sct hH) (RelCT.seq (copySaltY_sct hH)
    (RelCT.seq (signLen_sct hH) (RelCT.seq (ctHash_sct hH hc hdo) (RelCT.seq clearEm_sct (RelCT.seq putSalt_sct
      (RelCT.seq (putH_sct hH) (RelCT.seq (mgfXor_sct hGm hGh hGl hGv) clearTop_sct)))))))))

end VG.Proof.RsaPss.AArch64.Enc

end

end

/-! ### `RsaPss.AArch64.EncTop`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's encoding on AArch64: the whole function

`code_ok`: from the precondition, `encode` keeps the calling convention and
returns 1 with `em` holding `Spec.RsaPss.encode`'s encoding, or 0 if the
salt does not fit (`Post`): the prologue (`prologue_ok`), the checks of the
lengths (`body_ok`), and the restores (`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (fitH_ok saltFits_ok restore_frame_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb stk)

/-- The result, and the calling convention. -/
def Post (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ OutOk D Hs Gs s s'.mem (s'.gpr .x0)

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the prologue and `fitH`: the checks of the lengths, then the
encoding or 0. -/
theorem body_ok {tsH tsG : List FnTable} {s u : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtT s u)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x1).toNat)
    (h10 : (u.gpr .x10 != 0) = decide ((s.gpr .x1).toNat < H.D + 2)) :
    WP isa (.ite (.nonzero .x .x10) ret0 (seqs [.block ([ld .x12 sSaltLen] ++ saltFits H),
      .ite (.nonzero .x .x10) ret0 (encMain f H g)])) u fun t => MidE s t ∧ OutOk H.D Hs Gs s t.mem (t.gpr .x0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  have hel := hp.hel
  refine WP.ite _ (eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h10, decide_eq_true_eq] at hb
    exact ret0_ok hu.e (RsaPss.encode_none₂ Hs Gs (by rw [hsl, ← hel, hHl]; omega_using [hb]))
  rw [h10, decide_eq_false_iff_not] at hb
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (saltFits_ok H hD (F := fb s) hu.e.sp
    (by rw [hu.e.rd, hu.e.wr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide))))
    (a := (s.gpr .x1).toNat) (sl := (s.gpr .x4).toNat) (by omega_using [hb]) (by omega_using [hk2]) h9
    (by rw [hu.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (s.gpr .x4).isLt) fun u₃ ⟨O₃, x9₃, x10₃⟩ sy₃ => ?_)
  have hu₃ := hu.only O₃ sy₃
  refine WP.ite _ (eval_nonzero _ _) (fun hb₃ => ?_) (fun hb₃ => ?_)
  · rw [x10₃, decide_eq_true_eq] at hb₃
    exact ret0_ok hu₃.e (RsaPss.encode_none₂ Hs Gs (by rw [hsl, ← hel, hHl]; omega_using [hb₃]))
  rw [x10₃, decide_eq_false_iff_not] at hb₃
  exact encMain_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht hu₃ x9₃ (by omega_using [hb, hb₃])

include hH hHs hHl hHv hGh hGl hGv hdo in
theorem code_ok {tsH tsG : List FnTable} {s : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) : WP isa (encode f H g) s (Post H.D Hs Gs s) := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  have hk2 := hp.k2
  unfold encode
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega_using [this]) ?_
  unfold encBody seqs seqs seqs
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_
  refine WP.mono (tabSlots_ok hp hu (by rw [sy]; simp [allocated])) fun u₀ hu₀ => ?_
  refine WP.mono_syms (fitH_ok H hD (k := (s.gpr .x1).toNat)
    (by rw [hu₀.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk2])) fun u₁ ⟨O₁, x9₁, x10₁⟩ sy₁ => ?_
  refine WP.seq (WP.mono (body_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht (hu₀.only O₁ sy₁) x9₁ x10₁)
    fun t ⟨m, r⟩ => ?_)
  refine WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, hmem⟩ mm uu fl =>
    ⟨⟨habi.1, habi.2.1, habi.2.2⟩, ?_⟩
  -- The encoded message lies apart from the frame, whose bytes the `free` loses.
  have hb : Spec.Rsa.bytesAt mm (s.gpr .x0) (s.gpr .x1).toNat =
      Spec.Rsa.bytesAt (freed frameBytes w).mem (s.gpr .x0) (s.gpr .x1).toNat :=
    List.map_congr_left fun i hi => lost_byte (R := emR s) fl
      (hp.ke.symm.sub_right (Offset.sub_below s.sp (by unfold stk; omega_arith) (by unfold stk; omega_arith)))
      (List.mem_range.mp hi)
  show OutOk _ Hs Gs s mm ((freed frameBytes w).gpr .x0)
  rw [hx0]
  unfold OutOk
  rw [hb, hmem]; exact r

end

end VG.Proof.RsaPss.AArch64.Enc

end

end

/-!
# EMSA-PSS's encoding on AArch64: constant time

`code_ct`: two runs of `encode` from entry states with the same public data
leak the same trace. The prologue and the checks of the lengths branch on
the lengths only (the taint analysis, and correctness for the branches); the
encoding is `encEnc_ct`; the copy to `em` loads `em` from its slot, public by
correctness (`copyArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off two_taintE two_step pins_nil zH PssChecks fitH_ok saltFits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- `a; (b; c)` as `(a; b); c`. -/
theorem relct_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

/-- 0 returned: the stack pointer is kept. -/
theorem ret0_ct {Φ : State → State → Prop} (hΦ : ∀ a u, Φ a u → u.sp = fb a) :
    RelCT isa (Two Φ) ret0 (Two fun a t => t.sp = fb a) :=
  two_post (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [hΦ a s₁ h₁, hΦ a s₂ h₂]) (by taint_decide))
    fun a u h => by
      unfold ret0
      exact wp_movz fun t o _ => wp_nil (by rw [o.sp, hΦ a u h])

/-- After the checks of the lengths. -/
structure AtM (D : Nat) (s w : State) : Prop where
  e : AtT s w
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (D + 2))
  fit : D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat

/-- The encoding's start. -/
theorem sr_of {T : Tabs} {a w : State} (h : ∃ s, E T a s ∧ AtM T.H.D s w) :
    SR T T.H.D (sregs0 T.H.D) sslots a w := by
  obtain ⟨s, e, hm⟩ := h
  have hp := e.1
  have hk1 := hp.k1; have hk2 := hp.k2
  have hf := hm.fit
  have L := lay_of hp hm.e.e.sp hm.e.e.x20 hm.e.e.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L
  have h1 := e.gpr (r := .x1) (by decide)
  have h4 := e.gpr (r := .x4) (by decide)
  refine ⟨⟨s, w, e, hm.e, Frame.refl _ _, rfl, hm.e.e.rd, hm.e.e.wr⟩, L, fun q hq => ?_, fun q hq => ?_,
    ⟨?_, ?_, ?_⟩, rfl⟩
  · simp only [sregs0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [hm.e.e.x19]; exact congrArg (off · oSt) e.scr
    · rw [hm.e.e.x21]; exact congrArg (off · oDig) e.scr
    · rw [hm.e.e.x23, h1]
    · rw [hm.x9, h1]; rfl
  · simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact (hm.e.e.fr.rs (.x2, sDig) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact (hm.e.e.fr.rs (.x3, sSalt) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact (hm.e.e.fr.rs (.x4, sSaltLen) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact hm.e.e.lo
  · show 1 ≤ (a.gpr .x1).toNat; rw [← h1]; exact hk1
  · show (a.gpr .x1).toNat ≤ 1024; rw [← h1]; exact hk2
  · show T.H.D + (a.gpr .x4).toNat + 2 ≤ (a.gpr .x1).toNat - 0
    rw [← h1, ← h4]; omega_using [hf]

section
variable {T : Tabs} (hH : HashOK T.H) (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
  {Hs Gs : Spec.Mgf1.Hash} (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x)
  (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P)

include hH hHs hGh hGl hGv hc hdo in
/-- After the checks: the encoding, its copy and 1. -/
theorem main_ct : RelCT isa (Two fun a w => ∃ s, E T a s ∧ AtM T.H.D s w) (encMain T.f T.H T.g)
    fun _ _ => True := by
  unfold encMain seqs seqs
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E T a s ∧ AtCopy s (encF Hs Gs T.H.D s) t)
    (two_map (fun a => a) (fun a w h => sr_of h) (encEnc_ct hH hGm hGh hGl hGv hc hdo))
    fun a w ⟨s, e, hm⟩ => WP.mono (enc_ok hH hGm hHs hGh hGl hGv hdo e.1 e.2.2.1 hm.e hm.x9 hm.fit)
      fun t ht => ⟨s, e, ht⟩) ?_
  unfold copyOut
  refine relct_assoc' (two_step (Ψ := fun a u => u.sp = fb a ∧ u.gpr .x11 = off (scr a) oEm ∧
      u.gpr .x14 = a.gpr .x0 ∧ u.gpr .x12 = a.gpr .x1)
    (two_taint [] (pins_nil fun a s₁ s₂ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ => by rw [h₁.sp, h₂.sp, e₁.fb, e₂.fb])
      (by taint_decide))
    (fun a t ⟨s, e, ht⟩ => WP.mono (copyArgs_ok e.1 ht) fun u ⟨O, h11, h14, h12⟩ =>
      ⟨by rw [O.sp, ht.sp, e.fb], by rw [h11, ← e.scr], by rw [h14, e.gpr (by decide)],
        by rw [h12, e.gpr (by decide)]⟩)
    (two_taint [.x11, .x14, .x12] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.1, h₂.1], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]⟩) (by taint_decide)))

include hH hHs hGh hGl hGv hc hdo in
theorem code_ct : RelCT isa (Two (E T)) (encode T.f T.H T.g) fun _ _ => True := by
  have hD : T.H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  unfold encode
  refine two_alloc (R := fun _ _ => True) ?_
  unfold encBody seqs seqs seqs
  rw [show encPrologue ++ tabSlots ++ fitH T.H = (encPrologue ++ [arg .x9 0]) ++ (tabSlots.tail ++ fitH T.H) from rfl]
  refine RelCT.seq_block_append ?_
  refine RelCT.seq (two_post (Ψ := fun a u₁ => ∃ s u, E T a s ∧ AtE s u ∧ Only [.x9] u u₁ ∧
      u₁.gpr .x9 = stackArg s 0 ∧ u₁.syms = s.syms)
    (two_taintE [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.1.sp, h₂.2.1.sp],
        fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (encPrologue ++ [arg .x9 0]))) rfl (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    rw [WP.block_append_iff]
    exact WP.mono_syms (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun t ht sy =>
      WP.mono_syms (arg0_ok h.1 ht) fun u₁ ⟨o, e9⟩ sy' => ⟨s, t, h, ht, o, e9, sy'.trans sy⟩
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtT s u ∧
      u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ (u.gpr .x10 != 0) = decide ((s.gpr .x1).toNat < T.H.D + 2))
    (two_taintE [.x9] (fun _ u₁ u₂ ⟨s₁, v₁, h₁, j₁, o₁, x₁, _⟩ ⟨s₂, v₂, h₂, j₂, o₂, x₂, _⟩ =>
        ⟨by rw [o₁.sp, o₂.sp, j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => by
          rw [List.mem_singleton.mp hr, x₁, x₂, h₁.arg (by decide), h₂.arg (by decide)]⟩)
      (c' := Code.eraseOff (.block (tabSlots.tail ++ fitH zH))) rfl (by taint_decide))
    fun a u₁ ⟨s, u, h, hu, o, e9, sy⟩ => ?_) ?_
  · have hk2 := h.1.k2
    rw [WP.block_append_iff]
    exact WP.mono (tabSlotsT_ok h.1 hu o e9 sy) fun u₀ hu₀ =>
      WP.mono_syms (fitH_ok T.H hD (k := (s.gpr .x1).toNat) (by rw [hu₀.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
        (by omega_using [hk2])) fun t' ⟨O, x9, x10⟩ sy' => ⟨s, h, hu₀.only O sy', x9, x10⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, x₁⟩ ⟨s₂, h₂, _, _, x₂⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x1) (by decide), h₂.gpr (r := .x1) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.e.sp, h.fb]) ?_
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, E T a s ∧ AtT s w ∧
      w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (T.H.D + 2)) ∧
      (w.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - (T.H.D + 2) < (s.gpr .x4).toNat) ∧
      ¬ (s.gpr .x1).toNat < T.H.D + 2)
    (two_taintE [] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.e.sp, j₂.e.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block ([ld .x12 sSaltLen] ++ saltFits zH))) rfl (by taint_decide))
    fun a u ⟨⟨s, h, j, x9, x10⟩, hb⟩ => ?_) ?_
  · rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    have hk2 := h.1.k2
    exact WP.mono_syms (saltFits_ok T.H hD (F := fb s) j.e.sp
      (by rw [j.e.rd, j.e.wr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide))))
      (a := (s.gpr .x1).toNat) (sl := (s.gpr .x4).toNat) (by omega_using [hb]) (by omega_using [hk2]) x9
      (by rw [j.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (s.gpr .x4).isLt) fun w ⟨O, x9', x10'⟩ sy => ⟨s, h, j.only O sy, x9', x10', hb⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, x₁, _⟩ ⟨s₂, h₂, _, _, x₂, _⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x1) (by decide), h₂.gpr (r := .x1) (by decide),
        h₁.gpr (r := .x4) (by decide), h₂.gpr (r := .x4) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.e.sp, h.fb]) ?_
  have hm : ∀ a w, ((∃ s, E T a s ∧ AtT s w ∧ w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (T.H.D + 2)) ∧
      (w.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - (T.H.D + 2) < (s.gpr .x4).toNat) ∧
      ¬ (s.gpr .x1).toNat < T.H.D + 2) ∧ isa.eval (.nonzero .x .x10) w = some false) →
      ∃ s, E T a s ∧ AtM T.H.D s w := fun a w ⟨⟨s, h, j, x9, x10, hk⟩, hb⟩ => by
    rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    exact ⟨s, h, j, x9, by omega_using [hk, hb]⟩
  exact two_post (two_map (fun a => a) hm (main_ct hH hGm hHs hGh hGl hGv hc hdo)) fun a w hw => by
    obtain ⟨s, h, m⟩ := hm a w hw
    unfold encMain seqs seqs
    exact WP.seq (WP.mono (enc_ok hH hGm hHs hGh hGl hGv hdo h.1 h.2.2.1 m.e m.x9 m.fit) fun t ht =>
      WP.mono (copy_ok' h.1 ht) fun t' ⟨mt, _⟩ => by rw [mt.sp, h.fb])

end

end VG.Proof.RsaPss.AArch64.Enc
