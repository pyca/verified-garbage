module

public import VerifiedGarbage.Proof.Dsa.AArch64.KeygenEntry
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.Layout

/-! # AAPCS64 argument capture for DSA key derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def deriveFieldValues (original : State) (qlen B : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .x2
  | .q => original.gpr .x2 + original.gpr .x4
  | .g => original.gpr .x2 + original.gpr .x4 + qlen
  | .y => B + BitVec.ofNat 64 derivedY
  | .x => original.gpr .x5
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => original.gpr .x0
  | .pLen => original.gpr .x4
  | .qLen => qlen
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

abbrev deriveFields := Generate.deriveFields

def deriveFieldMem (mem : Mem) (B out p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW
    (off B Field.digest.offset) (0#64)).writeW (off B Field.digestLen.offset) (0#64)).writeW
    (off B Field.out.offset) out).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem deriveFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block deriveFields) s fun t =>
      t.mem = deriveFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold deriveFields Generate.deriveFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .signature, field_enc .nonce, field_enc .digest, field_enc .digestLen,
    field_enc .out, field_enc .p, field_enc .pLen, field_enc .qLen,
    hw .signature, hw .nonce, hw .digest, hw .digestLen, hw .out, hw .p, hw .pLen, hw .qLen]
  rfl

theorem deriveTail_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block [SignVerify.initial .x5 .x, movi .x3 derivedY,
      .add .x .x3 .x11 .x3, SignVerify.initial .x3 .y]) s fun t =>
      t.mem = (s.mem.writeW (off B Field.x.offset) (s.gpr .x5)).writeW (off B Field.y.offset)
        (B + BitVec.ofNat 64 derivedY) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .x, field_enc .y, hw .x, hw .y]
  rfl

theorem deriveMoveScratch_ok (s : State) :
    WP isa (.block [mov .x11 .x7]) s fun t =>
      t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  brun []

theorem deriveEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h7 : s0.gpr .x7 = B) :
    WP isa (.block Generate.deriveEntry) s0 (KeygenEntryPost s0 B (deriveFieldValues s0 (s0.gpr .x6) B true)) := by
  unfold Generate.deriveEntry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (deriveMoveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h7] at h11
  rw [WP.block_append_iff]
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  refine WP.mono (deriveFields_ok (hs.congr hk1.wr) h11 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x4 (by decide), hreg .x6 (by decide)] at hmem3
  have hk123 := hk1.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (deriveFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x6)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x2) (pl := s0.gpr .x4) (ql := s0.gpr .x6) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  have h5 : s4.gpr .x5 = s0.gpr .x5 := hk1234.gpr .x5 (by decide)
  refine WP.mono (deriveTail_ok (hs.congr hk1234.wr) h114 (by decide)) fun t ⟨hmem5, hk5⟩ => ?_
  rw [h5] at hmem5
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [deriveFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, deriveFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega
    rw [hmem5, hmem4, hmem3]
    simp only [deriveFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

end VG.Proof.Dsa.AArch64
