module

public import VerifiedGarbage.Proof.Ed25519.AArch64.PointDecode
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyTbl
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
import VerifiedGarbage.Proof.Framework.Lit

/-! The verification inputs remain readable and outside the workspace. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, h.sp, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scr s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarQ : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  challengeQ : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)
  /-- The static of the cached `-[1]B … -[15]B`, which the equation copies. -/
  tbl : BTblAt s base (s.syms bSym)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) (k : VerifyKeep base s t) (hy : t.syms = s.syms) :
    VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar,
    by rw [hy]; exact h.tbl.of_powers k (by decide)⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarQ _ ‹_›
  · exact h.challengeQ _ ‹_›

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

end VG.Proof.Ed25519.AArch64
