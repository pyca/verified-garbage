module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Sample
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Framework.Omega

/-! Sampling modifies the private output and its dedicated mask control only. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem sampleFrame_header {p : Parameters} {s t : State} {N i : Nat}
 (scratch : Scr s p.B p.Z) (inside : i<32) (different : i≠sMask)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 word t.mem p.B (8*i)=word s.mem p.B (8*i) := by
 rw [workspace_word (by have := scratch.nowrap;omega) same
  (by have := hdr_lt_slot p.w 8 inside;have := p.room;omega)]
 exact header_other (writeW_outside _ _ _ (by decide : 8*sMask+8≤2^64)) (by decide) inside different

theorem FieldInitial.after_sample {p : Parameters} {s t : State} {N : Nat}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) : FieldInitial p t := by
 have nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega
 have masked := writeW_outside s.mem p.B (sampleMask N) (by decide : 8*sMask+8≤2^64)
 have arrays (a : Nat) (ha : a<8) : wv t.mem p.B (slot p.w a) p.w=wv s.mem p.B (slot p.w a) p.w := by
  have within := Nat.le_trans (slot_le (w:=p.w) ha) p.room
  apply Eq.trans _ (masked.wv (Or.inr (hdr_lt_slot p.w a (show sMask<32 by decide))) (by have := slot_le (w:=p.w) ha;omega))
  apply wv_congr
  intro i hi
  exact workspace_word (by have := field.good.scr.nowrap;omega) same (by omega)
 have wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  rw [workspace_word (by have := field.good.scr.nowrap;omega) same
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.room;have := p.positive;omega)]
  exact masked.word (Or.inr (hdr_lt_slot p.w 0 (show sMask<32 by decide)))
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.positive;omega)
 refine ⟨good,(arrays 0 (by decide)).trans field.modulus,?_,(arrays 4 (by decide)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_sample {p : Parameters} {s t : State} {N k : Nat}
 (h : Controls p.B p.src p.ctx k p.N s) (scratch : Scr s p.B p.Z)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 Controls p.B p.src p.ctx k p.N t :=
 ⟨(sampleFrame_header scratch (by decide) (by decide) same).trans h.context,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.source,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.length,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.bits,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached
