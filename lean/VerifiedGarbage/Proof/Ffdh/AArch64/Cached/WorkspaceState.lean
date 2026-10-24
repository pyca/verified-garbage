module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
import VerifiedGarbage.Proof.Framework.Omega

/-! Context stores preserve every arithmetic value inside the separate workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem workspace_word {B : Addr} {Z d : Nat} {m m' : Mem}
 (size : Z≤2^64) (same : ∀ x,ofs B x<Z→m' x=m x) (inside : d+8≤Z) : word m' B d=word m B d := by
 apply Mem.readW_congr
 intro i hi
 apply same
 rw [ofs_off B (by omega)]
 omega

theorem workspace_array {p : Parameters} {s t : State} {j : Nat}
 (good : Good s p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) (inside : j<8) :
 wv t.mem p.B (slot p.w j) p.w=wv s.mem p.B (slot p.w j) p.w := by
 have arrayRoom := Nat.le_trans (slot_le (w:=p.w) inside) p.room
 apply wv_congr
 intro i hi
 exact workspace_word (by have := good.scr.nowrap;omega) same (by omega)

theorem ModState.after_workspace {p : Parameters} {s t : State} (h : ModState p s)
 (good : Good t p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) : ModState p t := by
 have inverseWord : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) :=
  workspace_word (by have := h.good.scr.nowrap;omega) same
   (by have := slot_le (w:=p.w) (by decide : 0<8);have := p.room;have := p.positive;omega)
 refine ⟨good,(workspace_array h.good same (by decide)).trans h.modulus,?_,
  (workspace_array h.good same (by decide)).trans h.one,(workspace_array h.good same (by decide)).trans h.r2⟩
 rw [inverseWord]
 exact h.inverse

theorem Basis.after_workspace {p : Parameters} {E : Nat} {s t : State} (h : Basis p E s)
 (good : Good t p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) : Basis p E t := by
 have array := workspace_array h.good same (by decide : 5<8)
 exact ⟨h.toModState.after_workspace good same,by rw [array];exact h.bound,array.trans h.value⟩

theorem Power.after_workspace {p : Parameters} {E : Nat} {s t : State} (h : Power p E s)
 (good : Good t p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) : Power p E t := by
 have array := workspace_array h.good same (by decide : 6<8)
 exact ⟨h.toModState.after_workspace good same,by rw [array];exact h.bound,array.trans h.value⟩

theorem Basis.after_header {p : Parameters} {E : Nat} {s t : State} {i : Nat}
 (h : Basis p E s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : Basis p E t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have same : wv t.mem p.B (slot p.w 5) p.w=wv s.mem p.B (slot p.w 5) p.w :=
  frame.wv (Or.inr (hdr_lt_slot _ _ hi)) (by have := slot_le (w:=p.w) (by decide : 5<8);omega)
 exact ⟨h.toModState.after_header good frame hi,by rw [same];exact h.bound,same.trans h.value⟩

theorem workspace_header {p : Parameters} {s t : State} {i : Nat} (good : Good s p.B p.Z p.w p.mi)
 (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) (inside : i<32) : word t.mem p.B (8*i)=word s.mem p.B (8*i) :=
 workspace_word (by have := good.scr.nowrap;omega) same (by have := hdr_lt_slot p.w 8 inside;have := p.room;omega)


end VG.Proof.Ffdh.AArch64.Cached
