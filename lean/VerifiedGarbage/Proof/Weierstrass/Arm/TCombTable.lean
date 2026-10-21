module

import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.List.BasicAux
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.Comb

/-! Read-only comb tables, in the existing architecture-independent word layout. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Weierstrass

structure TableMem (s : State) (T : Addr) (ws : List (BitVec 64)) : Prop where
  fit : T.toNat + 8*ws.length ≤ 2^32
  readable : InRegions (s.rd ++ s.wr) T (8*ws.length)
  words : ∀ i < ws.length, s.mem.readW (T+BitVec.ofNat 64 (8*i)) 64 = ws.getD i 0

theorem TableMem.unch {s t : State} {T : Addr} {ws : List (BitVec 64)}
    (h : TableMem s T ws) (hr : t.rd ++ t.wr = s.rd ++ s.wr)
    (hm : ∀ i < ws.length, ∀ b < 8, t.mem (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b) =
      s.mem (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) : TableMem t T ws :=
  ⟨h.fit, hr ▸ h.readable, fun i hi => by
    rw [← h.words i hi]; exact Mem.readW_congr fun b hb => hm i hi b (by omega)⟩

theorem TableMem.of_frame {s t : State} {T : Addr} {ws : List (BitVec 64)} {L : List Region}
    (h : TableMem s T ws) (hr : t.rd ++ t.wr = s.rd ++ s.wr) (hf : Frame L s.mem t.mem)
    (hd : ∀ r ∈ L, Region.Disjoint ⟨T,8*ws.length⟩ r) : TableMem t T ws :=
  h.unch hr fun i hi b hb => by
    rw [Offset.add_add]
    exact hf.bytes (R := ⟨T,8*ws.length⟩) hd (by have := h.fit; dsimp only; omega)
      (by dsimp only; omega)

theorem TableMem.entry {s : State} {T : Addr} {n R p H J : Nat} {tbl : List (List (Nat × Nat))}
    (hT : TableMem s T (tcombWords n R p tbl)) (hJ : tbl.length=J)
    (hH : ∀ j<J,(tbl.getD j []).length=H) {j m : Nat} (hj : j<J) (hm : m<H)
    (hx : (combAt tbl j m).1*R%p < 2^(64*n)) (hy : (combAt tbl j m).2*R%p < 2^(64*n)) :
    wordsVal s.mem (T+BitVec.ofNat 64 (j*(16*n*H))) (16*n*m) n = (combAt tbl j m).1*R%p ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (j*(16*n*H))) (16*n*m+8*n) n = (combAt tbl j m).2*R%p :=
  tcombWords_entry hT.words hJ hH hj hm hx hy

end VG.Proof.Weierstrass.Arm.TComb
