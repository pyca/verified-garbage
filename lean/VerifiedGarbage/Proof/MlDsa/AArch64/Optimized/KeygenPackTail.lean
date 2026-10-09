import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def tailResult (nb : Nat) (m : Mem) (out : Addr) (acc : BitVec 64) : Mem × BitVec 64 :=
  let off := nb/8*8
  let rem := nb%8
  let m1 := if rem≥4 then m.writeW (out+BitVec.ofNat 64 off) (acc.setWidth 32) else m
  let a1 := if rem≥4 then acc>>>32 else acc
  let p := out+BitVec.ofNat 64 (off+rem/4*4)
  let m2 := if rem%4≥2 then (m1.writeW p (a1.setWidth 8)).writeW (p+1) ((a1>>>8).setWidth 8) else m1
  let a2 := if rem%4≥2 then a1>>>16 else a1
  let m3 := if rem%2=1 then m2.writeW (out+BitVec.ofNat 64 (nb-1)) (a2.setWidth 8) else m2
  (m3,a2)

def TailWidth (nb : Nat) : Prop := nb=3 ∨ nb=6 ∨ nb=9 ∨ nb=10 ∨ nb=13

theorem tail_ok (nb : Nat) (hn : TailWidth nb) (s : State)
    (hw : ∀off sz,off+sz≤nb → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz) :
    WP isa (.block (tail nb)) s fun t =>
      ((t.mem=(tailResult nb s.mem (s.gpr .x2) (s.gpr .x9)).1 ∧
        t.gpr .x9=(tailResult nb s.mem (s.gpr .x2) (s.gpr .x9)).2) ∧
       Keep [.x9] s t) ∧ t.v=s.v := by
  rcases hn with rfl|rfl|rfl|rfl|rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 : InRegions s.wr (s.gpr .x2) 1 := by simpa using hw 0 1 (by decide)
    have h1 := hw 1 1 (by decide)
    have h2 := hw 2 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,h2,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 : InRegions s.wr (s.gpr .x2) 4 := by simpa using hw 0 4 (by decide)
    have h1 := hw 4 1 (by decide)
    have h2 := hw 5 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,h2,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 1 (by decide)
    have h1 := hw 9 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 4 (by decide)
    have h1 := hw 12 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl


end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
