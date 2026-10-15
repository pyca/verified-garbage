module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A reusable rejection segment with an existing accepted prefix -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem Env.transfer {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s u : State}
    (h : Env N B bP aP s) (hm : u.mem=s.mem) (hr : u.rd=s.rd) (hw : u.wr=s.wr)
    (h16 : u.gpr .x16=s.gpr .x16) : Env N B bP aP u := by
  refine ⟨⟨?_,?_,?_,h.disj,h.bound⟩,?_,?_,?_,?_,?_⟩
  · simpa only [hm] using h.buf
  · simpa only [hr,hw] using h.inb
  · simpa only [hw] using h.ina
  · simpa only [hr,hw] using h.input16
  · simpa only [hw] using h.output16
  · simpa only [hr,hw,h16] using h.tableRead
  · simpa only [hm,h16] using h.tableData
  · simpa only [h16] using h.tableDisj

structure Entry (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr) (s : State) : Prop where
  env : Env N B bP aP s
  constants : Constants s
  len : initial.length≤256
  coeffs : Scalar.Coeffs s.mem aP initial
  x2 : s.gpr .x2=bP
  x3 : s.gpr .x3=coeffAddr aP initial.length
  x4 : (s.gpr .x4).toNat=256-initial.length
  x5 : (s.gpr .x5).toNat=N
  x9 : (s.gpr .x9).toNat=q
  x10 : (s.gpr .x10).toNat=15

theorem Entry.inv {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s : State}
    (h : Entry initial N B bP aP s) : Scalar.Inv initial N B bP aP s 0 s :=
  ⟨⟨rfl,rfl,rfl,h.len,h.x3,h.x4,h.x9,h.coeffs,Frame.refl _ _⟩,Keep.refl _ _,
    by simpa only [Nat.mul_zero,ptr_zero] using h.x2,
    by simpa only [Nat.sub_zero] using h.x5,h.x10⟩

theorem segment_ok {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s : State}
    (h : Entry initial N B bP aP s) (hN : 0<N) (hm : N%4=0) :
    WP isa Impl.MlKem.AArch64.Rej8.rejLoop s (Post initial N B aP s) :=
  loop_ok h.env hN hm h.inv h.constants

theorem segment_relCT {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s u : State} (hs : Entry initial N B bP aP s) (hu : Entry initial N B bP aP u)
    (hsp : s.sp=u.sp) (htab : s.gpr .x16=u.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (fun a b => a=s ∧ b=u) Impl.MlKem.AArch64.Rej8.rejLoop
      (fun a b => Post initial N B aP s a ∧ Post initial N B aP u b) :=
  RelCT.mono (loop_relCT hs.env hu.env hsp htab hN hm)
    (by intro a b h; rcases h with ⟨rfl,rfl⟩; exact ⟨hs.inv,hu.inv,hs.constants,hu.constants⟩)
    (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8
