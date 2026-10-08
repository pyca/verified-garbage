import VerifiedGarbage.Proof.P256.Linear.Form
import VerifiedGarbage.Proof.P256.Linear.Correction

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem linear129_eq (o a b : Nat) : Impl.P256.Linear.linear129 o a b=
    form129 a b++correction++stores [.x3,.x4,.x5,.x6] o := by
  simp [Impl.P256.Linear.linear129,form129,nineB,times12A,tripleA,complement,
    shift3,addAcc,shift1,addTriple,shift2,correction,loads,stores,ld,st,Nat.add_assoc]

/-- Canonical fused 12A−9B; loads complete before output stores, allowing aliases. -/
theorem linear129_ok {s : State} {base : Addr} {size o a b : Nat}
    (hs : Scr s base size) (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hA : wordsVal s.mem base a 4<p) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (Impl.P256.Linear.linear129 o a b)) s fun t =>
      KeepRegs (clob 4) s t ∧ Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4<p ∧
      wordsVal t.mem base o 4=(12*wordsVal s.mem base a 4+9*(p-wordsVal s.mem base b 4))%p := by
  rw [linear129_eq,List.append_assoc,WP.block_append_iff]
  refine WP.mono (form129_ok hs ha hb ha8 hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  rw [WP.block_append_iff]
  have hn : regsVal s1 [.x3,.x4,.x5,.x6,.x7]<21*p := by rw [e1]; omega
  refine WP.mono (correction_ok s1 z1 hn) fun s2 ⟨e2,k2⟩ => ?_
  have hs2 := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)
  refine WP.mono (stores_ok [.x3,.x4,.x5,.x6] hs2 ho ho8 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  change wordsVal t.mem base o 4=regsVal s2 [.x3,.x4,.x5,.x6] at et
  change Outside base o 32 s2.mem t.mem at ot
  have keep : Keeps (clob 4) s s2 :=
    (k1.mono (by unfold formRegs; decide)).trans (k2.mono (by decide))
  have ek : KeepRegs (clob 4) s s2 := ⟨keep.gpr,keep.rd,keep.wr,keep.sp⟩
  refine ⟨ek.trans (kt.mono (by simp)),?_,?_,?_⟩
  · simpa only [keep.mem] using ot
  · rw [et,e2]; exact Nat.mod_lt _ (by decide)
  · rw [et,e2,e1]

end VG.Proof.P256.Linear
