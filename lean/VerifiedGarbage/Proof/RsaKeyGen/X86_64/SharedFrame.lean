module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Preserve policy inputs around the shared round's private stack -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure SharedEnv (B : Addr) (Z : Nat) (sp : Addr) (s : State) : Prop where
  room : Caller.Room s B Z
  rsp : s.gpr .rsp = sp
  clear : Clear (below sp 128) s

theorem SharedEnv.kept {B sp : Addr} {Z : Nat} {s t : State} {rs : List Reg}
    (h : SharedEnv B Z sp s) (hk : Keep rs s t) (hsp : Reg.rsp ∉ rs) : SharedEnv B Z sp t := by
  have ht : t.gpr .rsp = s.gpr .rsp := hk.gpr hsp
  refine ⟨⟨by rw [ht]; exact h.room.size, by rw [ht]; exact h.room.disjoint⟩,
    ht.trans h.rsp, ?_⟩
  intro r hr
  rw [hk.2.1, hk.2.2] at hr
  exact h.clear r hr

theorem SharedEnv.back {B sp : Addr} {Z : Nat} {s t : State} {rs : List Reg}
    (h : SharedEnv B Z sp t) (hk : Keep rs s t) (hsp : Reg.rsp ∉ rs) : SharedEnv B Z sp s := by
  have ht : t.gpr .rsp = s.gpr .rsp := hk.gpr hsp
  refine ⟨⟨by rw [← ht]; exact h.room.size, by rw [← ht]; exact h.room.disjoint⟩,
    ht.symm.trans h.rsp, ?_⟩
  intro r hr
  apply h.clear r
  rw [hk.2.1, hk.2.2]
  exact hr

abbrev SharedFrame (B sp : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  WorkFrame B rs [below sp 128] m m'

theorem SharedFrame.word {B sp : Addr} {Z d : Nat} {s : State} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : SharedFrame B sp rs m m') (he : SharedEnv B Z sp s)
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hf : d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d := by
  apply h.word_eq hd hf hn
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [← he.rsp]
  exact he.room.disjoint

theorem SharedFrame.array {B sp : Addr} {Z d k : Nat} {s : State} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : SharedFrame B sp rs m m') (he : SharedEnv B Z sp s)
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hf : d + 8 * k ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : wv m' B d k = wv m B d k := by
  apply h.wv_eq hd hf hn
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [← he.rsp]
  exact he.room.disjoint

theorem _root_.VG.Proof.Bignum.X86_64.Src.shared
    {s t : State} {B sp p : Addr} {Z : Nat} {bs : List Byte} {rs : List (Nat × Nat)}
    {regs : List Reg} (h : Src s B Z p bs) (he : SharedEnv B Z sp s)
    (hf : SharedFrame B sp rs s.mem t.mem) (hfit : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (hk : Keep regs s t) : Src t B Z p bs := by
  refine ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact h.rd i hi, ?_, h.out⟩
  intro i hi
  rw [hf (p + BitVec.ofNat 64 i) ?_ ?_]
  · exact h.val i hi
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact he.clear.miss (fun _ h => h) (h.rd i hi) (by simp)
  · intro r hr
    exact Or.inr (Nat.le_trans (hfit r hr) (h.out i hi))

end VG.Proof.RsaKeyGen.X86_64
