module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Sha3.Arith

/-! # Padding preserves the hash workspace and establishes the permutation input -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64

theorem pad_kept {s : State} {sc : Reg} {st wk rate pos sfx : Nat}
    (hs : HSetup sc st wk rate s) (hp : pos<rate) (hoff : st+rate≤4096) :
    WP isa (.block (padCode sc st rate pos sfx)) s fun t=>
      Kept [STr sc st s] s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Spec.Sha3.stateAt t.mem (s.gpr sc+BitVec.ofNat 64 st)=
        Proof.Sha3.xorByte (Proof.Sha3.xorByte (Spec.Sha3.stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st))
          pos (BitVec.ofNat 8 sfx)) (rate-1) 128 := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  have ne : ∀r∈preserved,r≠Reg.x9 ∧ r≠Reg.x10 := by decide
  refine WP.mono (pad_ok (ne _ hs.hsc.1).1 (ne _ hs.hsc.1).2 (by omega) (by omega) hp hoff
    (fun a n h=>hs.cov a n (by
      obtain ⟨r,hr,hc⟩:=h
      exact ⟨r,List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)),hc⟩))) fun t ⟨hk,hf,he⟩=>?_
  exact ⟨⟨fun r hr _=>hk.get r (by have hh:=ne r hr; simp [hh.1,hh.2]),
    hk.sp,hk.rd,hk.wr,hf,hk.vcs⟩,hk.get .x30 (by decide),he⟩

theorem pad_repr {s : State} {sc : Reg} {st wk rate pos sfx : Nat} {msg : List Byte}
    (hs : HSetup sc st wk rate s) (hoff : st+rate≤4096)
    (repr : Spec.Sha3.Repr s.mem (s.gpr sc+BitVec.ofNat 64 st) rate msg)
    (hp : pos=msg.length%rate) :
    WP isa (.block (padCode sc st rate pos sfx)) s fun t=>
      Kept [STr sc st s] s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Spec.Sha3.keccakF (Spec.Sha3.stateAt t.mem (s.gpr sc+BitVec.ofNat 64 st))=
        Spec.Sha3.absorb rate (Spec.Sha3.pad rate (BitVec.ofNat 8 sfx) msg) := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  refine WP.mono (pad_kept hs (by rw [hp]; exact Nat.mod_lt _ (by omega)) hoff) fun t ⟨hk,h30,he⟩=>?_
  refine ⟨hk,h30,?_⟩
  rw [he,hp,repr,Proof.Sha3.absorb_pad (by omega) (by omega)]
  rfl

end VG.Proof.MlKem.AArch64.FixedHash
