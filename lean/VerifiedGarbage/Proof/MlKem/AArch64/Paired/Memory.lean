module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector

import VerifiedGarbage.Proof.Framework.Offset

/-! # Preserve independent paired-sampler streams and checkpoints -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem checkpoint_frame {w16 : Bool} {m m' : Mem} {p a : Addr} {L : List Zq} {rs : List Region}
    (h : checkpointW w16 p a L m) (hf : Frame rs m m')
    (hd : ∀r∈rs,(Region.mk p 16).Disjoint r) : checkpointW w16 p a L m' := by
  constructor
  · have hc : (Region.mk p 16).Contains p 8 := by
      simpa only [BitVec.add_zero] using Offset.contains_base p (d := 0) (by decide : 0+8≤16) (by decide)
    rw [hf.readW hc hd (by decide)]
    exact h.1
  · have hc : (Region.mk p 16).Contains (p+8) 8 := Offset.contains_base p (by decide) (by decide)
    rw [hf.readW hc hd (by decide)]
    exact h.2

theorem coeffs_frame {w16 : Bool} {m m' : Mem} {p : Addr} {L : List Zq} {rs : List Region}
    (h : Rej8.Scalar.CoeffsW w16 m p L) (hl : L.length≤256) (hf : Frame rs m m')
    (hd : ∀r∈rs,(polyRegion p).Disjoint r) : Rej8.Scalar.CoeffsW w16 m' p L := by
  intro i hi
  rw [coeffAtW_frame hf hd (by omega)]
  exact h i hi

end VG.Proof.MlKem.AArch64.Paired

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem EnvW.frame {w16 : Bool} {s u : State} {N : Nat} {B : Nat → Byte} {p a : Addr} {rs : List Region}
    (h : EnvW w16 N B p a s) (hr : u.rd=s.rd) (hw : u.wr=s.wr) (h16 : u.gpr .x16=s.gpr .x16)
    (hf : Frame rs s.mem u.mem)
    (hb : ∀r∈rs,(Region.mk p (3*N+4)).Disjoint r)
    (ht : ∀mask<256,∀r∈rs,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint r) :
    EnvW w16 N B p a u := by
  refine ⟨⟨?_,?_,?_,h.disj,h.bound⟩,?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [hf.bytes (R := ⟨p,3*N+4⟩) hb (by change 3*N+4≤2^64; have := h.bound; omega) (by omega : i<3*N+4)]
    exact h.buf i hi
  · simpa only [hr,hw] using h.inb
  · simpa only [hw] using h.ina
  · simpa only [hr,hw] using h.input16
  · simpa only [hw] using h.output16
  · simpa only [hr,hw,h16] using h.tableRead
  · intro mask hm
    rw [h16,hf.read (Region.contains_self _ _) (ht mask hm) (by decide)]
    exact h.tableData mask hm
  · simpa only [h16] using h.tableDisj

theorem Env.frame {s u : State} {N : Nat} {B : Nat → Byte} {p a : Addr} {rs : List Region}
    (h : Env N B p a s) (hr : u.rd=s.rd) (hw : u.wr=s.wr) (h16 : u.gpr .x16=s.gpr .x16)
    (hf : Frame rs s.mem u.mem)
    (hb : ∀r∈rs,(Region.mk p (3*N+4)).Disjoint r)
    (ht : ∀mask<256,∀r∈rs,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint r) :
    Env N B p a u := EnvW.frame h hr hw h16 hf hb ht

end VG.Proof.MlKem.AArch64.Rej8
