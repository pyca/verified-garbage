module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr))) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1 ∧
      Keep [.x4, .x15] t u := by
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1)
    ?_ rfl rfl rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]
  rfl

theorem keygen_writeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0)) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ Keep [.x15] t u := by
  refine WP.keep [.x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0)) ?_ rfl rfl rfl
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega)) (by omega)) hk (hf.word (by decide) (by decide))

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 8 t.mem u.mem)
    (hk : Keep randomVolatile t u) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega)) (by omega)) hk
    (hf.word (by decide) (by decide))

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
  apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact ht.params.val i h₂

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .x1).toNat 0))

end VG.Proof.Dsa.AArch64
