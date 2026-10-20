module
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyState

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyDerive
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublishValue
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)]) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧ u.zf = some (t.gpr .rax == 1) ∧
      Keep [.rax] t u := by
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧
    u.zf = some (t.gpr .rax == 1)) ?_ rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]
  exact sub_beq_zero _ _

theorem keygen_keepStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block GenerateKey.keepStatus) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64) ∧
      Keep [.rax] t u := by
  refine WP.keep [.rax] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64)) ?_ rfl
  unfold GenerateKey.keepStatus
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega)) (by omega)) hk (by rw [hmx])

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 24 t.mem u.mem)
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega)) (by omega)) hk
    (by rw [hmx])

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
  simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .rsi).toNat 0))

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveKey v.sq v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k)
      KeygenState h used u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat = res.getD (List.replicate (s.gpr .rsi).toNat 0) := by
  refine WP.seq (WP.mono_mx (by decide) (keygen_deriveArgs_saved ht.scr ht.sp ht.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ hmxa => ?_)
  have ha := ht.of_outgoing hargs (hka.mono (by decide)) hmxa
  have hnA : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k := by
    have hq : (stackArg s 0).toNat ≤ 32 := by
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega
    exact (random_outside_bytes hargs (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega) (Or.inr (show 0 + 24 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 ha.rd ha.wr)
    fun b ⟨hbr, hbw, hbc, hf, hst, hout, hmxb⟩ => ?_)
  rw [keygen_bytes_params ha, hnA] at hst hout
  have hoF : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackOut.sub_left (keygen_frame_sub h)).symm
  have hsF : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hb, _⟩ := ha.after_call (wr := keygenDeriveWr s)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hoF
      · exact hsF)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outParams
      · exact h.paramsScratch.symm)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outRand
      · exact h.randScratch.symm)
    hf hbr hbw hbc hmxb
  refine WP.mono_mx (by decide) (keygen_keepStatus_ok hb.scr hb.sp) fun u ⟨hum, hku⟩ hmxu => ?_
  refine ⟨hb.write_status hum (hku.mono (by decide)) hmxu, ?_, ?_⟩
  · rw [hum, word_writeW_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), ← BitVec.toNat_setWidth, hst]
    exact (Nat.mod_eq_of_lt (by unfold Spec.Dsa.signStatus; split <;> decide)).symm
  · rw [hum, random_writeW_bytes _ (hoF.sep (Region.contains_self _ _)
      (Offset.contains_base (randomBase s) (d := Random.oStatus) (n := 8) (by decide) (by decide)))
      (s.gpr .rsi).isLt]
    exact hout

end VG.Proof.Dsa.X86_64
