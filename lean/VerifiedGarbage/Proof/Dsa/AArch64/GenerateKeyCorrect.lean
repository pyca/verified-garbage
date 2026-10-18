module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBody
import VerifiedGarbage.Proof.Framework.Omega

/-! # Key generation's functional correctness against its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveKey v.mul)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

theorem keygen_depth (v : Backend) :
    16 * (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveKey v.mul)).aarch64Depth ≤ v.stack + 256 := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.aarch64Depth,
    show Random.prepare.aarch64Depth = 0 from rfl,
    show Random.sample.aarch64Depth = 0 from rfl,
    show RandomSign.finish.aarch64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  change 16 * (max (Generate.checkParameters v.mul).aarch64Depth
    (Generate.deriveKey v.mul).aarch64Depth + 16) ≤ _
  rw [Nat.mul_add, ← Nat.mul_max_mul_left]
  exact Nat.add_le_add_right (Nat.max_le.mpr ⟨v.parametersDepth, v.deriveDepth⟩) 256

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.key.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveKey v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht => ⟨ht.sp, ht.wr, ?_⟩
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ht.output, ht.used,
    ht.callee, ?_, ht.vectors, ht.nonce⟩
  change t.sp + BitVec.ofNat 64 Random.frameBytes = s.sp
  rw [ht.sp, randomBase, BitVec.sub_add_cancel]

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.mul) (Generate.deriveKey v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, keygen_shared_post h hp⟩

end VG.Proof.Dsa.AArch64
