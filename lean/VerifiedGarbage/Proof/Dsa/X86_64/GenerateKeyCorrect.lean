module
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck

import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Key generation's functional correctness against its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveKey v.sq v.mul)).all (fun i => !isa.writesSp i) = true := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.all, Bool.and_eq_true]
  repeat' constructor
  all_goals first | exact v.parametersSp | exact v.deriveSp | decide

theorem keygen_depth (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveKey v.sq v.mul)).x86_64Depth ≤ v.stack + 256 := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.x86_64Depth,
    show Random.prepare.x86_64Depth = 0 from rfl,
    show Random.sample.x86_64Depth = 0 from rfl,
    show RandomSign.finish.x86_64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  have hm := Nat.max_le.mpr ⟨Nat.add_le_add_right v.parametersDepth 8, Nat.add_le_add_right v.deriveDepth 8⟩
  exact Nat.add_le_add_right hm 248

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveKey v.sq v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht => ⟨ht.sp, ht.wr, ?_⟩
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ht.output, ht.used, ?_, ht.mxcsr, ht.nonce⟩
  intro r hr
  by_cases he : r = .rsp
  · subst r
    change t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes = s.gpr .rsp
    rw [ht.sp, randomBase, BitVec.sub_add_cancel]
  · change (t.setReg .rsp (t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes)).gpr r = _
    simp only [State.setReg, ite_eq_right he]
    exact ht.callee r hr he

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.sq v.mul) (Generate.deriveKey v.sq v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  refine ⟨trace, t, he, ⟨hp.callee, ?_, hp.mxcsr⟩, keygen_shared_post h hp⟩
  have hd := keygen_depth v
  have hb := v.stackBound
  have hf := Exec.stackFrame (SpSafe.of_all (keygen_sp v)) he (by omega)
  have hfb := VG.X86_64.Frame.below_mono hf hd (by omega)
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.retOut
    · exact h.retUsed
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by omega)

end VG.Proof.Dsa.X86_64
