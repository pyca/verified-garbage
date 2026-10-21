module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar

/-! # Combine a checked bit with the persistent RSA validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem withFlag_ok {s : State} {B : Addr} {Z n value : Nat} {c : Prog isa}
    (bit : slot s.mem B kOk ≤ 1) (valueBit : value ≤ 1)
    (correct : WP isa c s fun u => Ws u B Z n 32 ∧ Keep B n [] [kFlag] s.mem u.mem ∧
      slot u.mem B kFlag = value ∧ Keeps [.eax] s u) :
    WP isa (withFlag c) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧ value = 1 then 1 else 0) ∧ Keeps [.eax] s t := by
  unfold withFlag andFlag
  refine WP.seq (WP.mono correct fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  refine WP.mono (andS_ok hu (by decide) (by decide) (by decide)
    (by rw [maskU]; exact bit) (by rw [flag]; exact valueBit)) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  exact ⟨ht, Ou.join Ot (js := []) (ds := [kFlag, kOk]), by rw [mask, maskU, flag], Ku.trans Kt⟩

theorem maskFlag_preserves_e {m m' : Mem} {B : Addr} {n : Nat}
    (O : Keep B n [] [kFlag, kOk] m m') : val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  change r ∈ [] ++ [(kFlag, 4), (kOk, 4)] at hr
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  all_goals exact Or.inl (by decide)

end VG.Proof.RsaKeyGen.X86.Key
