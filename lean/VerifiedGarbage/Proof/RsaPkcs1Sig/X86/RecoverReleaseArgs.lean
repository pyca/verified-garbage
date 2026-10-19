module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStatus
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigestArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Preserve the acceptance bit and prepare a masked trailing-digest copy -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover

def accepted (g : Geometry) (s : State) : Bool :=
  decide (s.gpr .ebp = 0) && (savedStatus g s).getLsbD 0

theorem acceptance_bit (x y : BitVec 32) :
    BitVec.ofNat 32 (decide (x = 0)).toNat &&& y =
      BitVec.ofNat 32 (decide (x = 0) && y.getLsbD 0).toNat := by
  cases eq : decide (x = 0) with
  | false => change 0#32 &&& y = 0#32; exact BitVec.zero_and
  | true =>
    change 1#32 &&& y = BitVec.ofNat 32 (y.getLsbD 0).toNat
    rw [BitVec.and_comm, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
    cases y.getLsbD 0 <;> rfl

def releaseSetup : List Instr :=
  [.mov .ebx (.reg .eax), .mov .edx (.imm 0), .alu .sub .edx (.reg .eax),
    .mov .edi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1))] ++ digestPtr

theorem releaseSetup_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} {good : Bool}
    (h : Context g bs s) (status : s.gpr .eax = BitVec.ofNat 32 good.toNat) :
    WP isa (.block releaseSetup) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.ebx, .edx, .edi, .ecx, .esi] s t ∧ t.gpr .ebx = BitVec.ofNat 32 good.toNat ∧
      t.gpr .edx = -BitVec.ofNat 32 good.toNat ∧ t.gpr .edi = g.output ∧
      t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  unfold releaseSetup
  rw [WP.block_append_iff]
  refine wp_movS rfl fun a A _ => ?_
  refine wp_movS rfl fun b B _ => ?_
  refine wp_subS rfl fun c C _ => ?_
  have K : Keeps [.ebx, .edx, .edi, .ecx, .esi] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M := C.mem.trans (B.mem.trans A.mem)
  have hc := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold incoming stackAt
  refine wp_ldm rfl (hc.readArg (by decide : 0 < 13)) fun d D => ?_
  have hd := hc.after (by rw [D.mem]; exact Frame.refl _ _) D.keeps (D.other .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 1 < 13)) fun e E => WP.block_nil ?_
  have ke := K.trans ((D.keeps.mono (by decide)).trans (E.keeps.mono (by decide)))
  have me := E.mem.trans (D.mem.trans M)
  have he := h.after (by rw [me]; exact Frame.refl _ _) ke (ke.1 .esp (by decide))
  refine WP.mono (digestPtr_ok he) ?_
  rintro t ⟨ht, Mt, Kt, ptr⟩
  refine ⟨ht, Mt.trans me, ke.trans (Kt.mono (by decide)), ?_, ?_, ?_, ?_, ptr⟩
  · rw [Kt.1 .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.gpr, status]
  · rw [Kt.1 .edx (by decide), E.other .edx (by decide), D.other .edx (by decide), C.gpr, B.gpr,
      B.other .eax (by decide), A.other .eax (by decide), status]
    change 0#32 - BitVec.ofNat 32 good.toNat = _
    rw [BitVec.zero_sub]
  · rw [Kt.1 .edi (by decide), E.other .edi (by decide), D.gpr, hc.argumentValue (by decide : 0 < 13)]
    rfl
  · rw [Kt.1 .ecx (by decide), E.gpr, hd.argumentValue (by decide : 1 < 13)]
    rfl

theorem releaseArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block releaseArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .edx, .edi, .ecx, .esi] s t ∧
      t.gpr .ebx = BitVec.ofNat 32 (accepted g s).toNat ∧
      t.gpr .edx = -BitVec.ofNat 32 (accepted g s).toNat ∧ t.gpr .edi = g.output ∧
      t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  change WP isa (.block (VG.Impl.RsaPkcs1Sig.X86.Verify.result ++ releaseSetup)) s _
  rw [WP.block_append_iff]
  refine WP.mono (result_ok h) ?_
  rintro a ⟨ha, M, K, value⟩
  have ax : a.gpr .eax = BitVec.ofNat 32 (accepted g s).toNat := value.trans (acceptance_bit _ _)
  refine WP.mono (releaseSetup_ok ha ax) ?_
  rintro t ⟨ht, Mt, Kt, good, mask, dst, cnt, src⟩
  exact ⟨ht, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide)), good, mask, dst, cnt, src⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
