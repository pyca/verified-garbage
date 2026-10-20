module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Save
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Inline
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_stream_init`

The code zeroes the chaining value and runs `init` with the state as its
`out`, which writes the key schedule and the subkeys before it: the state
then represents the empty message.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64
open VG.Impl.CmacTripleDes.X86_64 (at_)
open VG.Proof.CmacTripleDes.X86_64 (offset_nat)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rsi : s₀.gpr .rsi = Kp
  rdx : (s₀.gpr .rdx).toNat = KL
  rcx : s₀.gpr .rcx = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 640⟩]
  st_k : (⟨St, 416⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 640⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 416⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64
  klen : Spec.TripleDes.validKey KL

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k⟩

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem := m.writeW (St + BitVec.ofNat 64 400) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zeroCv_bytes (m : Mem) (St : Addr) :
    Spec.Aes.bytesAt (zeroCv m St) (St + BitVec.ofNat 64 400) 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64]; decide

theorem zeroCv_frame (m : Mem) (St : Addr) : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] m (zeroCv m St) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧
      s₁.gpr .rdx = St ∧ s₁.gpr .rcx = S ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = zeroCv s₀.mem St ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hKL : s₀.gpr .rdx = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rdx, toNat_ofNat (by rcases hp.klen with h | h <;> omega)])
  have w : InRegions s₀.wr (St + BitVec.ofNat 64 400) 8 := by
    rw [hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by have := hp.wSt; omega)⟩
  refine ⟨_, by
    simp only [initPre, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32,
      State.setReg32, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg, wr_setReg,
      reduceCtorEq, ↓reduceIte, hp.rdi, w]
    rfl, ?_⟩
  simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, hp.rsi, hKL]
  refine ⟨trivial, trivial, trivial, hp.rcx, fun r hr => ?_, rfl, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem init_wp {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa streamInit s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rsi = Kp at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rdx).toNat = KL at hp
  have hw := hp.wSt
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, sv₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  have oSt : Region.Sub ⟨St, 400⟩ ⟨St, 416⟩ := Region.sub_prefix (by decide)
  have args : IArgs s₁ Kp St S KL :=
    { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      retO := by rw [rsp₁]; exact hp.ret_st.sub_right oSt
      retS := by rw [rsp₁]; exact hp.ret_s
      wrapK := hp.wK
      wrapO := by omega
      wrapS := hp.wS
      reads := by
        rw [rd₁, wr₁, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩ }
  refine WP.mono (init_inline_wp args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, sv₁ r hr], ?_⟩, ?_⟩
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [h₂.frame.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_st.sub_right oSt
        · exact hp.ret_s) (by decide),
      f₁.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_st.sub_right (Offset.sub_base St (by decide))) (by decide)]
  · show Spec.Cmac.tdesRepr s₂.mem (s₀.gpr .rdi) (Spec.TripleDes.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .rdx).toNat) []
    rw [hp.rdi, hp.rsi, hp.rdx, Proof.CmacTripleDes.Stream.repr_iff]
    have hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL := by
      simp only [Spec.TripleDes.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      exact f₁.bytes (R := ⟨Kp, KL⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_k.symm.sub_right (Offset.sub_base St (by decide)))
        (by show KL ≤ 2 ^ 64; have := hp.wK; omega)
        (List.mem_range.mp hi)
    have hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
    obtain ⟨hs, hk⟩ := h₂.out
    rw [hkey] at hs hk
    refine ⟨⟨by rw [hlen]; exact hp.klen, hs, hk⟩, ?_, by
      simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
    rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl,
      Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base St (d := 400) (by decide) (by decide)
        · exact (hp.st_s.sub_left (Offset.sub_base St (by decide)))) (by decide), m₁, zeroCv_bytes]
    rfl

end VG.Proof.CmacTripleDes.Stream.X86_64
