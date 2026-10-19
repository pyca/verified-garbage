module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Save
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_finish`

The code copies the chaining value to `out`, computes the number of bytes
held back, and runs `finalize` with the state as its key and `out` as its
state: its result is the MAC of the message the state represents
(`repr_finish`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64
open VG.Impl.CmacTripleDes.X86_64 (at_)
open VG.Proof.CmacTripleDes.X86_64 (offset_nat)
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`) and the scratch
buffer `S`. -/
structure HPre (s₀ : State) (St O S : Addr) : Prop where
  rdi : s₀.gpr .rdi = St
  rdx : s₀.gpr .rdx = O
  rcx : s₀.gpr .rcx = S
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 416⟩, ⟨O, 8⟩, ⟨S, 640⟩]
  st_o : (⟨St, 416⟩ : Region).Disjoint ⟨O, 8⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  o_s : (⟨O, 8⟩ : Region).Disjoint ⟨S, 640⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 416⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 8⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wO : O.toNat + 8 ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64

theorem HPre.of {s₀ : State} (h : finishX86_64.pre s₀) : HPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k⟩

/-- The memory after copying the chaining value to `out`. -/
def copyCv (m : Mem) (O St : Addr) : Mem := m.writeW O (m.readW (St + BitVec.ofNat 64 400) 64)

theorem copyCv_bytes (m : Mem) (O St : Addr) :
    Spec.Aes.bytesAt (copyCv m O St) O 8 = Spec.Aes.bytesAt m (St + BitVec.ofNat 64 400) 8 := by
  rw [copyCv, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW]

theorem copyCv_frame (m : Mem) (O St : Addr) : Frame [⟨O, 8⟩] m (copyCv m O St) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem finishPre_ok {s₀ : State} {St O S : Addr} (hp : HPre s₀ St O S) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = O ∧
      s₁.gpr .rdx = St + BitVec.ofNat 64 408 ∧ s₁.gpr .rcx = s₀.gpr .rsi ∧ s₁.gpr .r8 = S ∧
      (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧ s₁.zf = some (s₀.gpr .rsi == 0) ∧
      s₁.mem = copyCv s₀.mem O St ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have r₁ : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 400) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by omega)⟩
  have w₁ : InRegions s₀.wr O 8 := by
    rw [hp.wr]; exact ⟨⟨O, 8⟩, by simp, Region.contains_self _ _⟩
  have k0 : O + BitVec.ofNat 64 0 = O := BitVec.add_zero O
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, finishPre, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hp.rdi, hp.rdx, k0, r₁, w₁]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, BitVec.and_self, hp.rdi, hp.rcx,
    sx408]
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, rfl, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 408) S (held (s₀.gpr .rsi).toNat)
  mem : s.mem = copyCv s₀.mem O St
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {L : Nat} (hp : HPre s₀ St O S) (hL : L ≤ 8)
    (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = O) (rdx : s.gpr .rdx = St + BitVec.ofNat 64 408)
    (rcx : s.gpr .rcx = BitVec.ofNat 64 L) (r8 : s.gpr .r8 = S) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 408) S L := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 408, L⟩ ⟨St, 416⟩ := Offset.sub_base St (by omega)
  exact
  { rdi := rdi, rsi := rsi, rdx := rdx, rcx := rcx, r8 := r8, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    retSt := by rw [rsp]; exact hp.ret_o
    retS := by rw [rsp]; exact hp.ret_s
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega⟩
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : Addr} (hp : HPre s₀ St O S) :
    WP isa finPre s₀ (HMid s₀ St O S) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rsi).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ ?_ r8₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, rcx₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, rcx₁, sx1, sx7]
    have hne : s₀.gpr .rsi ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .rcx := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ (held_bv _ hne) r8₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

theorem finish_wp {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa finish s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rdx = O at hp
  generalize s₀.gpr .rcx = S at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact copyCv_frame _ _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 8⟩, ⟨S, 640⟩] s₀.mem s₂.mem := (f₁.mono (by simp)).trans h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
  · intro key msg hr hc hlen
    rw [hp.rdi] at hr
    rw [hp.rdx]
    -- The state is unchanged before `finalize`.
    have hr₁ : Spec.Cmac.tdesRepr s₁.mem St key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨St, 416⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
    obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
    rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
    obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
    have hn : (s₀.gpr .rsi).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    have hciph : Proof.CmacTripleDes.X86_64.ciphAt s₁.mem St = Spec.Cmac.tdes key := by
      simp only [Proof.CmacTripleDes.X86_64.ciphAt, hks, Spec.Cmac.tdes]
    have e₂ : Spec.Aes.bytesAt s₁.mem O 8 = Spec.Aes.bytesAt s₁.mem (St + 400) 8 := by
      rw [h₁.mem, copyCv_bytes, show St + 400 = St + BitVec.ofNat 64 400 from rfl]
      exact (Proof.Cmac.bytesAt_frame (copyCv_frame _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_o.sub_left (Offset.sub_base St (d := 400) (n := 8) (by decide))) (by decide)).symm
    have out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, hn, show St + BitVec.ofNat 64 408 = St + 408 from rfl, happ,
      Proof.CmacTripleDes.Stream.tdesCmac_eq]

end VG.Proof.CmacTripleDes.Stream.X86_64
