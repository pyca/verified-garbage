module
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Implies
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Save
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Inline
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Common
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.CT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch

/-! ### `CmacTripleDes.Stream.X86_64.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.X86_64.Init`, which only this module used -/

section

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
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 120⟩]
  st_k : (⟨St, 416⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 120⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 120⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 416⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 120⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 120 ≤ 2 ^ 64
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
  obtain hKL : s₀.gpr .rdx = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rdx, toNat_ofNat (by rcases hp.klen with h | h <;> omega_using [h])])
  obtain w : InRegions s₀.wr (St + BitVec.ofNat 64 400) 8 := by
    rw [hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by have := hp.wSt; omega_using [])⟩
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
  obtain hp := IPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rsi = Kp at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rdx).toNat = KL at hp
  have hw := hp.wSt
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, sv₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  obtain oSt : Region.Sub ⟨St, 400⟩ ⟨St, 416⟩ := Region.sub_prefix (by decide)
  obtain args : IArgs s₁ Kp St S KL :=
    { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      retO := by rw [rsp₁]; exact hp.ret_st.sub_right oSt
      retS := by rw [rsp₁]; exact hp.ret_s
      wrapK := hp.wK
      wrapO := by omega_using [hw]
      wrapS := hp.wS
      reads := by
        rw [rd₁, wr₁, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 120⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 120⟩, by simp, 0, by simp, by simp⟩ }
  refine WP.mono (init_inline_wp args) fun s₂ h₂ => ?_
  obtain f₁ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
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
    obtain hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL := by
      simp only [Spec.TripleDes.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      exact f₁.bytes (R := ⟨Kp, KL⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_k.symm.sub_right (Offset.sub_base St (by decide)))
        (by show KL ≤ 2 ^ 64; have := hp.wK; omega_using [this])
        (List.mem_range.mp hi)
    obtain hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
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

end

end

/-! ### `CmacTripleDes.Stream.X86_64.Finish`, which only this module used -/

section

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
  wr : s₀.wr = [⟨St, 416⟩, ⟨O, 8⟩, ⟨S, 120⟩]
  st_o : (⟨St, 416⟩ : Region).Disjoint ⟨O, 8⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 120⟩
  o_s : (⟨O, 8⟩ : Region).Disjoint ⟨S, 120⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 416⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 8⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 120⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wO : O.toNat + 8 ≤ 2 ^ 64
  wS : S.toNat + 120 ≤ 2 ^ 64

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
  obtain r₁ : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 400) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by omega_using [])⟩
  obtain w₁ : InRegions s₀.wr O 8 := by
    rw [hp.wr]; exact ⟨⟨O, 8⟩, by simp, Region.contains_self _ _⟩
  obtain k0 : O + BitVec.ofNat 64 0 = O := BitVec.add_zero O
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
  obtain pSt : Region.Sub ⟨St + BitVec.ofNat 64 408, L⟩ ⟨St, 416⟩ := Offset.sub_base St (by omega_using [hL])
  exact
  { rdi := rdi, rsi := rsi, rdx := rdx, rcx := rcx, r8 := r8, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    retSt := by rw [rsp]; exact hp.ret_o
    retS := by rw [rsp]; exact hp.ret_s
    wrapK := by omega_using [hw]
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_using [hL, hw]
    wrapS := hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega_using [hL]⟩
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 120⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 120⟩, by simp, 0, by simp, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : Addr} (hp : HPre s₀ St O S) :
    WP isa finPre s₀ (HMid s₀ St O S) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
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
    obtain hne : s₀.gpr .rsi ≠ 0 := fun e => h0 (by rw [e]; rfl)
    obtain hc : ∀ r ∈ calleeSaved, r ≠ .rcx := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ (held_bv _ hne) r8₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

theorem finish_wp {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa finish s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  obtain hp := HPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rdx = O at hp
  generalize s₀.gpr .rcx = S at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  obtain f₁ : Frame [⟨O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact copyCv_frame _ _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 8⟩, ⟨S, 120⟩] s₀.mem s₂.mem := (f₁.mono (by simp)).trans h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
  · intro key msg hr hc hlen
    rw [hp.rdi] at hr
    rw [hp.rdx]
    -- The state is unchanged before `finalize`.
    obtain hr₁ : Spec.Cmac.tdesRepr s₁.mem St key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨St, 416⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
    obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
    rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
    obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
    obtain hn : (s₀.gpr .rsi).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    obtain hciph : Proof.CmacTripleDes.X86_64.ciphAt s₁.mem St = Spec.Cmac.tdes key := by
      simp only [Proof.CmacTripleDes.X86_64.ciphAt, hks, Spec.Cmac.tdes]
    obtain e₂ : Spec.Aes.bytesAt s₁.mem O 8 = Spec.Aes.bytesAt s₁.mem (St + 400) 8 := by
      rw [h₁.mem, copyCv_bytes, show St + 400 = St + BitVec.ofNat 64 400 from rfl]
      exact (Proof.Cmac.bytesAt_frame (copyCv_frame _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_o.sub_left (Offset.sub_base St (d := 400) (n := 8) (by decide))) (by decide)).symm
    obtain out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, hn, show St + BitVec.ofNat 64 408 = St + 408 from rfl, happ,
      Proof.CmacTripleDes.Stream.tdesCmac_eq]

end VG.Proof.CmacTripleDes.Stream.X86_64

end

end

/-! ### `CmacTripleDes.Stream.X86_64.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.X86_64.AbsorbBlocks`, which only this module used -/

section

@[expose] public section

section

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_absorb`'s saved registers

`absorb` saves the five callee-saved registers it uses at `scratch + 120`,
where the code it runs does not write, and restores them at the end.
-/

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64
open VG.Impl.CmacTripleDes.X86_64 (at_)
open VG.Proof.CmacTripleDes.X86_64 (offset_nat readW_writeW_other)

/-- The memory after saving the registers at `S + 120`. -/
def absSavedMem (s : State) (S : Addr) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (S + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem absSaved_read (s : State) (S : Addr) :
    (absSavedMem s S).readW (S + BitVec.ofNat 64 120) 64 = s.gpr .rbx ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 128) 64 = s.gpr .r12 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 136) 64 = s.gpr .r13 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 144) 64 = s.gpr .r14 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 152) 64 = s.gpr .r15 := by
  simp only [absSavedMem, saved, List.foldl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 120 ≤ d) (h₂ : d + 8 ≤ 160) :
    (⟨b + BitVec.ofNat 64 120, 40⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 120) + BitVec.ofNat 64 (d - 120) from
    (Offset.add_add_eq b (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 120, 40⟩] s.mem (absSavedMem s S) := by
  simp only [absSavedMem, saved, List.foldl]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide)))

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .r8 = S)
    (hw : ∀ d, 120 ≤ d → d + 8 ≤ 160 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .r13 = s.gpr .rdx ∧ s'.gpr .r14 = s.gpr .rcx ∧
      s'.gpr .r15 = S ∧ s'.gpr .rsi = s.gpr .rsi ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rbp = s.gpr .rbp ∧ s'.zf = some (s.gpr .rsi == 0) ∧
      s'.mem = absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, saved, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat, hS,
      hw 120 (by decide) (by decide), hw 128 (by decide) (by decide), hw 136 (by decide) (by decide),
      hw 144 (by decide) (by decide), hw 152 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, BitVec.and_self, hS]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  simp only [absSavedMem, saved, List.foldl]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 120 ≤ d → d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 120) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 128) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 136) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 144) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 152) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.map_some, hb,
      hr 120 (by decide) (by decide), hr 128 (by decide) (by decide), hr 136 (by decide) (by decide),
      hr 144 (by decide) (by decide), hr 152 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, mem_setReg]
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r a b c d e => ?_, trivial⟩
  simp [a, b, c, d, e]

end VG.Proof.CmacTripleDes.Stream.X86_64

end

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_absorb`'s straight-line code

What each piece of code between the copies and the runs of `update`
computes, in terms of `count` (`c`) and `len` (`L`): the bytes held back
`h = held c`, the bytes copied after them `f = min L (8 - h)`, the data left
`L - f`, whether to chain the block held back (`b1`), the blocks chained
after it (`nb`), and the rest (`rest`).
-/

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (8 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first run of `update` chains: the block held
back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second run chains: those of the data left but
its last 1 to 8 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 8 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 8 := by
  have := held_le c; unfold fOf; omega_using [this]

theorem nb_le (c L : Nat) : fOf c L + 8 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_using [this]

/-! ## Arithmetic on registers -/

theorem sub8 {h : Nat} (hh : h ≤ 8) :
    BitVec.setWidth 64 (8 : BitVec 32) - BitVec.ofNat 64 h = BitVec.ofNat 64 (8 - h) :=
  Offset.ofNat_sub_ofNat hh

/-- `8 nb` for the data left `x > 0`, as `sub 1; mov; and 7; sub` computes it. -/
theorem nb8_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 - ((BitVec.ofNat 64 x - 1) &&& 7) = BitVec.ofNat 64 (8 * ((x - 1) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 64 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and7, e, BitVec.toNat_ofNat]
  omega_using []

theorem shr3 {n : Nat} (hn : 8 * n < 2 ^ 64) :
    BitVec.ofNat 64 (8 * n) >>> 3 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hn]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .rsi = BitVec.ofNat 64 c)
    (hz : s.zf = some (s.gpr .rsi == 0)) :
    WP isa Impl.CmacTripleDes.Stream.X86_64.held s fun s' => s'.gpr .rax = BitVec.ofNat 64 (Stream.held c) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by show s.zf = _; rw [hz, hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
    exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by show s.zf = _; rw [hz, hd, beq_eq_false_iff_ne.mpr hne]) (fun h => by cases h)
      fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
        Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, hd, sx1, sx7]
    refine ⟨by rw [held_bv _ hne, toNat_ofNat hc], fun r h => by simp [h], trivial, trivial, trivial⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 (Stream.held c))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hbx : s.gpr .rbx = St) :
    WP isa fill s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 (408 + Stream.held c) ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hh := held_le c
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (.imm 8),
      .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (8 - Stream.held c) ∧ s₁.cf = some (decide (L < 8 - Stream.held c)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, hax, h14, sub8 hh,
      toNat_ofNat hL, toNat_ofNat (show 8 - Stream.held c < 2 ^ 64 by omega_using [])]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hl : L < 8 - Stream.held c
    · refine WP.ite true (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
      refine ⟨by rw [g₁ _ (by decide), h14, fOf, Nat.min_eq_left (by omega_using [hl])],
        fun r h => by simp [h, g₁ r h], m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.block_nil ⟨by rw [rcx₁, fOf, Nat.min_eq_right (by omega_using [hl])], g₁, m₁, rd₁, wr₁⟩
  · obtain ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g₂ _ (by decide : Reg.rbx ≠ .rcx),
      g₂ _ (by decide : Reg.rax ≠ .rcx), hbx, hax, sx408, rcx₂]
    refine ⟨trivial, by rw [BitVec.add_assoc, ← BitVec.ofNat_add], fun r h₁ h₂ => by simp [h₂, g₂ r h₁],
      m₂, rd₂, wr₂⟩

/-! ## `chain1`: the arguments of the first run of `update` -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h13 : s.gpr .r13 = D) (hcx : s.gpr .rcx = BitVec.ofNat 64 f) (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (hbx : s.gpr .rbx = St) (h15 : s.gpr .r15 = S) :
    WP isa chain1 s fun s' => s'.gpr .r13 = D + BitVec.ofNat 64 f ∧ s'.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .rdi = St ∧
      s'.gpr .rsi = St + BitVec.ofNat 64 400 ∧ s'.gpr .rdx = St + BitVec.ofNat 64 408 ∧ s'.gpr .r8 = S ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r13₁, r14₁, rcx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .add .r13 (.reg .rcx),
      .alu .sub .r14 (.reg .rcx), .mov32 .rcx (.imm 0)] s = some s₁ ∧
      s₁.gpr .r13 = D + BitVec.ofNat 64 f ∧ s₁.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L - f = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_setReg, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h14, hcx,
      Offset.ofNat_sub_ofNat hf, beq_zero_iff, toNat_ofNat (show L - f < 2 ^ 64 by omega_using [hL])]
    exact ⟨trivial, trivial, rfl, trivial, fun r a b c => by simp [a, b, c], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [rcx₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, h0, ↓reduceIte]
      exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · obtain ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r13) (b : r ≠ .r14) (c : r ≠ .rcx) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g _ (by decide : Reg.rbx ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.r15 ≠ .r13) (by decide) (by decide), hbx, h15, sx400, sx408,
      g₂ _ (by decide : Reg.r13 ≠ .rcx), g₂ _ (by decide : Reg.r14 ≠ .rcx), r13₁, r14₁, rcx₂]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, fun r hr a b => ?_,
      by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `chain2`: the arguments of the second run of `update` -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 (8 * (if x = 0 then 0 else (x - 1) / 8)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 8) ∧ s'.gpr .rdi = s.gpr .rbx ∧
      s'.gpr .rsi = s.gpr .rbx + BitVec.ofNat 64 400 ∧ s'.gpr .rdx = s.gpr .r13 ∧ s'.gpr .r8 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r12 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r12 = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (x = 0)) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h14, BitVec.and_self,
      beq_zero_iff, toNat_ofNat hx]
    exact ⟨rfl, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r12 = BitVec.ofNat 64 (8 * (if x = 0 then 0 else (x - 1) / 8)) ∧
    (∀ r, r ≠ .r12 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_
    fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r12₁]; simp [h0], fun r h _ => g₁ r h, m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
          Option.bind_some]
        rfl, ?_⟩
      simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, reduceCtorEq, h0, ↓reduceIte, g₁ _ (by decide : Reg.r14 ≠ .r12), h14,
        sx1, sx7]
      exact ⟨nb8_bv (by omega_using [h0]) hx, fun r a b => by simp [a, b, g₁ r a], m₁, rd₁, wr₁⟩
  · obtain ⟨r12₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self,
        BitVec.reduceSignExtend, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, execShift, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
      rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, ite_true, reduceCtorEq, ite_false,
      g₂ _ (by decide : Reg.rbx ≠ .r12) (by decide),
      g₂ _ (by decide : Reg.r13 ≠ .r12) (by decide), g₂ _ (by decide : Reg.r15 ≠ .r12) (by decide), r12₂]
    refine ⟨trivial, shr3 (by split <;> omega_arith), trivial, trivial, trivial, trivial,
      fun r hr a => ?_, m₂, rd₂, wr₂⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 8 * n ≤ x)
    (h13 : s.gpr .r13 = D + BitVec.ofNat 64 a) (h12 : s.gpr .r12 = BitVec.ofNat 64 (8 * n))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .r13 = D + BitVec.ofNat 64 (a + 8 * n) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (x - 8 * n) ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 408 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (x - 8 * n) ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [rest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
    wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h12, h14, sx408, Offset.ofNat_sub_ofNat hn]
  refine ⟨by rw [BitVec.add_assoc, ← BitVec.ofNat_add], trivial, trivial, trivial, fun r hr a b => ?_,
    trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end VG.Proof.CmacTripleDes.Stream.X86_64

end

end


@[expose] public section

section

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_absorb` up to the first `update`

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 8 - h)` bytes after them, and sets up the first run of `update`,
which chains the block held back if data is left (`AMid₁`).
-/

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`
and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : Addr) (L : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rdx : s₀.gpr .rdx = D
  rcx : (s₀.gpr .rcx).toNat = L
  r8 : s₀.gpr .r8 = S
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 160⟩]
  st_d : (⟨St, 416⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 160⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 160⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 416⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 160⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 160 ≤ 2 ^ 64

theorem APre.of {s₀ : State} (h : absorbX86_64.pre s₀) :
    APre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j⟩

section
variable {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.rcx]; exact BitVec.isLt _

theorem APre.rcx' : s₀.gpr .rcx = BitVec.ofNat 64 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.rcx, toNat_ofNat hp.lt])

theorem APre.inSt {d n : Nat} (h : d + n ≤ 416) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 160) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 160⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_using [h])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a run of `update` on `n` blocks at `Dd`, from a state
with the permissions and stack pointer of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hrdi : s.gpr .rdi = St)
    (hrsi : s.gpr .rsi = St + BitVec.ofNat 64 400) (hrdx : s.gpr .rdx = Dd)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 n) (hr8 : s.gpr .r8 = S) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 8 * n < 2 ^ 64)
    (hdc : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 400, 8⟩)
    (hds : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨S, 120⟩) (hwrap : Dd.toNat + 8 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 416⟩, ⟨S, 160⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 8 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 400) Dd S n := by
  have hw := hp.wSt
  obtain c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  obtain s120 : Region.Sub ⟨S, 120⟩ ⟨S, 160⟩ := Region.sub_prefix (by decide)
  exact
  { rdi := hrdi, rsi := hrsi, rdx := hrdx, rcx := hrcx, r8 := hr8, hn := hn
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right s120
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c400).sub_right s120
    retC := by rw [hsp]; exact hp.ret_st.sub_right c400
    retS := by rw [hsp]; exact hp.ret_s.sub_right s120
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 160⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 160⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (408 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first run of `update` leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 400) (St + BitVec.ofNat 64 408) S (b1Of (s₀.gpr .rsi).toNat L)
  rbx : s.gpr .rbx = St
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rsi).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rsi).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = s₀.gpr .rbp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .rsi).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L) := by
  generalize hc : (s₀.gpr .rsi).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hsi : s₀.gpr .rsi = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hc, toNat_ofNat hcl])
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  obtain ⟨s₁, run₁, rbx₁, r13₁, r14₁, r15₁, rsi₁, rsp₁, rbp₁, zf₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.r8 fun d _ h => hp.inS (by omega_using [h])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [rsi₁, hsi]) (by rw [zf₁, rsi₁]))
    fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) hL ax₂ (by rw [g₂ _ (by decide), r14₁, hp.rcx'])
    (by rw [g₂ _ (by decide), rbx₁, hp.rdi])) fun s₃ ⟨cx₃, dx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c, g₂ r a]
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (L := fOf c L) (by omega_using [hfh])
    (by rw [g _ (by decide) (by decide) (by decide), r13₁, hp.rdx]) dx₃ cx₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by
      rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  have g' (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) (d : r ≠ .r10) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a d, g r a b c]
  refine WP.mono (chain1_wp hfL hL (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r13₁, hp.rdx])
    (by rw [h₄.other _ (by decide) (by decide), cx₃])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r14₁, hp.rcx'])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), rbx₁, hp.rdi])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r15₁])) fun s₅ h₅ => ?_
  obtain ⟨r13₅, r14₅, rcx₅, rdi₅, rsi₅, rdx₅, r8₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r13) (b : r ≠ .r14) : s₅.gpr r = s₁.gpr r := by
    rw [sv₅ r hr a b, g' r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  obtain hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rsp₁]
  obtain hb1 : 8 * b1Of c L ≤ 8 := by unfold b1Of; split <;> omega_using []
  obtain c408 : Region.Sub ⟨St + BitVec.ofNat 64 408, 8 * b1Of c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs rdi₅ rsi₅ rdx₅ (by rw [rcx₅, b1Of, leftOf]) r8₅ hsp hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c408).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega_using [hb1]⟩,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbx₁, hp.rdi],
    r13₅, by rw [r14₅]; rfl, by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), r15₁], hsp,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacTripleDes.Stream.X86_64

end

/-!
# Streaming TDEA-CMAC on x86-64: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- A region disjoint from every region of a frame is unchanged. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := Proof.Cmac.bytesAt_frame hf hd hn

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- What the first part of `absorb` (up to and with the first run of `update`)
leaves, for the second. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rsi).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rsi).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorb₁_after {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorb₁ s₀ (AAfter₁ s₀ St D S L) :=
  WP.seq (WP.mono (absorbPre_wp hp) fun _ h =>
    WP.mono (upd_wp h.args) fun _ h₆ =>
      ⟨by rw [h₆.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₆.saved _ (by simp [calleeSaved]), h.r13],
        by rw [h₆.saved _ (by simp [calleeSaved]), h.r14], by rw [h₆.saved _ (by simp [calleeSaved]), h.r15],
        by rw [h₆.saved _ (by simp [calleeSaved]), h.rsp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩)

theorem absorb_wp {s₀ : State} (h0 : absorbX86_64.pre s₀) :
    WP isa absorb s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rdx = D at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .rcx).toNat = L at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rsi).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_))
  obtain ⟨args₅, rbx₅, r13₅, r14₅, r15₅, rsp₅, rbp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ r13₅ r14₅ m₅
  refine WP.mono (upd_wp args₅) fun s₆ h₆ => ?_
  have k₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ _ (by simp [calleeSaved]), r14₅])) fun s₇ h₇ => ?_)
  obtain ⟨r12₇, rcx₇, rdi₇, rsi₇, rdx₇, r8₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8) = nbOf c L := rfl
  rw [hnb] at r12₇ rcx₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s₅.gpr r := by rw [sv₇ r hr a, k₆ r hr]
  obtain hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₅]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 8 * nbOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [rdi₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rsi₇, k₆ _ (by simp [calleeSaved]), rbx₅])
    (by rw [rdx₇, k₆ _ (by simp [calleeSaved]), r13₅]) rcx₇
    (by rw [r8₇, k₆ _ (by simp [calleeSaved]), r15₅]) hsp₇ (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c400).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.seq (WP.mono (upd_wp args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ calleeSaved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, r13₉, r14₉, rdx₉, rcx₉, sv₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D) (a := fOf c L)
    (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r13₅])
    (by rw [k₈ _ (by simp [calleeSaved]), r12₇])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r14₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain hrr : restOf c L ≤ 8 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 408, restOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L))
    (C := St + BitVec.ofNat 64 408) (L := restOf c L) (by omega_using [hL, hsum]) r13₉
    (by rw [rdx₉, k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), rbx₅]) rcx₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  obtain r15₁₀ : s₁₀.gpr .r15 = S := by
    rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
      k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r15₅]
  obtain ⟨s₁₁, run₁₁, rbx₁₁, r12₁₁, r13₁₁, r14₁₁, r15₁₁, g₁₁, m₁₁⟩ := restore_ok s₁₀ r15₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega_using [h])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨S + BitVec.ofNat 64 120, 40⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 120⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 120⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 408, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 120, 40⟩, ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 120⟩, ⟨St + BitVec.ofNat 64 408, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key, the data and the return address are in none of these.
  obtain dK : ∀ r ∈ K, (⟨St, 400⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain dRet : ∀ r ∈ K, (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, F11.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  · -- The registers, restored from their slots.
    obtain Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 120 ≤ d) (h₂ : d + 8 ≤ 160) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 160⟩ := Offset.sub_base S (by omega_using [h₂])
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_using [h₁]) (by omega_using [h₂])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
    obtain ⟨a₁, a₃, a₄, a₅, a₆⟩ := absSaved_read s₀ S
    obtain hsp₁₀ : s₁₀.gpr .rsp = s₀.gpr .rsp := by
      rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
        k₈ _ (by simp [calleeSaved]), hsp₇]
    obtain hbp : s₁₀.gpr .rbp = s₀.gpr .rbp := by
      rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
        k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), rbp₅]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₁₁, slot 120 (by decide) (by decide), a₁]
    · rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbp]
    · rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hsp₁₀]
    · rw [r12₁₁, slot 128 (by decide) (by decide), a₃]
    · rw [r13₁₁, slot 136 (by decide) (by decide), a₄]
    · rw [r14₁₁, slot 144 (by decide) (by decide), a₅]
    · rw [r15₁₁, slot 152 (by decide) (by decide), a₆]
  · intro key msg hr hcnt hlen
    rw [hp.rdi] at hr ⊢
    rw [hp.rdx, hp.rcx]
    rw [hp.rcx] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Proof.CmacTripleDes.X86_64.ciphAt m St = Spec.Cmac.tdes key := fun m hf => by
      simp only [Proof.CmacTripleDes.X86_64.ciphAt, Spec.Cmac.tdes]
      rw [Proof.CmacTripleDes.scheduleAt_congr fun i hi => frame_at hf dK (by omega_using [hw]) (by omega_using [hi]),
        hsch]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, frame_bytes hf dDat (by omega_using [hlen])]
    obtain fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 400) 8 := by
      rw [frame_bytes fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    obtain cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 400) 8 :=
      frame_bytes fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 400, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 408) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 408) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 408) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hh]))).sub_right
            (Offset.sub_base S (by decide)))
          (by omega_using [hh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.CmacTripleDes.Stream.repr_fill hr hk
        (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ ⟨St, 416⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 120⟩],
            (⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, frame_bytes f8 dj (by omega_using [hfh, hfL']),
          frame_bytes f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 8 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 8 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.CmacTripleDes.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.CmacTripleDes.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append,
          Proof.CmacTripleDes.Stream.blocksAt_eq, dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 408)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.X86_64

end

end


/-!
# Streaming TDEA-CMAC on x86-64: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Implies.lean`), which imply them, with
no stack: the functions call nothing.

`absorb` is constant time in two parts: the taint analysis covers each
(`CT.lean`), the second from the registers the first leaves, which its
correctness proof pins to the public arguments (`AAfter₁`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.Stream.X86_64

/-! ## `absorb` is constant time -/

theorem absorb₂_agree {s₀ s₀' a b : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
    (hp' : APre s₀' St D S L) (q : s₀.gpr .rsi = s₀'.gpr .rsi) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp)
    (h₁ : AAfter₁ s₀ St D S L a) (h₂ : AAfter₁ s₀' St D S L b) : X86_64.Taint.Agree τAbsorb₂ a b := by
  obtain wf : ∀ (σ t : State), APre σ St D S L → AAfter₁ σ St D S L t → X86_64.Taint.Wf τAbsorb₂ t := by
    intro σ t hσ ht
    obtain hw : t.wr = [⟨St, 416⟩, ⟨S, 160⟩] := by rw [ht.wr, hσ.wr]
    refine ⟨fun _ => ⟨by simp [hw, τAbsorb₂], by simp [hw, hσ.st_s], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τAbsorb₂, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw, ht.rbx, ht.r15]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => by rw [h₁.wr, h₂.wr, hp.wr, hp'.wr],
    wf _ _ hp h₁, wf _ _ hp' h₂, ?_, ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τAbsorb₂, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.r13, h₂.r13, q]
    · rw [h₁.r14, h₂.r14, q]
    · rw [h₁.r15, h₂.r15]
    · rw [h₁.rsp, h₂.rsp, q1]
  · intro sl h; simp [τAbsorb₂] at h
  · intro sl h; simp [τAbsorb₂] at h

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ag := absorb_agree h0 h0' hq
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  obtain hp := APre.of h0
  obtain hp' : APre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat := by
    rw [q1, q3, q4, q5]; exact APre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rdx = D at hp hp'
  generalize s₀.gpr .r8 = S at hp hp'
  generalize (s₀.gpr .rcx).toNat = L at hp hp'
  obtain ⟨_, hA⟩ := absorb₁_taint
  obtain ⟨_, hB⟩ := absorb₂_taint
  obtain a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') τAbsorb
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag) hA).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorb₁_after hp, absorb₁_after hp'⟩
  obtain b := RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b)
    τAbsorb₂ (fun a b h => absorb₂_agree hp hp' q2 q6 h.1 h.2) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq b

theorem absorb_ct : ConstantTime isa absorbX86_64.pre absorbX86_64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_mx : streamInit.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem absorb_mx : absorb.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finish_mx : finish.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

theorem absorb_correct (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec absorb_mx he hg, hp⟩

theorem finish_correct (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finish_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec finish_mx he hg, hp⟩

theorem init_verified : Verified X86_64.target streamInit (streamInitScratchContract15 X86_64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified X86_64.target absorb (absorbScratchContract20 X86_64.abi 0) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified X86_64.target finish (finishScratchContract15 X86_64.abi 0) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.X86_64

end

end


/-!
# Streaming TDEA-CMAC on x86-64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 8 bytes standing for the return address, then
the working space (120 bytes, and 160 for `absorb`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.Stream.X86_64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract X86_64.abi 128).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract X86_64.abi 168).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract X86_64.abi 128).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 128 .rcx streamInit)
    (Spec.Cmac.tdesStreamInitContract X86_64.abi 128) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacTripleDes.Stream.streamInitPostOut_local _) (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 15)
    (pre := Spec.Cmac.tdesStreamInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 128) init_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) initFrameSat_pre

theorem absorb_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 168 .r8 absorb)
    (Spec.Cmac.tdesAbsorbContract X86_64.abi 168) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacTripleDes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 20)
    (post := Spec.Cmac.tdesAbsorbPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 168) absorb_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) absorbFrameSat_pre

theorem finish_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 128 .rcx finish)
    (Spec.Cmac.tdesFinishContract X86_64.abi 128) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacTripleDes.Stream.finishPostOut_local _) (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 15)
    (post := Spec.Cmac.tdesFinishPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 128) finish_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.X86_64
